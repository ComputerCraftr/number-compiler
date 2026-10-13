"""Exact bounded 2*reverse(n) queries over the shared scheduler and SLPs.

The temporal recurrence is deliberately explicit: the scheduler composes and
applies one authenticated primitive at a time.  Each primitive acts on a
ledger-owned straight-line word, so it never constructs the intermediate
integer or decimal string.  This module makes no logarithmic-time claim about
the number of temporal steps.
"""

from __future__ import annotations

from collections.abc import Generator, Iterator, MutableMapping
from contextlib import ExitStack, closing
from dataclasses import dataclass
from typing import Self, cast

from number_compiler.arithmetic.automata.guard import record_slp_metrics
from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp import BimachineSLPProjector, SLPNode
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.execution.source_bound_images import (
    SourceImageBinding,
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageID,
    SourceImageProjection,
    SourceImageView,
)
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.lifecycle import cleanup_all, cleanup_on_error
from number_compiler.resources.output_stream_metrics import (
    closing_output_stream,
    initialize_output_stream_metrics,
    measured_output_stream,
)


@dataclass(frozen=True, slots=True, eq=False)
class _DoubleReverseSource:
    issuer: ArenaToken
    seed: int
    root: int


@dataclass(frozen=True, slots=True)
class _DoubleReverseAction:
    steps: int

    def __post_init__(self) -> None:
        if type(self.steps) is not int or self.steps < 0:
            raise ValueError("double-reverse action requires nonnegative exact steps")


@dataclass(frozen=True, slots=True)
class _DoubleReverseImage:
    issuer: ArenaToken
    source: _DoubleReverseSource
    action: _DoubleReverseAction
    root: int


def _iter_slp_symbols(
    arena: LedgerSLPArena,
    ledger: ResourceLedger,
    scratch_owner: int,
    root: int,
    *,
    reverse: bool,
    metric: str | None,
) -> Generator[int, None, None]:
    tasks: list[tuple[str, int, int]] = []
    retained = 0

    def push(task: tuple[str, int, int]) -> None:
        nonlocal retained
        ledger.reserve(scratch_owner, entries=1, nodes=1)
        try:
            tasks.append(task)
        except BaseException:
            ledger.release(scratch_owner, entries=1, nodes=1)
            raise
        retained += 1

    try:
        push(("node", root, 1))
        while tasks:
            kind, node_id, count = tasks.pop()
            ledger.release(scratch_owner, entries=1, nodes=1)
            retained -= 1
            if kind == "node" and metric is not None:
                ledger.bump(metric)
            if kind == "repeat":
                if count:
                    push(("repeat", node_id, count - 1))
                    push(("node", node_id, 1))
                continue
            node: SLPNode = arena.nodes[node_id]
            if node.kind == "EMPTY":
                continue
            if node.kind == "TERM":
                yield node.symbol
            elif node.kind == "CONCAT":
                if reverse:
                    push(("node", node.left, 1))
                    push(("node", node.right, 1))
                else:
                    push(("node", node.right, 1))
                    push(("node", node.left, 1))
            elif node.kind == "REPEAT":
                push(("repeat", node.child, node.count))
            else:
                raise AssertionError(node.kind)
    finally:
        if retained:
            ledger.release(scratch_owner, entries=retained, nodes=retained)


class _CarryDFA:
    start = 0

    @staticmethod
    def step(state: int, symbol: int) -> int | None:
        if state not in (0, 1) or not 0 <= symbol <= 9:
            return None
        return (2 * symbol + state) // 10


class _SuffixNonzeroDFA:
    start = 0

    @staticmethod
    def step(state: int, symbol: int) -> int | None:
        if state not in (0, 1) or not 0 <= symbol <= 9:
            return None
        return int(bool(state or symbol))


class _DoubleReverseMachine:
    """Two-sided word law: forward carry and a trailing-zero suffix flag."""

    __slots__ = ("left", "right")

    def __init__(self) -> None:
        self.left = _CarryDFA()
        self.right = _SuffixNonzeroDFA()

    @staticmethod
    def emit(
        carry: int, symbol: int, suffix_has_nonzero: int
    ) -> tuple[int, ...] | None:
        if (
            carry not in (0, 1)
            or not 0 <= symbol <= 9
            or suffix_has_nonzero not in (0, 1)
        ):
            return None
        if symbol == 0 and suffix_has_nonzero == 0:
            # The corresponding high zero of the reversed numeral is omitted.
            # If a carry reaches it, this zero emits that final leading digit.
            return (1,) if carry else ()
        return ((2 * symbol + carry) % 10,)


class _DoubleReverseSourceAdapter:
    family = "double-reverse"
    semantic_version = "decimal-2rev-source-image-v1"

    def __init__(
        self,
        ledger: ResourceLedger,
        arena: LedgerSLPArena,
        projector: BimachineSLPProjector,
        source: _DoubleReverseSource,
        issuer: ArenaToken,
        max_steps: int,
        max_state_bits: int,
        projector_memos: tuple[OwnedMemo[object, object], ...],
        reverse_owner: OwnedMemo[int, int],
        threshold_owner: OwnedMemo[int, bytes],
        scratch_owner: int,
    ) -> None:
        self.ledger = ledger
        self.arena = arena
        self.projector = projector
        self.source = source
        self.issuer = issuer
        self.max_steps = max_steps
        self.max_state_bits = max_state_bits
        self.projector_memos = projector_memos
        self._reverse_owner = reverse_owner
        self._threshold_owner = threshold_owner
        self.scratch_owner = scratch_owner
        self._closed = False
        self._cleanup_complete = False

    def validate_source(self, source: object) -> None:
        if type(source) is not _DoubleReverseSource:
            raise ValueError("double-reverse source is foreign or malformed")
        exact = source
        if (
            exact is not self.source
            or exact.issuer is not self.issuer
            or exact.root < 0
            or exact.root >= len(self.arena.nodes)
            or type(exact.seed) is not int
            or exact.seed < 0
        ):
            raise ValueError("double-reverse source is foreign or malformed")

    def validate_action(self, action: object) -> None:
        if type(action) is not _DoubleReverseAction:
            raise TypeError("double-reverse action has the wrong type")
        exact = action
        if exact.steps > self.max_steps:
            raise ValueError("double-reverse action exceeds its admitted horizon")

    def validate_payload(self, payload: object) -> None:
        if type(payload) is not _DoubleReverseImage:
            raise TypeError("double-reverse image has the wrong type")
        exact = payload
        if exact.issuer is not self.issuer or exact.source is not self.source:
            raise ValueError("double-reverse image belongs to another source owner")
        self.validate_action(exact.action)
        if (
            type(exact.root) is not int
            or not 0 <= exact.root < len(self.arena.nodes)
            or exact.action.steps > self.max_steps
        ):
            raise ValueError("double-reverse image root or horizon is invalid")

    def identity_action(self, source: object) -> _DoubleReverseAction:
        self.validate_source(source)
        return _DoubleReverseAction(0)

    def action_children(
        self, action: object
    ) -> tuple[_DoubleReverseAction, _DoubleReverseAction] | None:
        self.validate_action(action)
        steps = cast(_DoubleReverseAction, action).steps
        if steps < 2:
            return None
        before = steps // 2
        return _DoubleReverseAction(before), _DoubleReverseAction(steps - before)

    def compose_actions(self, before: object, after: object) -> _DoubleReverseAction:
        self.validate_action(before)
        self.validate_action(after)
        total = (
            cast(_DoubleReverseAction, before).steps
            + cast(_DoubleReverseAction, after).steps
        )
        self.validate_action(_DoubleReverseAction(total))
        return _DoubleReverseAction(total)

    def admit_source(self, source: object) -> SourceImageCandidate:
        self.validate_source(source)
        exact = cast(_DoubleReverseSource, source)
        payload = _DoubleReverseImage(
            self.issuer, exact, _DoubleReverseAction(0), exact.root
        )
        width = self.arena.nodes[exact.root].length
        return SourceImageCandidate(payload, 0, radix=10, precision=width)

    def _apply_word(self, root: int) -> int:
        # The projector's explicit worklists can retain a constant multiple of
        # the current grammar size. Reserve that transient storage before work.
        bound = max(16, 4 * len(self.arena.nodes))
        with self.ledger.reservation(self.scratch_owner, entries=bound, nodes=bound):
            carry = self.projector.forward(root, self.projector.machine.left.start)
            if carry is None:
                raise ValueError("decimal doubling carry rejected an input symbol")
            lsd_root = self.projector.apply(root)
            if carry:
                lsd_root = self.arena.concat(lsd_root, self.arena.terminal(carry))
            # The transducer emits little-endian digits; public occurrences use
            # a canonical most-significant-first grammar.
            result = self._reverse_grammar(lsd_root)
        if result == self.arena.empty_id:
            result = self.arena.terminal(0)
        width = self.arena.nodes[result].length
        if not self._fits_state_bits(result, width):
            raise BlockContextBudgetExceeded(
                "double-reverse state exceeds the admitted state-bit budget"
            )
        self.ledger.bump("double_reverse_spatial_transducer_applications")
        return result

    def _fits_state_bits(self, root: int, width: int) -> bool:
        if 4 * width <= self.max_state_bits:
            return True
        if 3 * (width - 1) >= self.max_state_bits:
            return False
        threshold = self._threshold_digits()
        if width != len(threshold):
            return width < len(threshold)
        with closing(
            _iter_slp_symbols(
                self.arena,
                self.ledger,
                self.scratch_owner,
                root,
                reverse=False,
                metric="double_reverse_state_comparison_node_visits",
            )
        ) as symbols:
            for index, symbol in enumerate(symbols):
                threshold_symbol = threshold[index] - ord("0")
                self.ledger.bump("double_reverse_state_comparison_digits")
                if symbol != threshold_symbol:
                    return symbol < threshold_symbol
        return False

    def _threshold_digits(self) -> bytes:
        if self.max_state_bits in self._threshold_owner:
            return self._threshold_owner[self.max_state_bits]

        # Reserve the binary operand, base-10 chunks, and packed decimal bytes
        # before constructing the cached threshold representation.
        threshold_bits = self.max_state_bits
        estimated_digits = 5 * ((threshold_bits + 15) // 16)
        chunks = (estimated_digits + 8) // 9
        scratch_nodes = (
            2 * ((threshold_bits + 29) // 30)
            + chunks
            + 2 * ((estimated_digits + 7) // 8)
        )
        with self.ledger.reservation(
            self.scratch_owner, entries=1, nodes=max(1, scratch_nodes)
        ):
            remaining = 1 << threshold_bits
            pieces: list[int] = []
            while remaining:
                remaining, piece = divmod(remaining, 1_000_000_000)
                pieces.append(piece)
                self.ledger.bump("double_reverse_threshold_divisions")
            encoded = bytearray(str(pieces[-1]).encode("ascii"))
            for piece in reversed(pieces[:-1]):
                encoded.extend(f"{piece:09d}".encode("ascii"))
            digits = bytes(encoded)
            self.ledger.bump("double_reverse_threshold_conversion_bytes", len(digits))
            self._threshold_owner[self.max_state_bits] = digits
        return digits

    def apply_primitive(
        self, action: object, source: SourceImageView
    ) -> SourceImageCandidate:
        self.validate_action(action)
        prior = self._view_payload(source)
        exact_action = cast(_DoubleReverseAction, action)
        if exact_action.steps == 0:
            return SourceImageCandidate(
                prior,
                0,
                radix=10,
                precision=self.arena.nodes[prior.root].length,
            )
        if exact_action.steps != 1:
            raise ValueError("double-reverse primitive must have one step")
        result = self._apply_word(prior.root)
        combined = self.compose_actions(prior.action, exact_action)
        payload = _DoubleReverseImage(self.issuer, self.source, combined, result)
        return SourceImageCandidate(
            payload,
            combined.steps,
            radix=10,
            precision=self.arena.nodes[result].length,
        )

    def apply_composite(
        self,
        action: object,
        source: SourceImageView,
        demand: SourceImageDemand | None,
    ) -> None:
        self.validate_action(action)
        self._view_payload(source)
        del demand

    def compose_chronological(
        self,
        action: object,
        source: SourceImageView,
        before: SourceImageView,
        after: SourceImageView,
    ) -> SourceImageCandidate:
        self.validate_action(action)
        original = self._view_payload(source)
        middle = self._view_payload(before)
        final = self._view_payload(after)
        children = self.action_children(action)
        if (
            children is None
            or middle.action != self.compose_actions(original.action, children[0])
            or final.action != self.compose_actions(middle.action, children[1])
        ):
            raise ValueError(
                "double-reverse child images do not compose chronologically"
            )
        return SourceImageCandidate(
            final,
            final.action.steps,
            radix=10,
            precision=self.arena.nodes[final.root].length,
        )

    def admitted_input_key(self, action: object, source: SourceImageView) -> None:
        self.validate_action(action)
        self._view_payload(source)

    def transport_reuse(
        self,
        action: object,
        cached_source: SourceImageView,
        cached_result: SourceImageView,
        source: SourceImageView,
    ) -> SourceImageCandidate:
        del action, cached_source, cached_result, source
        raise ValueError("double-reverse images have no relative source transport")

    def project(
        self, image: SourceImageView, demand: SourceImageDemand
    ) -> SourceImageProjection:
        payload = self._view_payload(image)
        if demand.name != "width" or demand.parameters:
            raise ValueError("double-reverse supports only the width projection")
        return SourceImageProjection(self.arena.nodes[payload.root].length)

    def first_failure(self, image: SourceImageView) -> None:
        self._view_payload(image)

    def audit_image_binding(
        self,
        binding: SourceImageBinding,
        payload: object,
        failure_prefix: object,
    ) -> tuple[object, ...]:
        if failure_prefix is not None:
            raise ValueError("double-reverse images cannot carry failure prefixes")
        self.validate_source(binding.source)
        self.validate_payload(payload)
        exact = cast(_DoubleReverseImage, payload)
        if (
            exact.source is not binding.source
            or exact.action != binding.action
            or binding.family != self.family
            or binding.semantic_version != self.semantic_version
            or binding.extent != exact.action.steps
            or binding.radix != 10
            or binding.orientation != 1
            or binding.boundary_ports
            or binding.precision != self.arena.nodes[exact.root].length
        ):
            raise ValueError("double-reverse image binding is inconsistent")
        return (payload,)

    def _view_payload(self, view: SourceImageView) -> _DoubleReverseImage:
        if type(view) is not SourceImageView:
            raise TypeError("double-reverse operation needs a scheduler image view")
        self.validate_source(view.binding.source)
        self.validate_payload(view.payload)
        payload = cast(_DoubleReverseImage, view.payload)
        if (
            view.binding.family != self.family
            or view.binding.semantic_version != self.semantic_version
            or view.binding.source is not self.source
            or view.binding.action != payload.action
            or view.binding.extent != payload.action.steps
            or view.binding.radix != 10
            or view.binding.orientation != 1
            or view.binding.boundary_ports
            or view.binding.precision != self.arena.nodes[payload.root].length
        ):
            raise ValueError("double-reverse scheduler binding is stale or foreign")
        return payload

    @staticmethod
    def _width_bits(width: int) -> int:
        # 3.322 bits per decimal digit is a strict upper bound for log2(10).
        return max(1, (3322 * width + 999) // 1000)

    def _reverse_grammar(self, root: int) -> int:
        memo = self._reverse_memo
        if root in memo:
            return memo[root]
        tasks: list[tuple[str, int]] = [("visit", root)]
        values: list[int] = []
        while tasks:
            operation, node_id = tasks.pop()
            node = self.arena.nodes[node_id]
            if operation == "visit":
                cached = memo.get(node_id)
                if cached is not None:
                    values.append(cached)
                elif node.kind in ("EMPTY", "TERM"):
                    memo[node_id] = node_id
                    values.append(node_id)
                elif node.kind == "CONCAT":
                    tasks.append(("join", node_id))
                    tasks.append(("visit", node.left))
                    tasks.append(("visit", node.right))
                elif node.kind == "REPEAT":
                    tasks.append(("repeat", node_id))
                    tasks.append(("visit", node.child))
                else:
                    raise AssertionError(node.kind)
            elif operation == "join":
                left_reversed = values.pop()
                right_reversed = values.pop()
                result = self.arena.concat(right_reversed, left_reversed)
                memo[node_id] = result
                values.append(result)
            elif operation == "repeat":
                child = values.pop()
                result = self.arena.repeat(child, node.count)
                memo[node_id] = result
                values.append(result)
            else:
                raise AssertionError(operation)
        if len(values) != 1:
            raise AssertionError("double-reverse SLP reversal stack is unbalanced")
        record_slp_metrics(sections=len(memo))
        return values[0]

    @property
    def _reverse_memo(self) -> OwnedMemo[int, int]:
        return self._reverse_owner

    def dispose(self) -> None:
        if self._cleanup_complete:
            return
        self._closed = True
        cleanup_all(
            (
                *tuple(memo.dispose for memo in self.projector_memos),
                self._reverse_owner.dispose,
                self._threshold_owner.dispose,
            )
        )
        self._cleanup_complete = True


class DoubleReverseTerm:
    """A resource-bounded exact term of ``2 * reverse(n)`` iteration."""

    __slots__ = (
        "__weakref__",
        "_adapter",
        "_arena",
        "_authority",
        "_cleanup_complete",
        "_closed",
        "_image",
        "_issuer",
        "_ledger",
        "_projector",
        "_reverse_memo",
        "_scheduler",
        "_scratch_owner",
        "_source",
        "_threshold_memo",
        "generation",
        "max_state_bits",
        "max_steps",
        "seed",
        "source_digits",
    )

    def __init__(
        self,
        seed: int,
        generation: int,
        *,
        max_steps: int = 4096,
        max_state_bits: int = 4096,
        max_context_nodes: int | None = None,
        max_cache_entries: int | None = None,
    ) -> None:
        self.seed = require_integer(seed, "seed", 0)
        self.generation = require_integer(generation, "generation", 0)
        self.max_steps = require_integer(max_steps, "maximum steps", 0)
        self.max_state_bits = require_integer(max_state_bits, "maximum state bits", 1)
        if self.generation > self.max_steps:
            raise BlockContextBudgetExceeded(
                "double-reverse generation exceeds its step budget"
            )
        if self.seed.bit_length() > self.max_state_bits:
            raise BlockContextBudgetExceeded(
                "double-reverse source exceeds the admitted state-bit budget"
            )
        self._ledger = ResourceLedger(max_context_nodes, max_cache_entries)
        self._issuer = ArenaToken("double-reverse-term")
        self._closed = False
        self._cleanup_complete = False
        with ExitStack() as rollback:
            self._arena = LedgerSLPArena(
                self._ledger,
                "double-reverse",
                owner_kind="double_reverse",
            )
            rollback.enter_context(cleanup_on_error(self._arena.dispose))
            source_lsd = tuple(self._digits_lsd(self.seed))
            self.source_digits = source_lsd
            source_msd = tuple(reversed(source_lsd))
            source_root = self._arena.word(source_msd)
            self._source = _DoubleReverseSource(self._issuer, self.seed, source_root)
            (
                self._adapter,
                self._projector,
                self._scheduler,
                self._reverse_memo,
                self._scratch_owner,
                self._threshold_memo,
            ) = self._create_execution(rollback)
            self._image: SourceImageID | None = None
            self._authority = (
                self.seed,
                self.generation,
                self.max_steps,
                self.max_state_bits,
                self._ledger,
                self._ledger.max_nodes,
                self._ledger.max_cache_entries,
                self._arena,
                self._source,
                self._adapter,
                self._projector,
                self._reverse_memo,
                self._scheduler,
                self._scratch_owner,
                self._threshold_memo,
            )
            initialize_output_stream_metrics(
                self._ledger, "double_reverse_output_stream"
            )
            self._ledger.bump("recursive_output_stream_node_visits", 0)
            self._ledger.register_execution_root(self)

    @staticmethod
    def _digits_lsd(value: int) -> Iterator[int]:
        if value == 0:
            yield 0
            return
        while value:
            value, digit = divmod(value, 10)
            yield digit

    def _create_execution(
        self, rollback: ExitStack
    ) -> tuple[
        _DoubleReverseSourceAdapter,
        BimachineSLPProjector,
        TileScheduler,
        OwnedMemo[int, int],
        int,
        OwnedMemo[int, bytes],
    ]:
        ledger = self._ledger
        prefix = f"double-reverse-{ledger.owner_count}"
        machine = _DoubleReverseMachine()
        projector = BimachineSLPProjector(machine, self._arena)
        owner_names = (
            "forward",
            "reverse",
            "block",
            "forward-power",
            "reverse-power",
            "grammar-reversal",
        )
        owners = tuple(
            ledger.register(prefix + "-" + name, "double_reverse_projector_memo")
            for name in owner_names
        )
        memo_rows: list[OwnedMemo[object, object]] = []
        for owner in owners[:5]:
            memo: OwnedMemo[object, object] = OwnedMemo(
                ledger, owner, nodes_per_entry=1
            )
            memo_rows.append(memo)
            rollback.enter_context(cleanup_on_error(memo.dispose))
        memos = cast(tuple[OwnedMemo[object, object], ...], tuple(memo_rows))
        projector._fwd = cast(MutableMapping[tuple[int, int], int | None], memos[0])
        projector._rev = cast(MutableMapping[tuple[int, int], int | None], memos[1])
        projector._block = cast(MutableMapping[tuple[int, int, int], int], memos[2])
        projector._fwd_power = cast(
            MutableMapping[tuple[int, int, int], int | None], memos[3]
        )
        projector._rev_power = cast(
            MutableMapping[tuple[int, int, int], int | None], memos[4]
        )
        reverse_memo: OwnedMemo[int, int] = OwnedMemo(
            ledger, owners[5], nodes_per_entry=1
        )
        rollback.enter_context(cleanup_on_error(reverse_memo.dispose))
        threshold_owner = ledger.register(
            prefix + "-state-threshold", "double_reverse_state_threshold"
        )
        threshold_memo: OwnedMemo[int, bytes] = OwnedMemo(
            ledger,
            threshold_owner,
            node_cost=lambda _key, value: max(1, (len(value) + 7) // 8),
        )
        rollback.enter_context(cleanup_on_error(threshold_memo.dispose))
        scratch_owner = ledger.register(prefix + "-scratch", "double_reverse_workspace")
        adapter = _DoubleReverseSourceAdapter(
            ledger,
            self._arena,
            projector,
            self._source,
            self._issuer,
            self.max_steps,
            self.max_state_bits,
            memos,
            reverse_memo,
            threshold_memo,
            scratch_owner,
        )
        rollback.enter_context(cleanup_on_error(adapter.dispose))
        scheduler = TileScheduler.source_only(ledger)
        scheduler.register_source_image_adapter(adapter)
        rollback.enter_context(cleanup_on_error(scheduler.dispose_source_images))
        return (
            adapter,
            projector,
            scheduler,
            reverse_memo,
            scratch_owner,
            threshold_memo,
        )

    def prepare_endpoint(self) -> None:
        """Construct the exact endpoint before entering source-read-only scope."""
        self._check_open()
        if (
            self._authority[:4]
            != (self.seed, self.generation, self.max_steps, self.max_state_bits)
            or self._authority[4] is not self._ledger
            or self._authority[5] != self._ledger.max_nodes
            or self._authority[6] != self._ledger.max_cache_entries
            or self._authority[7] is not self._arena
            or self._authority[8] is not self._source
            or self._authority[9] is not self._adapter
            or self._authority[10] is not self._projector
            or self._authority[11] is not self._reverse_memo
            or self._authority[12] is not self._scheduler
            or self._authority[13] != self._scratch_owner
            or self._authority[14] is not self._threshold_memo
        ):
            raise ValueError("double-reverse term binding changed")
        if self._image is None:
            self._image = self._scheduler.source_image(
                self._adapter, self._source, _DoubleReverseAction(self.generation)
            )
        image = self._image
        assert image is not None
        view = self._scheduler._source_image_core().view(image)
        self._adapter._view_payload(view)

    def _root(self) -> int:
        self.prepare_endpoint()
        image = self._image
        assert image is not None
        view = self._scheduler._source_image_core().view(image)
        return self._adapter._view_payload(view).root

    @property
    def maximum_width(self) -> int:
        self._check_open()
        return max(1, len(self.source_digits) + self.generation)

    @property
    def estimated_bit_length(self) -> int:
        return _DoubleReverseSourceAdapter._width_bits(self.maximum_width)

    @property
    def source_lsd_digits(self) -> tuple[int, ...]:
        return self.source_digits

    def width(self) -> int:
        root = self._root()
        return self._arena.nodes[root].length

    def digit(self, position: int) -> int:
        position = require_integer(position, "digit coordinate")
        root = self._root()
        width = self._arena.nodes[root].length
        if not 0 <= position < width:
            raise IndexError(position)
        return self._symbol_at(root, width - position - 1)

    def _symbol_at(self, root: int, position: int) -> int:
        node_id = root
        offset = position
        while True:
            node = self._arena.nodes[node_id]
            if node.kind == "TERM":
                return node.symbol
            if node.kind == "CONCAT":
                left_length = self._arena.nodes[node.left].length
                if offset < left_length:
                    node_id = node.left
                else:
                    offset -= left_length
                    node_id = node.right
            elif node.kind == "REPEAT":
                child_length = self._arena.nodes[node.child].length
                if child_length == 0:
                    raise AssertionError("empty repetition cannot contain a digit")
                offset %= child_length
                node_id = node.child
            else:
                raise AssertionError(node.kind)

    def _iter_symbols(self, root: int, *, reverse: bool) -> Iterator[int]:
        yield from _iter_slp_symbols(
            self._arena,
            self._ledger,
            self._scratch_owner,
            root,
            reverse=reverse,
            metric="recursive_output_stream_node_visits",
        )

    def iter_digits(self) -> Generator[int, None, None]:
        def source() -> Iterator[int]:
            self._check_open()
            root = self._root()
            yield from self._iter_symbols(root, reverse=True)

        return measured_output_stream(
            self._ledger, "double_reverse_output_stream", source
        )

    def digits(self) -> tuple[int, ...]:
        return tuple(self.iter_digits())

    def materialize(self, *, max_bits: int) -> int:
        self._check_open()
        max_bits = require_integer(max_bits, "output bit cap", 0)
        root = self._root()
        value = 0
        with closing_output_stream(self._iter_symbols(root, reverse=False)) as digits:
            for digit in digits:
                value = value * 10 + digit
                if value.bit_length() > max_bits:
                    raise BlockContextBudgetExceeded(
                        "double-reverse output exceeds the requested materialization budget"
                    )
        return value

    def metrics(self) -> dict[str, int]:
        """Return a read-only snapshot; this does not prepare an endpoint."""
        return dict(self._ledger.counters)

    def dispose(self) -> None:
        if self._cleanup_complete:
            return
        self._closed = True
        cleanup_all(
            (
                self._scheduler.dispose_source_images,
                self._adapter.dispose,
                self._arena.dispose,
            )
        )
        self._cleanup_complete = True

    def _check_open(self) -> None:
        if self._closed:
            raise ValueError("disposed double-reverse term")

    def __enter__(self) -> Self:
        self._check_open()
        return self

    def __exit__(self, *_exc: object) -> None:
        self.dispose()
