"""Scheduler-owned source-image adapter for decimal ``2 * reverse``."""

from __future__ import annotations

from contextlib import closing
from dataclasses import dataclass
from typing import Final, cast

from number_compiler.arithmetic.automata.guard import record_slp_metrics
from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp import BimachineSLPProjector
from number_compiler.arithmetic.automata.slp_walks import iter_symbols, symbol_at
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.execution.source_bound_images import (
    SourceImageBinding,
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageProjection,
    SourceImageView,
)
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.lifecycle import cleanup_all
from number_compiler.resources.metric_keys import (
    double_reverse as _double_reverse_keys,
)
from number_compiler.sequences.double_reverse.temporal_hashlife import (
    DoubleReversePortAction,
    DoubleReverseTemporalHashlife,
    growth_ports,
)
from number_compiler.sequences.double_reverse.temporal_hashlife_types import (
    DoubleReverseSourcePrefix,
)

DOUBLE_REVERSE_SOURCE_IMAGE_VERSION: Final[str] = "decimal-2rev-source-image-v1"


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
    semantic_version = DOUBLE_REVERSE_SOURCE_IMAGE_VERSION

    def __init__(
        self,
        ledger: ResourceLedger,
        arena: LedgerSLPArena,
        projector: BimachineSLPProjector,
        two_step_projector: BimachineSLPProjector,
        source: _DoubleReverseSource,
        issuer: ArenaToken,
        max_steps: int,
        max_state_bits: int,
        projector_memos: tuple[OwnedMemo[object, object], ...],
        reverse_owner: OwnedMemo[int, int],
        threshold_owner: OwnedMemo[int, bytes],
        scratch_owner: int,
        temporal_hashlife: DoubleReverseTemporalHashlife,
        temporal_memos: tuple[OwnedMemo[object, object], ...],
    ) -> None:
        self.ledger = ledger
        self.arena = arena
        self.projector = projector
        self.two_step_projector = two_step_projector
        self.source = source
        self.issuer = issuer
        self.max_steps = max_steps
        self.max_state_bits = max_state_bits
        self.projector_memos = projector_memos
        self._reverse_owner = reverse_owner
        self._threshold_owner = threshold_owner
        self.scratch_owner = scratch_owner
        self.temporal_hashlife = temporal_hashlife
        self.temporal_memos = temporal_memos
        self._closed = False
        self._cleanup_complete = False
        self.temporal_hashlife._bind_source_advancer(self._apply_word)

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
        # For a bounded real primitive, reverse the decimal digits first and
        # perform multiplication by two as a binary integer shift. Long SLPs
        # retain the decimal carry transducer so CONCAT/REPEAT stays compact.
        width = self.arena.nodes[root].length
        if 0 < width <= 32:
            reverse_value = 0
            weight = 1
            with self.ledger.reservation(
                self.scratch_owner, entries=width, nodes=width
            ):
                for index in range(width):
                    digit = self._symbol_at(root, index)
                    if not 0 <= digit <= 9:
                        raise ValueError("2rev10 source contains a nondecimal symbol")
                    reverse_value += digit * weight
                    weight *= 10
                shifted = reverse_value << 1
                if shifted.bit_length() > self.max_state_bits:
                    raise BlockContextBudgetExceeded(
                        "double-reverse state exceeds the admitted state-bit budget"
                    )
                result = self.arena.word(tuple(int(ch) for ch in str(shifted)))
            if not self._fits_state_bits(result, self.arena.nodes[result].length):
                raise BlockContextBudgetExceeded(
                    "double-reverse state exceeds the admitted state-bit budget"
                )
            self.ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_BINARY_SHIFT_PRIMITIVES
            )
            return result
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
        self.ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_SPATIAL_TRANSDUCER_APPLICATIONS
        )
        return result

    def _advance_temporal_prefix(self) -> DoubleReverseSourcePrefix:
        """Advance the owner cursor through this adapter's exact one-T map."""
        return self.temporal_hashlife._advance_source_prefix()

    def _record_square_guard_visit(self) -> None:
        self.ledger.bump(_double_reverse_keys.DOUBLE_REVERSE_SQUARE_GUARD_REGION_VISITS)

    def _symbol_at(self, root: int, position: int) -> int:
        return symbol_at(
            self.arena,
            root,
            position,
            on_visit=self._record_square_guard_visit,
        )

    def _trailing_zero_count(self, root: int) -> int:
        """Count a compressed decimal suffix without visiting its cells."""
        nodes = self.arena.nodes
        bound = max(16, 4 * len(nodes))
        with self.ledger.reservation(self.scratch_owner, entries=bound, nodes=bound):
            tasks = [(root, 0)]
            zeros: dict[int, int] = {}
            try:
                while tasks:
                    current, stage = tasks.pop()
                    self.ledger.bump(
                        _double_reverse_keys.DOUBLE_REVERSE_SUFFIX_ZERO_FOLD_NODE_VISITS
                    )
                    self.ledger.bump(
                        _double_reverse_keys.DOUBLE_REVERSE_SUFFIX_ZERO_FOLD_OPERAND_BITS,
                        nodes[current].length.bit_length(),
                    )
                    if current in zeros:
                        continue
                    node = nodes[current]
                    if node.kind == "EMPTY":
                        zeros[current] = 0
                        self.ledger.bump(
                            _double_reverse_keys.DOUBLE_REVERSE_SUFFIX_ZERO_FOLD_OPERATIONS
                        )
                    elif node.kind == "TERM":
                        zeros[current] = int(node.symbol == 0)
                        self.ledger.bump(
                            _double_reverse_keys.DOUBLE_REVERSE_SUFFIX_ZERO_FOLD_OPERATIONS
                        )
                    elif node.kind == "CONCAT" and stage == 0:
                        tasks.append((current, 1))
                        tasks.append((node.right, 0))
                    elif node.kind == "CONCAT" and stage == 1:
                        right_zeros = zeros[node.right]
                        if right_zeros == nodes[node.right].length:
                            tasks.append((current, 2))
                            tasks.append((node.left, 0))
                        else:
                            zeros[current] = right_zeros
                            self.ledger.bump(
                                _double_reverse_keys.DOUBLE_REVERSE_SUFFIX_ZERO_FOLD_OPERATIONS
                            )
                    elif node.kind == "CONCAT" and stage == 2:
                        zeros[current] = zeros[node.right] + zeros[node.left]
                        self.ledger.bump(
                            _double_reverse_keys.DOUBLE_REVERSE_SUFFIX_ZERO_FOLD_OPERATIONS
                        )
                    elif node.kind == "REPEAT" and stage == 0:
                        tasks.append((current, 1))
                        tasks.append((node.child, 0))
                    elif node.kind == "REPEAT" and stage == 1:
                        child_zeros = zeros[node.child]
                        zeros[current] = (
                            node.length
                            if child_zeros == nodes[node.child].length
                            else child_zeros
                        )
                        self.ledger.bump(
                            _double_reverse_keys.DOUBLE_REVERSE_SUFFIX_ZERO_FOLD_OPERATIONS
                        )
                    else:
                        raise AssertionError("invalid double-reverse suffix SLP")
                return zeros[root]
            finally:
                tasks.clear()
                zeros.clear()

    def _general_two_step(self, root: int) -> int | None:
        """Apply exact normalized T², including arbitrary source contraction."""
        width = self.arena.nodes[root].length
        if width < 1:
            return None
        self.ledger.bump(_double_reverse_keys.DOUBLE_REVERSE_SQUARE_WIDTH_GUARDS)
        if self._symbol_at(root, width - 1) != 0:
            trailing_zeros = 0
        elif width > 1 and self._symbol_at(root, width - 2) != 0:
            trailing_zeros = 1
        else:
            trailing_zeros = self._trailing_zero_count(root)
        if trailing_zeros == width:
            self.ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_SQUARE_APPLICATIONS
            )
            self.ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_SQUARE_ZERO_FIXED_POINTS
            )
            return self.arena.terminal(0)

        new_width = width - trailing_zeros
        trimmed = (
            self.temporal_hashlife.part(root, 0, new_width) if trailing_zeros else root
        )
        leading = self._symbol_at(trimmed, 0)
        trailing = self._symbol_at(trimmed, new_width - 1)
        right_birth = int(trailing >= 5)
        left_birth = int((2 * leading) % 10 >= 5)
        adjacent = self._symbol_at(trimmed, 1) if new_width > 1 else 0
        first_cell = (
            4 * leading + int((2 * adjacent + int(leading >= 5)) % 10 >= 5)
        ) % 10
        leading_trim = int(not left_birth and first_cell == 0)
        intermediate_width = new_width + right_birth
        final_width = new_width + left_birth + right_birth - leading_trim
        if final_width < 1:
            raise AssertionError("positive double-reverse square has zero width")
        if (
            self._width_bits(intermediate_width) > self.max_state_bits
            or self._width_bits(final_width) > self.max_state_bits
        ):
            self.ledger.bump(_double_reverse_keys.DOUBLE_REVERSE_SQUARE_GUARD_REFUSALS)
            self.ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_SQUARE_BIT_BUDGET_GUARD_REFUSALS
            )
            return None

        bound = max(16, 4 * len(self.arena.nodes))
        before = self.two_step_projector.section_calls
        with self.ledger.reservation(self.scratch_owner, entries=bound, nodes=bound):
            interior = self.two_step_projector.apply(trimmed)
            result = self.arena.concat_many(
                (
                    self.arena.terminal(1) if left_birth else self.arena.empty_id,
                    interior,
                    self.arena.terminal(2) if right_birth else self.arena.empty_id,
                )
            )
            if leading_trim:
                if self._symbol_at(result, 0) != 0:
                    raise AssertionError("2rev10 normalized leading digit was not zero")
                result = self.temporal_hashlife.part(
                    result, 1, self.arena.nodes[result].length
                )
        if self.arena.nodes[result].length != final_width:
            raise AssertionError("2rev10 normalized square changed its certified width")
        if self._symbol_at(result, 0) == 0:
            raise AssertionError("2rev10 square produced a noncanonical leading zero")
        if final_width > width:
            self.ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_SQUARE_GROWTH_SEAMS
            )
        if final_width < width:
            self.ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_SQUARE_SHRINK_SEAMS
            )
        if trailing_zeros or leading_trim:
            self.ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_SQUARE_NORMALIZATIONS
            )
        self.ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_SQUARE_APPLICATIONS
        )
        if final_width > width:
            self.ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_REPRESENTED_GROWTH_CELLS,
                final_width - width,
            )
        self.ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_SQUARE_REGION_VISITS,
            self.two_step_projector.section_calls - before,
        )
        return result

    def _fits_state_bits(self, root: int, width: int) -> bool:
        if 4 * width <= self.max_state_bits:
            return True
        if 3 * (width - 1) >= self.max_state_bits:
            return False
        threshold = self._threshold_digits()
        if width != len(threshold):
            return width < len(threshold)

        def record_visit(is_node: bool) -> None:
            if is_node:
                self.ledger.bump(
                    _double_reverse_keys.DOUBLE_REVERSE_STATE_COMPARISON_NODE_VISITS
                )

        with closing(
            iter_symbols(
                self.arena,
                root,
                reverse=False,
                on_task=record_visit,
                reserve_task=lambda: self.ledger.reserve(
                    self.scratch_owner, entries=1, nodes=1
                ),
                release_tasks=lambda count: self.ledger.release(
                    self.scratch_owner, entries=count, nodes=count
                ),
            )
        ) as symbols:
            for index, symbol in enumerate(symbols):
                threshold_symbol = threshold[index] - ord("0")
                self.ledger.bump(
                    _double_reverse_keys.DOUBLE_REVERSE_STATE_COMPARISON_DIGITS
                )
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
                self.ledger.bump(
                    _double_reverse_keys.DOUBLE_REVERSE_THRESHOLD_DIVISIONS
                )
            encoded = bytearray(str(pieces[-1]).encode("ascii"))
            for piece in reversed(pieces[:-1]):
                encoded.extend(f"{piece:09d}".encode("ascii"))
            digits = bytes(encoded)
            self.ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_THRESHOLD_CONVERSION_BYTES,
                len(digits),
            )
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
    ) -> SourceImageCandidate | None:
        self.validate_action(action)
        prior = self._view_payload(source)
        del demand
        exact_action = cast(_DoubleReverseAction, action)
        result: int | None = None
        powered_action: DoubleReversePortAction | None = None
        if exact_action.steps >= 2 and exact_action.steps % 2 == 0:
            phase = self.temporal_hashlife.certify(prior.root)
            if phase is not None:
                f_steps = exact_action.steps // 2
                left_births, right_births = growth_ports(phase, f_steps)
                final_width = (
                    self.arena.nodes[prior.root].length + left_births + right_births
                )
                if self._width_bits(final_width) > self.max_state_bits:
                    self.ledger.bump(
                        _double_reverse_keys.DOUBLE_REVERSE_HASHLIFE_BIT_BUDGET_REFUSALS
                    )
                    raise BlockContextBudgetExceeded(
                        "2rev10 powered endpoint exceeds the admitted state-bit budget"
                    )
                powered_action = self.temporal_hashlife.advance_action(
                    prior.root, f_steps, phase
                )
                result = self.temporal_hashlife.root_of(powered_action.target)
                self.ledger.bump(
                    _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_HASHLIFE_PUBLICATIONS
                )
                self.ledger.bump(
                    _double_reverse_keys.DOUBLE_REVERSE_REPRESENTED_GROWTH_CELLS,
                    left_births + right_births,
                )
            elif exact_action.steps == 2:
                result = self._general_two_step(prior.root)
        if result is None:
            return None
        combined = self.compose_actions(prior.action, exact_action)
        # The published engine action is retained in its own ledger memo. The
        # scheduler payload needs only the exact output root; duplicating the
        # action here created a second, weakly bound provenance record.
        payload = _DoubleReverseImage(self.issuer, self.source, combined, result)
        self.ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_COMPLETED_T2_PUBLICATIONS,
            int(exact_action.steps == 2),
        )
        return SourceImageCandidate(
            payload,
            combined.steps,
            radix=10,
            precision=self.arena.nodes[result].length,
        )

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
        # The hook authenticates the complete source/action/image relation.
        # Its enclosing payload is approved by the source-bound auditor after
        # this succeeds, so returning internal fields here would grant them a
        # separate semantic approval they do not need.
        return ()

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
                self.temporal_hashlife.dispose_audit_contract,
                *tuple(memo.dispose for memo in self.projector_memos),
                self._reverse_owner.dispose,
                self._threshold_owner.dispose,
                *tuple(memo.dispose for memo in self.temporal_memos),
            )
        )
        self._cleanup_complete = True
