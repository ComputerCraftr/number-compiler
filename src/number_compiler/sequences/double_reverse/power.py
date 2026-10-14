"""Exact bounded 2*reverse(n) queries over the shared scheduler and SLPs.

The scheduler retains exact source authority and a ledgered SLP. Certified
four-phase cylinders use guarded dyadic temporal Hashlife; other sources keep
the exact chronological path. Neither path materializes intermediate values.
"""

from __future__ import annotations

from collections.abc import Generator, Iterator
from contextlib import ExitStack
from typing import Self, cast

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp import BimachineSLPProjector
from number_compiler.arithmetic.automata.slp_walks import iter_symbols, symbol_at
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.execution.source_bound_images import (
    SourceImageID,
)
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.lifecycle import cleanup_all, cleanup_on_error
from number_compiler.resources.output_stream_metrics import (
    closing_output_stream,
    initialize_output_stream_metrics,
    measured_output_stream,
)
from number_compiler.sequences.double_reverse.source_adapter import (
    _DoubleReverseAction,
    _DoubleReverseMachine,
    _DoubleReverseSource,
    _DoubleReverseSourceAdapter,
)
from number_compiler.sequences.double_reverse.temporal_hashlife import (
    DoubleReversePortAction,
    DoubleReverseTemporalHashlife,
    temporal_action_node_cost,
)
from number_compiler.sequences.double_reverse.temporal_ports import (
    DecimalCarryPort,
    DoubleReverseClosedForm,
    closed_form_from_roots,
    decimal_carry_port,
)
from number_compiler.sequences.double_reverse.temporal_square import (
    DoubleReverseTwoStepMachine,
    attach_projector_memos,
)


class DoubleReverseTerm:
    """A resource-bounded exact term of ``2 * reverse(n)`` iteration."""

    __slots__ = (
        "__weakref__",
        "_active_symbol_walks",
        "_adapter",
        "_arena",
        "_authority",
        "_cleanup_complete",
        "_closed",
        "_dispose_resources_complete",
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
        self._active_symbol_walks = 0
        self._dispose_resources_complete = False
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
                self._adapter.temporal_hashlife,
                self._adapter.temporal_memos,
            )
            initialize_output_stream_metrics(
                self._ledger, "double_reverse_output_stream"
            )
            self._ledger.bump("recursive_output_stream_node_visits", 0)
            for counter in (
                "double_reverse_spatial_transducer_applications",
                "double_reverse_temporal_square_applications",
                "double_reverse_represented_growth_cells",
                "double_reverse_hashlife_cones",
                "double_reverse_hashlife_cone_hits",
                "double_reverse_hashlife_tile_selections",
                "double_reverse_hashlife_powered_t2_steps",
                "double_reverse_hashlife_power_chunks",
                "double_reverse_boundary_classifications",
                "double_reverse_boundary_node_visits",
                "double_reverse_temporal_hashlife_publications",
                "double_reverse_temporal_port_action_publications",
                "double_reverse_temporal_port_action_cache_hits",
                "double_reverse_weighted_carry_port_publications",
                "double_reverse_temporal_moment_port_publications",
                "double_reverse_temporal_affine_port_publications",
                "double_reverse_hashlife_bit_budget_refusals",
            ):
                self._ledger.bump(counter, 0)
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
        square_projector = BimachineSLPProjector(
            DoubleReverseTwoStepMachine(), self._arena
        )
        owner_names = (
            "forward",
            "reverse",
            "block",
            "forward-power",
            "reverse-power",
            "square-forward",
            "square-reverse",
            "square-block",
            "square-forward-power",
            "square-reverse-power",
            "grammar-reversal",
        )
        owners = tuple(
            ledger.register(prefix + "-" + name, "double_reverse_projector_memo")
            for name in owner_names
        )
        temporal_owners = tuple(
            ledger.register(prefix + "-" + name, "double_reverse_temporal_memo")
            for name in (
                "temporal-cones",
                "temporal-slices",
                "temporal-port-actions",
            )
        )
        memo_rows: list[OwnedMemo[object, object]] = []
        for owner in owners[:10]:
            memo: OwnedMemo[object, object] = OwnedMemo(
                ledger, owner, nodes_per_entry=1
            )
            memo_rows.append(memo)
            rollback.enter_context(cleanup_on_error(memo.dispose))
        memos = cast(tuple[OwnedMemo[object, object], ...], tuple(memo_rows))
        attach_projector_memos(projector, memos[:5])
        attach_projector_memos(square_projector, memos[5:10])
        reverse_memo: OwnedMemo[int, int] = OwnedMemo(
            ledger, owners[10], nodes_per_entry=1
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
        temporal_rows: list[OwnedMemo[object, object]] = []
        for index, owner in enumerate(temporal_owners):
            if index < 2:
                temporal_memo: OwnedMemo[object, object] = OwnedMemo(
                    ledger, owner, nodes_per_entry=1
                )
            else:
                temporal_memo = OwnedMemo(
                    ledger,
                    owner,
                    node_cost=temporal_action_node_cost,
                )
            temporal_rows.append(temporal_memo)
            rollback.enter_context(cleanup_on_error(temporal_memo.dispose))
        temporal_memos = cast(
            tuple[OwnedMemo[object, object], ...], tuple(temporal_rows)
        )
        temporal_hashlife = DoubleReverseTemporalHashlife(
            self._arena,
            ledger,
            self._issuer,
            scratch_owner,
            cast(OwnedMemo[tuple[int, int], int], temporal_memos[0]),
            cast(OwnedMemo[tuple[int, int, int], int], temporal_memos[1]),
            cast(
                OwnedMemo[tuple[int, int, int], DoubleReversePortAction],
                temporal_memos[2],
            ),
            self.max_steps,
        )
        rollback.enter_context(
            cleanup_on_error(temporal_hashlife.dispose_audit_contract)
        )
        adapter = _DoubleReverseSourceAdapter(
            ledger,
            self._arena,
            projector,
            square_projector,
            self._source,
            self._issuer,
            self.max_steps,
            self.max_state_bits,
            memos,
            reverse_memo,
            threshold_memo,
            scratch_owner,
            temporal_hashlife,
            temporal_memos,
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
            or self._authority[15] is not self._adapter.temporal_hashlife
            or self._authority[16] is not self._adapter.temporal_memos
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
        return symbol_at(self._arena, root, position)

    def _iter_symbols(self, root: int, *, reverse: bool) -> Generator[int, None, None]:
        def record_visit(is_node: bool) -> None:
            if is_node:
                self._ledger.bump("recursive_output_stream_node_visits")

        def walk() -> Generator[int, None, None]:
            self._active_symbol_walks += 1
            try:
                yield from iter_symbols(
                    self._arena,
                    root,
                    reverse=reverse,
                    on_task=record_visit,
                    reserve_task=lambda: self._ledger.reserve(
                        self._scratch_owner, entries=1, nodes=1
                    ),
                    release_tasks=lambda count: self._ledger.release(
                        self._scratch_owner, entries=count, nodes=count
                    ),
                    check_open=self._check_open,
                )
            finally:
                self._active_symbol_walks -= 1
                if self._closed and self._active_symbol_walks == 0:
                    self._mark_scratch_disposed()
                    if self._dispose_resources_complete:
                        self._cleanup_complete = True

        return walk()

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

    def carry_port(
        self,
        *,
        initial: bool = False,
        modulus: int | None = None,
        max_bits: int = 4096,
    ) -> DecimalCarryPort:
        """Lazily project the initial or admitted endpoint carry word."""
        self._check_open()
        if type(initial) is not bool:
            raise TypeError("initial selector must be Boolean")
        root = self._source.root if initial else self._root()
        result = decimal_carry_port(
            self._arena,
            root,
            modulus=modulus,
            max_bits=max_bits,
            ledger=self._ledger,
            scratch_owner=self._scratch_owner,
        )
        self._ledger.bump("double_reverse_weighted_carry_port_publications")
        return result

    def temporal_closed_form(
        self, *, modulus: int | None = None, max_bits: int = 4096
    ) -> DoubleReverseClosedForm:
        """Lazily project source/endpoint moments and cylinder growth."""
        self._check_open()
        endpoint = self._root()
        result = closed_form_from_roots(
            self._arena,
            self._source.root,
            endpoint,
            self.generation,
            modulus=modulus,
            max_bits=max_bits,
            ledger=self._ledger,
            scratch_owner=self._scratch_owner,
        )
        self._ledger.bump("double_reverse_temporal_moment_port_publications")
        if result.affine_gain is not None and result.affine_shift is not None:
            self._ledger.bump("double_reverse_temporal_affine_port_publications")
        return result

    def dispose(self) -> None:
        if self._cleanup_complete:
            return
        self._closed = True
        if not self._dispose_resources_complete:
            cleanup_all(
                (
                    self._scheduler.dispose_source_images,
                    self._adapter.dispose,
                    self._arena.dispose,
                )
            )
            self._dispose_resources_complete = True
        if self._active_symbol_walks == 0:
            self._mark_scratch_disposed()
            self._cleanup_complete = True

    def _mark_scratch_disposed(self) -> None:
        self._ledger.mark_disposed(self._scratch_owner)

    def _check_open(self) -> None:
        if self._closed:
            raise ValueError("disposed double-reverse term")

    def __enter__(self) -> Self:
        self._check_open()
        return self

    def __exit__(self, *_exc: object) -> None:
        self.dispose()
