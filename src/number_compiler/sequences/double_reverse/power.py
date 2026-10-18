"""Exact bounded 2*reverse(n) queries over the shared scheduler and SLPs.

The scheduler retains exact source authority and a ledgered SLP. Certified
four-phase cylinders use guarded dyadic temporal Hashlife; other sources keep
the exact chronological path. Neither path materializes intermediate values.
"""

from __future__ import annotations

from collections.abc import Generator, Iterator
from contextlib import ExitStack
from dataclasses import replace
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
from number_compiler.resources.metric_keys import (
    double_reverse as _double_reverse_keys,
)
from number_compiler.resources.metric_keys import shared as _shared_keys
from number_compiler.resources.output_stream_metrics import (
    closing_output_stream,
    initialize_output_stream_metrics,
    measured_output_stream,
)
from number_compiler.resources.payload_contracts import PayloadAuditStoreBinding
from number_compiler.sequences.double_reverse.protected_temporal_bank import (
    MAX_PROTECTED_PERIOD,
    ProtectedPeriodicBank,
    protected_periodic_bank,
)
from number_compiler.sequences.double_reverse.radix25_temporal_bank import (
    JointRadix25TemporalBank,
    Radix25ShiftPort,
    joint_radix25_temporal_bank,
    radix25_shift_port,
)
from number_compiler.sequences.double_reverse.source_adapter import (
    _DoubleReverseAction,
    _DoubleReverseMachine,
    _DoubleReverseSource,
    _DoubleReverseSourceAdapter,
)
from number_compiler.sequences.double_reverse.source_bound_bank import (
    DoubleReverseBankMixin,
)
from number_compiler.sequences.double_reverse.temporal_border_bank import (
    OBSERVERS,
    TemporalBorderEnvelope,
    _power_temporal_border_with_prefix,
)
from number_compiler.sequences.double_reverse.temporal_carry_safety import (
    ComponentSafetyProof,
    SourceCarrySafety,
    forced_carry_prefix,
    lift_from_slp,
)
from number_compiler.sequences.double_reverse.temporal_carry_safety_audit import (
    CarrySafetyCacheKey,
    IssuedCarrySafety,
    audit_double_reverse_carry_safety,
    carry_safety_result_node_cost,
    temporal_carry_safety_for_term,
)
from number_compiler.sequences.double_reverse.temporal_hashlife import (
    DoubleReverseTemporalHashlife,
    PointedDigitStencil,
    growth_ports,
)
from number_compiler.sequences.double_reverse.temporal_hashlife_types import (
    DoubleReverseSourcePrefix,
    IssuedDoubleReversePortAction,
    IssuedDoubleReverseSourcePrefix,
    UncertifiedPointedStencilError,
    source_prefix_node_cost,
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


class DoubleReverseTerm(DoubleReverseBankMixin):
    """A resource-bounded exact term of ``2 * reverse(n)`` iteration."""

    __slots__ = (
        "__weakref__",
        "_active_symbol_walks",
        "_adapter",
        "_arena",
        "_audit_carry_safety",
        "_authority",
        "_carry_safety_cache",
        "_carry_safety_owner",
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
            self._carry_safety_owner = self._ledger.register(
                f"double-reverse-{self._ledger.owner_count}-carry-safety",
                "double_reverse_temporal_memo",
            )
            self._carry_safety_cache: OwnedMemo[
                CarrySafetyCacheKey, IssuedCarrySafety
            ] = OwnedMemo(
                self._ledger,
                self._carry_safety_owner,
                node_cost=carry_safety_result_node_cost,
            )
            rollback.enter_context(cleanup_on_error(self._carry_safety_cache.dispose))
            self._audit_carry_safety = self._carry_safety_cache._data
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
                (self._source.issuer, self._source.seed, self._source.root),
                self._carry_safety_owner,
                self._carry_safety_cache,
            )
            initialize_output_stream_metrics(
                self._ledger, "double_reverse_output_stream"
            )
            self._ledger.bump(_shared_keys.RECURSIVE_OUTPUT_STREAM_NODE_VISITS, 0)
            for counter in (
                _double_reverse_keys.DOUBLE_REVERSE_SPATIAL_TRANSDUCER_APPLICATIONS,
                _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_SQUARE_APPLICATIONS,
                _double_reverse_keys.DOUBLE_REVERSE_REPRESENTED_GROWTH_CELLS,
                _double_reverse_keys.DOUBLE_REVERSE_HASHLIFE_CONES,
                _double_reverse_keys.DOUBLE_REVERSE_HASHLIFE_CONE_HITS,
                _double_reverse_keys.DOUBLE_REVERSE_HASHLIFE_TILE_SELECTIONS,
                _double_reverse_keys.DOUBLE_REVERSE_HASHLIFE_POWERED_T2_STEPS,
                _double_reverse_keys.DOUBLE_REVERSE_HASHLIFE_POWER_CHUNKS,
                _double_reverse_keys.DOUBLE_REVERSE_BOUNDARY_CLASSIFICATIONS,
                _double_reverse_keys.DOUBLE_REVERSE_BOUNDARY_NODE_VISITS,
                _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_HASHLIFE_PUBLICATIONS,
                _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_PORT_ACTION_PUBLICATIONS,
                _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_PORT_ACTION_CACHE_HITS,
                _double_reverse_keys.DOUBLE_REVERSE_WEIGHTED_CARRY_PORT_PUBLICATIONS,
                _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_MOMENT_PORT_PUBLICATIONS,
                _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_AFFINE_PORT_PUBLICATIONS,
                _double_reverse_keys.DOUBLE_REVERSE_HASHLIFE_BIT_BUDGET_REFUSALS,
                _double_reverse_keys.DOUBLE_REVERSE_POINTED_STENCIL_TILES,
                _double_reverse_keys.DOUBLE_REVERSE_POINTED_STENCIL_PUBLICATIONS,
                _double_reverse_keys.DOUBLE_REVERSE_POINTED_BORDER_ENTRY_ATTEMPTS,
                _double_reverse_keys.DOUBLE_REVERSE_POINTED_BORDER_ENTRY_STEPS,
                _double_reverse_keys.DOUBLE_REVERSE_POINTED_BORDER_ENTRY_CACHE_HITS,
                _double_reverse_keys.DOUBLE_REVERSE_POINTED_BORDER_PREFIX_CURSOR_PUBLICATIONS,
                _double_reverse_keys.DOUBLE_REVERSE_POINTED_PREFIX_CACHE_DISCARDS,
                _double_reverse_keys.DOUBLE_REVERSE_ENDPOINT_PROJECTOR_DISCARDS,
                _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_BANK_PUBLICATIONS,
                _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_BANK_ENVELOPE_PUBLICATIONS,
                _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_BANK_MATRIX_COMPOSITIONS,
                _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_BANK_MATRIX_CELLS,
                _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_BANK_MOORE_CONSTRUCTIONS,
                _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_BANK_MOORE_TRANSITION_EVALUATIONS,
                _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_BANK_MOORE_OUTPUT_EVALUATIONS,
                _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_BANK_MOORE_STATE_VISITS,
                _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_BANK_MOORE_REFINEMENT_SWEEPS,
                _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_BANK_MOORE_REFINEMENT_ROUNDS,
                _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_CERTIFIED_SUFFIX_PUBLICATIONS,
                _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_EXACT_PAIR_PUBLICATIONS,
                _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_PUBLICATIONS,
                _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_TEMPORAL_STATES,
                _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_STENCIL_EVALUATIONS,
                _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_GUARD_NODES,
                _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_INTERVAL_VISITS,
                _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_MOORE_CONSTRUCTIONS,
                _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_MOORE_OUTPUT_EVALUATIONS,
                _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_MOORE_STATE_VISITS,
                _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_MOORE_REFINEMENT_SWEEPS,
                _double_reverse_keys.DOUBLE_REVERSE_PERIODIC_BANK_MOORE_REFINEMENT_ROUNDS,
            ):
                self._ledger.bump(counter, 0)
            self._ledger.register_execution_root(self)
            rollback.enter_context(
                cleanup_on_error(
                    lambda: self._ledger.remove_payload_audit_contract(
                        self, "double_reverse"
                    )
                )
            )
            self._ledger.register_payload_audit_contract(
                self,
                "double_reverse",
                (
                    PayloadAuditStoreBinding(
                        self._carry_safety_owner,
                        "_audit_carry_safety",
                        "double_reverse_temporal_memo",
                    ),
                ),
                audit_double_reverse_carry_safety,
            )

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
                "temporal-source-prefix",
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
            elif index == 2:
                temporal_memo = OwnedMemo(
                    ledger,
                    owner,
                    node_cost=temporal_action_node_cost,
                )
            else:
                temporal_memo = OwnedMemo(
                    ledger,
                    owner,
                    node_cost=source_prefix_node_cost,
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
                OwnedMemo[tuple[int, int, int], IssuedDoubleReversePortAction],
                temporal_memos[2],
            ),
            cast(
                OwnedMemo[int, IssuedDoubleReverseSourcePrefix],
                temporal_memos[3],
            ),
            self._source.root,
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
        self._validate_source_binding()
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
            or self._authority[18] != self._carry_safety_owner
            or self._authority[19] is not self._carry_safety_cache
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
        if any(len(memo) for memo in self._adapter.projector_memos) or len(
            self._reverse_memo
        ):
            discarded = self._release_ephemeral_projection_tables()
            self._ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_ENDPOINT_PROJECTOR_DISCARDS,
                discarded,
            )

    def _validate_source_binding(self) -> None:
        """Check the exact source/root snapshot without constructing an endpoint."""
        self._check_open()
        source = self._source
        if (
            self._authority[:4]
            != (self.seed, self.generation, self.max_steps, self.max_state_bits)
            or self._authority[4] is not self._ledger
            or self._authority[5] != self._ledger.max_nodes
            or self._authority[6] != self._ledger.max_cache_entries
            or self._authority[7] is not self._arena
            or self._authority[8] is not source
            or self._authority[9] is not self._adapter
            or self._authority[15] is not self._adapter.temporal_hashlife
            or self._authority[16] is not self._adapter.temporal_memos
            or self._authority[17] != (source.issuer, source.seed, source.root)
            or self._authority[18] != self._carry_safety_owner
            or self._authority[19] is not self._carry_safety_cache
            or source.issuer is not self._issuer
            or source.seed != self.seed
        ):
            raise ValueError("double-reverse source binding changed")
        self._adapter.validate_source(source)

    def _release_ephemeral_projection_tables(self) -> int:
        """Drop transient transducer dictionaries after retaining exact SLP roots."""
        released = 0
        for memo in self._adapter.projector_memos:
            released += len(memo)
            memo.clear()
        released += len(self._reverse_memo)
        self._reverse_memo.clear()
        return released

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
        self._check_open()
        if self._image is not None:
            root = self._root()
            return self._arena.nodes[root].length
        try:
            entry = self._certified_prefix_entry(
                max_prefix=min(32, self.generation),
                require_even_remainder=True,
            )
        except UncertifiedPointedStencilError:
            root = self._root()
            return self._arena.nodes[root].length
        return self._pointed_shape(entry)[3]

    def _pointed_shape(
        self, entry: DoubleReverseSourcePrefix
    ) -> tuple[int, int, int, int]:
        """Resolve and budget the one exact source prefix plus F growth law."""
        phase = entry.certified_phase
        if phase is None:
            raise AssertionError("admitted prefix cursor lacks a certified phase")
        root = self._adapter.temporal_hashlife.root_of(entry.target)
        steps = (self.generation - entry.physical_steps) // 2
        left, right = growth_ports(phase, steps)
        width = self._arena.nodes[root].length + left + right
        if self._adapter._width_bits(width) > self.max_state_bits:
            self._ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_HASHLIFE_BIT_BUDGET_REFUSALS
            )
            raise BlockContextBudgetExceeded(
                "2rev10 powered endpoint exceeds the admitted state-bit budget"
            )
        return root, phase, steps, width

    def _certified_prefix_entry(
        self, *, max_prefix: int, require_even_remainder: bool
    ) -> DoubleReverseSourcePrefix:
        """Reuse one exact owner-issued chronological source-prefix cursor."""
        self._check_open()
        if type(require_even_remainder) is not bool:
            raise TypeError("prefix parity selector must be Boolean")
        engine = self._adapter.temporal_hashlife
        limit = min(
            require_integer(max_prefix, "prefix limit", 0),
            engine.prefix_limit,
            self.generation,
        )
        cursor = engine.source_prefix()
        explored = 0
        if cursor is None:
            self._ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_POINTED_BORDER_ENTRY_ATTEMPTS
            )
            cursor = self._adapter._advance_temporal_prefix()
        else:
            self._ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_POINTED_BORDER_ENTRY_CACHE_HITS
            )
            if cursor.physical_steps > limit:
                raise UncertifiedPointedStencilError(
                    "cached exact prefix exceeds this request's admission bound"
                )
        try:
            while True:
                prefix = cursor.physical_steps
                phase = cursor.certified_phase
                even_suffix = (self.generation - prefix) % 2 == 0
                positive_suffix = self.generation > prefix
                if phase is not None and (
                    not require_even_remainder or even_suffix and positive_suffix
                ):
                    return cursor
                if prefix >= limit:
                    raise UncertifiedPointedStencilError(
                        "no admitted certified 2rev10 prefix was found"
                    )
                self._ledger.bump(
                    _double_reverse_keys.DOUBLE_REVERSE_POINTED_BORDER_ENTRY_ATTEMPTS
                )
                explored += 1
                cursor = self._adapter._advance_temporal_prefix()
                self._ledger.bump(
                    _double_reverse_keys.DOUBLE_REVERSE_POINTED_BORDER_ENTRY_STEPS
                )
        finally:
            if explored:
                discarded = self._release_ephemeral_projection_tables()
                self._ledger.bump(
                    _double_reverse_keys.DOUBLE_REVERSE_POINTED_PREFIX_CACHE_DISCARDS,
                    discarded,
                )

    def pointed_stencil(self, position: int) -> PointedDigitStencil:
        """Resolve one LSD-first digit from its certified local temporal cone."""
        self._check_open()
        position = require_integer(position, "digit coordinate")
        if self.generation < 2:
            raise UncertifiedPointedStencilError(
                "pointed stencil requires at least two generations"
            )
        entry = self._certified_prefix_entry(
            max_prefix=min(32, self.generation - 2),
            require_even_remainder=True,
        )
        root, phase, f_steps, width = self._pointed_shape(entry)
        if not 0 <= position < width:
            raise IndexError(position)
        point = self._adapter.temporal_hashlife.pointed_stencil(
            root, f_steps, phase, width - position - 1
        )
        return replace(point, prefix_steps=entry.physical_steps)

    def temporal_border_bank(
        self,
    ) -> tuple[int, tuple[TemporalBorderEnvelope, ...]]:
        """Bound temporal border ports after one exact certified prefix scan."""
        self._check_open()
        entry = self._certified_prefix_entry(
            max_prefix=min(32, self.generation),
            require_even_remainder=False,
        )
        if entry.certified_phase is None:
            raise AssertionError("admitted prefix cursor lacks a certified phase")
        engine = self._adapter.temporal_hashlife
        if engine.validate_source_prefix(entry) is not entry:
            raise AssertionError("temporal border lost its owner-issued prefix")
        root = engine.root_of(entry.target)
        edge = engine.edge_signature(root)
        if edge is None:
            raise AssertionError("certified temporal border has no edge cells")
        horizon = self.generation - entry.physical_steps
        lifted = lift_from_slp(self._arena, root)
        if lifted.edge != edge:
            raise AssertionError("three-cell safety ports disagree with the source")
        forced_prefix = forced_carry_prefix(lifted)
        envelopes = tuple(
            _power_temporal_border_with_prefix(
                edge,
                horizon,
                observer,
                forced_prefix=forced_prefix,
                ledger=self._ledger,
                scratch_owner=self._scratch_owner,
            )
            for observer in OBSERVERS
            if observer != "joint"
        )
        self._ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_BANK_PUBLICATIONS
        )
        return entry.physical_steps, envelopes

    def temporal_carry_safety(
        self,
    ) -> tuple[int, SourceCarrySafety, tuple[ComponentSafetyProof, ...]]:
        """Report source-derived carries and bounded component refinements.

        This finite border analysis does not predict transitions after an SCC
        exit or across a shrinking frontier. A short original seed first needs
        an independently certified temporal-prefix entry.
        """
        self._validate_source_binding()
        return temporal_carry_safety_for_term(self)

    def protected_temporal_bank(
        self, pair_position: int, *, period: int = 2
    ) -> ProtectedPeriodicBank:
        """Source-certify and pump five-band temporal ports on an interior ray.

        The source-periodic guard covers the full moving left/right causal
        halos for the requested two-step horizon. A failed or incomplete
        protected grammar is never promoted from the edge relation alone.
        """
        self._check_open()
        pair_position = require_integer(pair_position, "pair position", 0)
        period = require_integer(period, "bank period", 1, MAX_PROTECTED_PERIOD)
        if self.generation < 2:
            raise UncertifiedPointedStencilError(
                "protected temporal bank requires two physical generations"
            )
        entry = self._certified_prefix_entry(
            max_prefix=min(32, self.generation - 2),
            require_even_remainder=True,
        )
        if entry.certified_phase is None:
            raise AssertionError("admitted temporal bank lacks its certified phase")
        root, phase, steps, _width = self._pointed_shape(entry)
        return protected_periodic_bank(
            self._arena,
            root,
            phase,
            pair_position,
            steps,
            period,
            physical_prefix=entry.physical_steps,
            ledger=self._ledger,
            scratch_owner=self._scratch_owner,
        )

    def source_radix25_shift(self, *, places: int = 8) -> Radix25ShiftPort:
        """Project the initial decimal source through the radix-2/5 shift law."""
        self._check_open()
        result = radix25_shift_port(
            self._arena,
            self._source.root,
            places=places,
            max_bits=self.max_state_bits,
            ledger=self._ledger,
            scratch_owner=self._scratch_owner,
        )
        self._ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_WEIGHTED_CARRY_PORT_PUBLICATIONS
        )
        return result

    def joint_radix25_temporal_bank(
        self,
        pair_position: int,
        *,
        period: int = 2,
        places: int = 8,
        walsh_start: int = 0,
    ) -> JointRadix25TemporalBank:
        """Join source CRT and 64 Walsh lanes under one protected source root."""
        self._check_open()
        pair_position = require_integer(pair_position, "pair position", 0)
        period = require_integer(period, "bank period", 1, MAX_PROTECTED_PERIOD)
        walsh_start = require_integer(walsh_start, "Walsh64 start tick", 0)
        if self.generation < 128:
            raise UncertifiedPointedStencilError(
                "joint Walsh64 bank needs 64 two-step temporal frames"
            )
        entry = self._certified_prefix_entry(
            max_prefix=min(32, self.generation - 128),
            require_even_remainder=True,
        )
        if entry.certified_phase is None:
            raise AssertionError("authenticated bank lacks its boundary phase")
        root, phase, steps, _width = self._pointed_shape(entry)
        try:
            return joint_radix25_temporal_bank(
                self._arena,
                root,
                phase,
                pair_position,
                steps,
                physical_prefix=entry.physical_steps,
                period=period,
                places=places,
                max_bits=self.max_state_bits,
                walsh_start=walsh_start,
                ledger=self._ledger,
                scratch_owner=self._scratch_owner,
            )
        except ValueError as exc:
            raise UncertifiedPointedStencilError(str(exc)) from exc

    def digit(self, position: int) -> int:
        position = require_integer(position, "digit coordinate")
        self._check_open()
        if position < 0:
            raise IndexError(position)
        if self._image is not None:
            return self._digit_at_root(self._root(), position)
        if self.generation >= 2:
            try:
                return self.pointed_stencil(position).digit
            except UncertifiedPointedStencilError:
                pass
        root = self._root()
        return self._digit_at_root(root, position)

    def _symbol_at(self, root: int, position: int) -> int:
        return symbol_at(self._arena, root, position)

    def _digit_at_root(self, root: int, position: int) -> int:
        """Read one LSD-first digit from an already resolved output root."""
        width = self._arena.nodes[root].length
        if not 0 <= position < width:
            raise IndexError(position)
        return self._symbol_at(root, width - position - 1)

    def _iter_symbols(self, root: int, *, reverse: bool) -> Generator[int, None, None]:
        def record_visit(is_node: bool) -> None:
            if is_node:
                self._ledger.bump(_shared_keys.RECURSIVE_OUTPUT_STREAM_NODE_VISITS)

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
        self._ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_WEIGHTED_CARRY_PORT_PUBLICATIONS
        )
        return result

    def temporal_closed_form(
        self, *, modulus: int | None = None, max_bits: int = 4096
    ) -> DoubleReverseClosedForm:
        """Publish exact endpoint moments and any certified suffix affine law.

        Unlike NC13, a seed outside the cylinder does not discard the exact
        later entry-phase action. Prefix and suffix are never confused: the
        suffix shift is relative to the authenticated *entry source*, and its
        linear gain does not claim to cover the uncertified prefix.
        """
        self._check_open()
        entry_root: int | None = None
        prefix_steps: int | None = None
        source_phase = self._adapter.temporal_hashlife.certify(self._source.root)
        if self.generation >= 2 and (source_phase is None or self.generation % 2 != 0):
            try:
                entry = self._certified_prefix_entry(
                    max_prefix=min(32, self.generation - 2),
                    require_even_remainder=True,
                )
            except UncertifiedPointedStencilError:
                pass
            else:
                entry_root = self._adapter.temporal_hashlife.root_of(entry.target)
                prefix_steps = entry.physical_steps
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
            entry_root=entry_root,
            prefix_steps=prefix_steps,
        )
        if result.suffix_affine_gain is not None:
            self._ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_CERTIFIED_SUFFIX_PUBLICATIONS
            )
        self._ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_MOMENT_PORT_PUBLICATIONS
        )
        if result.affine_gain is not None or result.suffix_affine_gain is not None:
            self._ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_AFFINE_PORT_PUBLICATIONS
            )
        return result

    def dispose(self) -> None:
        if self._cleanup_complete:
            return
        self._closed = True
        if not self._dispose_resources_complete:
            cleanup_all(
                (
                    lambda: self._ledger.remove_payload_audit_contract(
                        self, "double_reverse"
                    ),
                    self._carry_safety_cache.dispose,
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
