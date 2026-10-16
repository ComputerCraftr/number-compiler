"""Reverse/add queries owned by the shared source-bound tile scheduler.

The causal boundary evaluator is no longer a production fallback. Identity,
one-step, fused two-step and guarded no-growth consumers use the original source.
General temporal pullback remains a construction obligation; compact action
syntax alone is not execution.
"""

from __future__ import annotations

from collections.abc import Iterator
from math import ceil, log2
from typing import TYPE_CHECKING, Any

from number_compiler.arithmetic.contracts.exact_tree_context import (
    OriginalSourceConstruction,
    source_reads_only,
)
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.fields.radix import (
    bit_width,
    digits_lsd,
    value_from_lsd_digits,
)
from number_compiler.arithmetic.polynomials.twisted_observer import (
    TwistedCylinderProjection,
)
from number_compiler.resources.ledger import ResourceLedger, ResourceScope
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys
from number_compiler.resources.output_stream_metrics import (
    closing_output_stream,
    initialize_output_stream_metrics,
    measured_output_stream,
)
from number_compiler.resources.stores import LedgerList
from number_compiler.sequences.reverse_add.palindrome import (
    mirror_obstruction_from_output,
    mirror_palindrome_from_output,
)

if TYPE_CHECKING:
    from number_compiler.resources.metric_records import HashLifeBehaviorMetrics
    from number_compiler.resources.reverse_power_metrics import ReverseAddPowerMetrics
    from number_compiler.sequences.reverse_add.boundary_window import (
        ReverseBoundaryWindowObservation,
    )
    from number_compiler.sequences.reverse_add.q19_spatial_bank_morphism import (
        ReverseAddSpatialBankMorphism,
    )
    from number_compiler.sequences.reverse_add.source_images import (
        ReverseSourceImageWorkspace,
    )
    from number_compiler.sequences.reverse_add.temporal_matrix import (
        ReverseInnovationBank,
        SkewMoment,
        SourceBoundMoment,
    )
    from number_compiler.sequences.reverse_add.temporal_residue99 import (
        ReverseAddResidue99,
    )
    from number_compiler.sequences.reverse_add.temporal_ring_harmonics import (
        ReverseAddTemporalRingBank,
    )


def pair_field_from_integer(value: int, base: int) -> tuple[int, ...]:
    """Original-source encoding retained for independent kernel consumers."""
    value = require_integer(value, "seed", 0)
    base = require_integer(base, "base", 2)
    return _pair_field_from_digits(digits_lsd(value, base))


def _pair_field_from_digits(digits: tuple[int, ...]) -> tuple[int, ...]:
    if type(digits) is not tuple or not digits:
        raise ValueError("reverse pair source requires original digits")
    return tuple(digits[i] + digits[-1 - i] for i in range(len(digits)))


class ReverseAddPoweredTerm:
    """Lazy source/action request; no successor or boundary replay backend."""

    __slots__ = (
        "__weakref__",
        "_binding",
        "_boundary_observer",
        "_boundary_observer_identity",
        "_ledger",
        "_mirror_output_scratch",
        "_source_construction",
        "_workspace",
        "_workspace_identity",
        "base",
        "generation",
        "seed",
    )

    def __init__(
        self,
        seed: int,
        generation: int,
        *,
        base: int = 10,
        max_context_nodes: int | None = None,
        max_cache_entries: int | None = None,
    ) -> None:
        self.seed = require_integer(seed, "seed", 0)
        self.generation = require_integer(generation, "generation", 0)
        self.base = require_integer(base, "base", 2)
        self._binding = (self.seed, self.generation, self.base)
        self._ledger = ResourceLedger(max_context_nodes, max_cache_entries)
        self._boundary_observer: object | None = None
        self._boundary_observer_identity: object | None = None
        initialize_output_stream_metrics(self._ledger, "reverse_output_stream")
        self._mirror_output_scratch: LedgerList[int] | None = None
        self._workspace: ReverseSourceImageWorkspace | None = None
        self._workspace_identity: ReverseSourceImageWorkspace | None = None
        self._source_construction: OriginalSourceConstruction | None = None
        self._ledger.register_execution_root(self)

    def _source_workspace(self) -> ReverseSourceImageWorkspace:
        from number_compiler.sequences.reverse_add.source_images import (
            ReverseSourceImageWorkspace,
        )

        if (self.seed, self.generation, self.base) != self._binding:
            raise ValueError("reverse/add term source/action binding changed")
        found = self._workspace
        if found is None:
            found = ReverseSourceImageWorkspace(
                self._ledger,
                self.seed,
                self.generation,
                base=self.base,
                source_construction=self._source_construction,
            )
            self._workspace = found
            self._workspace_identity = found
        elif found is not self._workspace_identity or found.ledger is not self._ledger:
            raise ValueError("reverse/add term workspace binding changed")
        return found

    def _prepare_recursive_source_authority(self) -> None:
        if (self.seed, self.generation, self.base) != self._binding:
            raise ValueError("reverse/add term source/action binding changed")
        if self.base == 10:
            return
        from number_compiler.sequences.reverse_add.source_images import (
            MAX_COMPLETED_CHILD_FALLBACK_STEPS,
        )

        if not 3 <= self.generation <= MAX_COMPLETED_CHILD_FALLBACK_STEPS:
            return
        if self._source_construction is not None:
            return
        pair = pair_field_from_integer(self.seed, self.base)
        blank = 2 * self.base - 1
        required = max(1, len(pair) + self.generation)
        extent = 1 << ((required - 1).bit_length())
        self._source_construction = OriginalSourceConstruction(
            ExactSource(
                pair,
                self.base,
                "reverse-add-pair",
                blank,
                extent,
                2 * self.base,
            )
        )
        self._ledger.bump(
            _reverse_add_keys.REVERSE_SOURCE_PAIR_AUTHORITY_SYMBOLS, len(pair)
        )

    @property
    def operator_nodes(self) -> int:
        return 0 if self._workspace is None else self._workspace.operator_nodes

    @property
    def compose_operations(self) -> int:
        return 0 if self._workspace is None else self._workspace.compose_operations

    @property
    def syntax_depth_bound(self) -> int:
        return 0 if self._workspace is None else self._workspace.syntax_depth_bound

    @property
    def descriptor_bits(self) -> int:
        return (
            bit_width(self.seed) + bit_width(self.base) + bit_width(self.generation) + 3
        )

    @property
    def maximum_width(self) -> int:
        if (self.seed, self.generation, self.base) != self._binding:
            raise ValueError("reverse/add term source/action binding changed")
        workspace = self._workspace
        if workspace is not None:
            if (
                workspace is not self._workspace_identity
                or workspace.ledger is not self._ledger
            ):
                raise ValueError("reverse/add term workspace binding changed")
            completed = workspace.completed_width_if_cached()
            if completed is not None:
                return completed
        return len(digits_lsd(self.seed, self.base)) + self.generation

    def digit(self, position: int) -> int:
        position = require_integer(position, "digit coordinate")
        if position < 0:
            raise IndexError(position)
        self._prepare_recursive_source_authority()
        return self._digit_source_only(position)

    @source_reads_only
    def _digit_source_only(self, position: int) -> int:
        position = require_integer(position, "digit coordinate")
        if position < 0:
            raise IndexError(position)
        return self._source_workspace().digit(position)

    def direct_powered_digit(self, position: int) -> int:
        """Compatibility alias; does not select another execution path."""
        return self.digit(position)

    def width(self) -> int:
        self._prepare_recursive_source_authority()
        return self._width_source_only()

    @source_reads_only
    def _width_source_only(self) -> int:
        return self._source_workspace().width()

    @property
    def estimated_bit_length(self) -> int:
        width = self.width()
        return width if self.base == 2 else max(1, ceil(width * log2(self.base)))

    def _measured_output_digits(self) -> Iterator[int]:
        def source() -> Iterator[int]:
            self._prepare_recursive_source_authority()
            yield from self._source_workspace().iter_digits()

        return measured_output_stream(self._ledger, "reverse_output_stream", source)

    def iter_digits(self) -> Iterator[int]:
        return self._measured_output_digits()

    def digits(self) -> tuple[int, ...]:
        return tuple(self.iter_digits())

    def is_palindrome(self) -> bool:
        width = self.width()
        if width == 1:
            return True
        with closing_output_stream(self._measured_output_digits()) as digits:
            return mirror_palindrome_from_output(
                width,
                digits,
                ledger=self._ledger,
                scratch=self._output_mirror_scratch(),
            )

    def _output_mirror_scratch(self) -> LedgerList[int]:
        scratch = self._mirror_output_scratch
        if scratch is None:
            owner = self._ledger.register(
                "reverse-output-mirror-scratch", "explicit_lowering"
            )
            scratch = self._ledger.make_list(
                owner, nodes_per_entry=2, append_only=False
            )
            self._mirror_output_scratch = scratch
        return scratch

    def mirror_obstruction(
        self, *, first_width: int = 1
    ) -> TwistedCylinderProjection | None:
        first_width = require_integer(first_width, "first sheet width", 1)
        width = self.width()
        scratch = self._output_mirror_scratch()
        with closing_output_stream(self._measured_output_digits()) as digits:
            return mirror_obstruction_from_output(
                width,
                digits,
                ledger=self._ledger,
                scratch=scratch,
                first_width=first_width,
            )

    def temporal_spatial_bank_morphism(
        self, start: int, count: int, *, period: int = 2
    ) -> ReverseAddSpatialBankMorphism:
        """Publish a source-issued protected spatial bank without an integer."""
        if (self.seed, self.generation, self.base) != self._binding:
            raise ValueError("reverse/add term source/action binding changed")
        if self.base != 10:
            raise ValueError("spatial bank morphism requires decimal reversal")
        return self._source_workspace().certified_spatial_bank_morphism(
            start, count, period=period
        )

    def temporal_ring_bank(
        self, start: int = 0, count: int = 8
    ) -> ReverseAddTemporalRingBank:
        """Finite source-certified GT/EQ/LT, F5 and carry/borrow ring output."""
        if (self.seed, self.generation, self.base) != self._binding:
            raise ValueError("reverse/add term source/action binding changed")
        return self._source_workspace().certified_temporal_ring_bank(start, count)

    def temporal_residue99(self) -> ReverseAddResidue99:
        """Predict mod-99 without initializing the Q19 source workspace."""
        if (self.seed, self.generation, self.base) != self._binding:
            raise ValueError("reverse/add term source/action binding changed")
        if self.base != 10:
            raise ValueError("temporal residue99 is decimal-only")
        from .temporal_residue99 import from_seed

        return from_seed(self.seed, self.generation)

    def temporal_matrix(self, *, max_bits: int = 16384) -> SourceBoundMoment:
        """Project the authenticated endpoint into its exact skew matrix."""
        from number_compiler.sequences.reverse_add.temporal_matrix import (
            source_bound_temporal_matrix,
        )

        return source_bound_temporal_matrix(self, max_bits=max_bits)

    def temporal_moments(self, *, modulus: int) -> SkewMoment:
        """Project modular U,V directly from the issued Q19 source SLP."""
        from number_compiler.sequences.reverse_add.temporal_matrix import (
            source_bound_modular_moments,
        )

        return source_bound_modular_moments(self, modulus=modulus)

    def temporal_stencil(
        self, *, max_bits: int = 16384, max_digits: int = 8192
    ) -> ReverseInnovationBank:
        """Observe the exact endpoint's bounded five-band/borrow stencil.

        Width and bit caps are checked before endpoint digit expansion. The
        returned future borrow stencil is diagnostic source law; it does not
        authorize skipping future full-root transitions.
        """
        if (self.seed, self.generation, self.base) != self._binding:
            raise ValueError("reverse/add term source/action binding changed")
        if self.base != 10:
            raise ValueError("temporal stencil is decimal-only")
        max_digits = require_integer(max_digits, "stencil digit budget", 1)
        if self.maximum_width > max_digits:
            raise ValueError("reverse/add stencil exceeds its digit budget")
        action = self.temporal_matrix(max_bits=max_bits)
        from number_compiler.sequences.reverse_add.temporal_matrix import (
            ReverseInnovationBank,
        )

        width = max(1, self.maximum_width)
        workspace_owner = self._ledger.register(
            f"reverse-temporal-stencil-work-{self._ledger.owner_count}",
            "temporary_work",
            scope=ResourceScope.INDEX_OWNED,
        )
        try:
            with self._ledger.reservation(
                workspace_owner,
                entries=16 * width + 64,
                nodes=16 * width + 64,
            ):
                return ReverseInnovationBank.observe(
                    action.target,
                    max_digits=max_digits,
                    ledger=self._ledger,
                )
        finally:
            self._ledger.mark_disposed(workspace_owner)

    def materialize(self, *, max_bits: int) -> int:
        max_bits = require_integer(max_bits, "output bit cap", 0)
        estimate = self.estimated_bit_length
        if estimate > max_bits:
            raise ValueError((estimate, max_bits))
        return value_from_lsd_digits(self.iter_digits(), self.base)

    def behavior_metrics(self) -> HashLifeBehaviorMetrics:
        from number_compiler.sequences.reverse_add.behavior_metrics import (
            reverse_behavior_metrics,
        )

        return reverse_behavior_metrics(self)

    def observe_boundary_macro(
        self,
        *,
        max_states: int = 4096,
        max_compositions: int = 50_000,
        max_relation_entries: int = 8192,
        max_relation_states: int = 32_768,
    ) -> ReverseBoundaryWindowObservation:
        """Return a conservative decimal edge observation for this term.

        The result contains no complete endpoint. Its finite relation cache is
        owned by this term's resource ledger and shared across K=2,4,8 demands.
        """
        if (self.seed, self.generation, self.base) != self._binding:
            raise ValueError("reverse/add term source/action binding changed")
        if self.base != 10:
            raise ValueError("boundary macro observation is decimal-only")
        from number_compiler.sequences.reverse_add.boundary_window import (
            ReverseBoundaryWindowObserver,
        )

        observer = self._boundary_observer
        if observer is None:
            observer = ReverseBoundaryWindowObserver(
                self.seed,
                self.generation,
                self._ledger,
                source_workspace=self._source_workspace(),
                max_states=max_states,
                max_compositions=max_compositions,
                max_relation_entries=max_relation_entries,
                max_relation_states=max_relation_states,
            )
            self._boundary_observer = observer
            self._boundary_observer_identity = observer
        elif (
            type(observer) is not ReverseBoundaryWindowObserver
            or observer is not self._boundary_observer_identity
            or observer.ledger is not self._ledger
            or observer.relations.ledger is not self._ledger
            or observer.binding != self._binding
            or observer.max_states != max_states
            or observer.max_compositions != max_compositions
            or observer.max_relation_entries != max_relation_entries
            or observer.max_relation_states != max_relation_states
        ):
            raise ValueError("boundary observer binding or budget changed")
        return observer.observe(
            seed=self.seed, generation=self.generation, base=self.base
        )

    def metrics(self) -> ReverseAddPowerMetrics:
        from number_compiler.resources.metric_collection import (
            collect_unindexed_metrics,
        )
        from number_compiler.resources.powered_metrics import project_powered_metrics
        from number_compiler.resources.reverse_power_metrics import (
            ReverseAddPowerMetrics,
        )

        return project_powered_metrics(
            ReverseAddPowerMetrics,
            collect_unindexed_metrics(self._ledger),
            seed=self.seed,
            base=self.base,
            generation=self.generation,
            operator_nodes=self.operator_nodes,
            compose_operations=self.compose_operations,
            syntax_depth_bound=self.syntax_depth_bound,
            descriptor_bits=self.descriptor_bits,
            spacetime_carry_direction="lsd-to-msd",
        )


__all__ = ["ReverseAddPowerMetrics", "ReverseAddPoweredTerm", "pair_field_from_integer"]


def __getattr__(name: str) -> Any:
    from number_compiler.api.lazy_exports import resolve_export

    return resolve_export(
        name,
        {"ReverseAddPowerMetrics": "number_compiler.resources.reverse_power_metrics"},
        globals(),
    )
