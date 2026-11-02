"""Small exact state snapshots passed between Collatz run selectors."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.sequences.collatz.border_identity import (
    BoundaryOccurrenceProducerStamp,
)
from number_compiler.sequences.collatz.border_return_grammar import BorderReturnMacro
from number_compiler.sequences.collatz.boundary_macros import CollatzBoundaryMacro
from number_compiler.sequences.collatz.temporal_f5_observer import (
    CollatzF5AffineAction,
)
from number_compiler.sequences.collatz.temporal_mixed_execution import (
    MixedRunExecutorState,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.dyadic_return_runs import (
        RunArithmeticWorkspace,
    )
    from number_compiler.sequences.collatz.tape_width import (
        CollatzWidthSpineAccumulator,
    )
    from number_compiler.sequences.collatz.temporal_dyadic import D8TemporalTable
    from number_compiler.sequences.collatz.unified_skew_chain import UnifiedSkewChain
    from number_compiler.sequences.collatz.weighted_right_congruence import (
        WeightedRightBinding,
    )


def prepare_run_control(
    seed: int, physical_ticks: int, scratch: RunArithmeticWorkspace
) -> int:
    """Reserve the initial operand workspace and return control-bit width."""
    control_bits = max(1, physical_ticks.bit_length())
    scratch.require_bits(8 * (seed.bit_length() + 4 * control_bits + 16))
    return control_bits


@dataclass(slots=True)
class CollatzRunControl:
    """Mutable run scalars; issued actions and immutable selector inputs stay separate."""

    seed: int
    physical_ticks: int
    include_innovation_tape: bool
    joint_requested: bool
    current: int
    remaining: int
    previous_source: int
    unified_skew_retry: bool
    lookup_enabled: bool
    normalized_f5: CollatzF5AffineAction | None
    physical_f5: CollatzF5AffineAction | None
    odd_ticks: int = 0
    division_ticks: int = 0
    normalized: int = 0
    phase: int = 0
    run_actions: int = 0
    zero_symbols: int = 0
    one_symbols: int = 0
    cycle_repetitions: int = 0
    first_boundary_stamp: BoundaryOccurrenceProducerStamp | None = None
    first_boundary_macro: CollatzBoundaryMacro | BorderReturnMacro | None = None
    unified_skew_chain: UnifiedSkewChain | None = None
    pending_normalized_source: int | None = None
    d8_table: D8TemporalTable | None = None
    previous_width: int = 0
    previous_ones: int = 0
    weighted_binding: WeightedRightBinding | None = None
    weighted_cursor_source: int | None = None

    def restart_width_segment(self, width_spine: CollatzWidthSpineAccumulator) -> None:
        """Start the next width segment at the current exact run endpoint."""
        self.previous_source, self.previous_width, self.previous_ones = (
            self.current,
            self.normalized,
            self.one_symbols,
        )
        width_spine.reset_segment()

    def snapshot(self) -> MixedRunExecutorState:
        """Supply the selector's exact immutable arithmetic input."""
        return MixedRunExecutorState(
            self.current,
            self.remaining,
            self.normalized,
            self.division_ticks,
            self.odd_ticks,
            self.one_symbols,
            self.zero_symbols,
            self.run_actions,
            self.normalized_f5,
            self.physical_f5,
        )

    def apply_boundary(
        self,
        state: MixedRunExecutorState,
        macro: CollatzBoundaryMacro | BorderReturnMacro | None,
        *,
        boundary_offset: int | None = None,
        rearm_unified: bool = False,
    ) -> None:
        """Commit the exact selector result and its first authenticated boundary."""
        if macro is not None or rearm_unified:
            self.unified_skew_retry = True
        if (
            self.first_boundary_stamp is None
            and self.include_innovation_tape
            and macro is not None
        ):
            self.first_boundary_stamp = (
                BoundaryOccurrenceProducerStamp.from_selected_macro(
                    self.seed,
                    self.physical_ticks,
                    self.remaining,
                    macro,
                    boundary_offset=boundary_offset,
                )
            )
            self.first_boundary_macro = macro
        (
            self.current,
            self.remaining,
            self.normalized,
            self.division_ticks,
            self.odd_ticks,
            self.one_symbols,
            self.zero_symbols,
            self.run_actions,
            self.normalized_f5,
            self.physical_f5,
        ) = state
        self.previous_source = state.current
        self.previous_width = state.normalized
        self.previous_ones = state.one_symbols
        # A future parity class is never transported through a foreign macro.
        # Its publisher may explicitly install a reauthenticated successor.
        self.weighted_binding = None
        self.weighted_cursor_source = None


__all__ = ["CollatzRunControl", "prepare_run_control"]
