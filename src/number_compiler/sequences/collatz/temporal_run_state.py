"""Small exact state snapshots passed between Collatz run selectors."""

from __future__ import annotations

from typing import TYPE_CHECKING, NamedTuple

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


def prepare_run_control(
    seed: int, physical_ticks: int, scratch: RunArithmeticWorkspace
) -> int:
    """Reserve the initial operand workspace and return control-bit width."""
    control_bits = max(1, physical_ticks.bit_length())
    scratch.require_bits(8 * (seed.bit_length() + 4 * control_bits + 16))
    return control_bits


def executor_state(
    current: int,
    remaining: int,
    normalized: int,
    division_ticks: int,
    odd_ticks: int,
    one_symbols: int,
    zero_symbols: int,
    run_actions: int,
    normalized_f5: CollatzF5AffineAction | None,
    physical_f5: CollatzF5AffineAction | None,
) -> MixedRunExecutorState:
    """Build the shared immutable selector input from current run scalars."""
    return MixedRunExecutorState(
        current,
        remaining,
        normalized,
        division_ticks,
        odd_ticks,
        one_symbols,
        zero_symbols,
        run_actions,
        normalized_f5,
        physical_f5,
    )


class BoundaryApplicationSnapshot(NamedTuple):
    state: MixedRunExecutorState
    first_boundary_stamp: BoundaryOccurrenceProducerStamp | None
    first_boundary_macro: CollatzBoundaryMacro | BorderReturnMacro | None
    previous_source: int
    previous_width: int
    previous_ones: int
    unified_skew_retry: bool


def apply_boundary_application(
    state: MixedRunExecutorState,
    macro: CollatzBoundaryMacro | BorderReturnMacro | None,
    *,
    seed: int,
    physical_ticks: int,
    remaining: int,
    include_innovation_tape: bool,
    first_boundary_stamp: BoundaryOccurrenceProducerStamp | None,
    first_boundary_macro: CollatzBoundaryMacro | BorderReturnMacro | None,
    unified_skew_retry: bool,
    boundary_offset: int | None = None,
    rearm_unified: bool = False,
) -> BoundaryApplicationSnapshot:
    """Apply the shared fields of one selected boundary route."""
    if macro is not None or rearm_unified:
        unified_skew_retry = True
    if first_boundary_stamp is None and include_innovation_tape and macro is not None:
        first_boundary_stamp = BoundaryOccurrenceProducerStamp._issue_selected_macro(
            seed,
            physical_ticks,
            remaining,
            macro,
            boundary_offset=boundary_offset,
        )
        first_boundary_macro = macro
    return BoundaryApplicationSnapshot(
        state,
        first_boundary_stamp,
        first_boundary_macro,
        state.current,
        state.normalized,
        state.one_symbols,
        unified_skew_retry,
    )


__all__ = [
    "BoundaryApplicationSnapshot",
    "apply_boundary_application",
    "executor_state",
    "prepare_run_control",
]
