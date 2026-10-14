"""Exact normalized 1↔2 cycle pumping for physical Collatz runs."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.fields.blank_ledger import BlankLedger
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.joint_temporal_action import (
    CollatzJointTemporalBuilder,
)
from number_compiler.sequences.collatz.tape_width import (
    CollatzWidthSpineAccumulator,
    charge_width_repeat,
)
from number_compiler.sequences.collatz.temporal_f5_observer import (
    _CYCLE_F5,
)
from number_compiler.sequences.collatz.temporal_mixed_execution import (
    MixedRunExecutorState,
)

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.innovation_input_tape import (
        ParityProgramBuilder,
    )


def pump_normalized_one_cycle(
    state: MixedRunExecutorState,
    *,
    ledger: ResourceLedger,
    width_spine: CollatzWidthSpineAccumulator,
    include_joint: bool,
    joint_builder: CollatzJointTemporalBuilder,
    parity_builder: ParityProgramBuilder | None,
) -> tuple[MixedRunExecutorState, int] | None:
    """Consume every complete three-tick cycle when the state is exactly 1."""
    if state.current != 1 or state.remaining < 3:
        return None
    repetitions, tail = divmod(state.remaining, 3)
    if not repetitions:
        return None
    if parity_builder is not None:
        parity_builder.append_cycle(repetitions)
    if include_joint:
        joint_builder.append_cycle(state.current, repetitions)
    normalized_f5 = state.normalized_f5
    physical_f5 = state.physical_f5
    if normalized_f5 is not None and physical_f5 is not None:
        cycle_f5 = _CYCLE_F5.power(repetitions)
        normalized_f5 = normalized_f5.then(cycle_f5)
        physical_f5 = physical_f5.then(cycle_f5)
    if width_spine.complete:
        cycle_blank = BlankLedger(0, 0, 2)
        charge_width_repeat(ledger, cycle_blank, repetitions)
        width_spine.record(cycle_blank.repeat(repetitions))
    ledger.bump("collatz_physical_temporal_cycle_pump_requests")
    ledger.bump("collatz_physical_temporal_cycle_pump_repetitions", repetitions)
    return (
        MixedRunExecutorState(
            state.current,
            tail,
            state.normalized + 2 * repetitions,
            state.division_ticks + 2 * repetitions,
            state.odd_ticks + repetitions,
            state.one_symbols + repetitions,
            state.zero_symbols + repetitions,
            state.run_actions + 1,
            normalized_f5,
            physical_f5,
        ),
        repetitions,
    )
