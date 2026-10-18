"""Exact homogeneous-run and normalized-cycle pumping for physical Collatz."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.fields.blank_ledger import BlankLedger
from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.sequences.collatz.joint_temporal_action import (
    CollatzJointTemporalBuilder,
)
from number_compiler.sequences.collatz.tape_width import (
    CollatzWidthSpineAccumulator,
    charge_width_repeat,
)
from number_compiler.sequences.collatz.temporal_f5_observer import (
    _CYCLE_F5,
    CollatzF5AffineAction,
    _run_one_f5,
)
from number_compiler.sequences.collatz.temporal_mixed_execution import (
    MixedRunExecutorState,
)

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.innovation_input_tape import (
        ParityProgramBuilder,
    )


def pump_normalized_ones(
    source: int,
    length: int,
    *,
    scratch: RunArithmeticWorkspace,
    control_bits: int,
    width_spine: CollatzWidthSpineAccumulator,
    joint_builder: CollatzJointTemporalBuilder | None,
    parity_builder: ParityProgramBuilder | None,
    normalized_f5: CollatzF5AffineAction | None,
    physical_f5: CollatzF5AffineAction | None,
) -> tuple[int, CollatzF5AffineAction | None, CollatzF5AffineAction | None]:
    """Apply an admitted one-run and publish its demanded projections once."""
    scratch.require_bits(8 * (source.bit_length() + 2 * length + 4 * control_bits + 16))
    before_bits = source.bit_length()
    if joint_builder is not None:
        joint_builder.append_run(source, length, odd=True)
    if parity_builder is not None:
        endpoint, power3 = parity_builder.append_one_run(source, length)
    else:
        power3 = 3**length
        endpoint = power3 * ((source + 1) >> length) - 1
    if width_spine.complete:
        displacement = endpoint.bit_length() - before_bits
        # Each odd raw cell is at most one bit above its normalized bound.
        width_spine.record(BlankLedger(displacement, 0, displacement + 1))
    if normalized_f5 is not None and physical_f5 is not None:
        f5 = _run_one_f5(length)
        normalized_f5 = normalized_f5.then(f5)
        physical_f5 = physical_f5.then(f5)
    ledger = scratch.ledger
    ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_ONE_RUN_PUMPS)
    ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_ONE_RUN_SYMBOLS, length)
    ledger.bump(
        _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_RUN_OPERAND_BITS,
        before_bits + power3.bit_length() + endpoint.bit_length() + length.bit_length(),
    )
    return endpoint, normalized_f5, physical_f5


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
    ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_CYCLE_PUMP_REQUESTS)
    ledger.bump(
        _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_CYCLE_PUMP_REPETITIONS, repetitions
    )
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
