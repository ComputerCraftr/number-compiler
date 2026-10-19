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
from number_compiler.sequences.collatz.run_prefix_checkpoints import (
    publish_run_root_checkpoints,
)
from number_compiler.sequences.collatz.tape_width import (
    CollatzWidthSpineAccumulator,
    charge_width_repeat,
)
from number_compiler.sequences.collatz.temporal_f5_observer import (
    CYCLE_F5,
    CollatzF5AffineAction,
    run_one_f5,
    run_zero_f5,
)
from number_compiler.sequences.collatz.temporal_mixed_execution import (
    MixedRunExecutorState,
)
from number_compiler.sequences.collatz.terminal_run_execution import (
    consume_pending_odd_half_step,
)

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.innovation_input_tape import (
        ParityProgramBuilder,
    )
    from number_compiler.sequences.collatz.source_cylinder_cache import (
        CollatzDyadicMacros,
    )
    from number_compiler.sequences.collatz.temporal_run_state import CollatzRunControl


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
        f5 = run_one_f5(length)
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
        cycle_f5 = CYCLE_F5.power(repetitions)
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


def consume_homogeneous_run(
    control: CollatzRunControl,
    *,
    seed: int,
    available: int,
    control_bits: int,
    include_joint_cocycle: bool,
    ledger: ResourceLedger,
    scratch: RunArithmeticWorkspace,
    width_spine: CollatzWidthSpineAccumulator,
    joint_builder: CollatzJointTemporalBuilder,
    parity_builder: ParityProgramBuilder | None,
    macros: CollatzDyadicMacros | None,
) -> None:
    """Consume the selected even/odd run, retaining any pending odd half tick."""
    if control.current & 1 == 0:
        length = min(available, control.remaining)
        run_source = control.current
        run_offset = control.normalized
        run_odd_offset = control.one_symbols
        before_bits = control.current.bit_length()
        joint_source = control.current
        if parity_builder is not None:
            control.current = parity_builder.append_zero_run(run_source, length)
        else:
            control.current >>= length
        if include_joint_cocycle:
            joint_builder.append_run(joint_source, length, odd=False)
        if width_spine.complete:
            after_bits = control.current.bit_length()
            segment = BlankLedger(
                after_bits - before_bits,
                min(0, after_bits - before_bits),
                max(0, after_bits - before_bits),
            )
            width_spine.record(segment)
        if control.normalized_f5 is not None and control.physical_f5 is not None:
            f5 = run_zero_f5(length)
            control.normalized_f5 = control.normalized_f5.then(f5)
            control.physical_f5 = control.physical_f5.then(f5)
        control.remaining -= length
        control.division_ticks += length
        control.normalized += length
        control.zero_symbols += length
        control.run_actions += 1
        ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_ZERO_RUN_PUMPS)
        ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_ZERO_RUN_SYMBOLS, length)
        ledger.bump(
            _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_RUN_OPERAND_BITS,
            before_bits + control.current.bit_length() + length.bit_length(),
        )
        if macros is not None and control.current > 2:
            publish_run_root_checkpoints(
                macros,
                scratch,
                anchor=seed,
                source=run_source,
                normalized_offset=run_offset,
                odd_offset=run_odd_offset,
                run_length=length,
                odd_run=False,
            )
        control.unified_skew_retry = True
        return

    complete = min(available, control.remaining // 2)
    if complete:
        run_source = control.current
        run_offset = control.normalized
        run_odd_offset = control.one_symbols
        control.current, control.normalized_f5, control.physical_f5 = (
            pump_normalized_ones(
                control.current,
                complete,
                scratch=scratch,
                control_bits=control_bits,
                width_spine=width_spine,
                joint_builder=joint_builder if include_joint_cocycle else None,
                parity_builder=parity_builder,
                normalized_f5=control.normalized_f5,
                physical_f5=control.physical_f5,
            )
        )
        control.remaining -= 2 * complete
        control.odd_ticks += complete
        control.division_ticks += complete
        control.normalized += complete
        control.one_symbols += complete
        control.run_actions += 1
        if macros is not None and control.current > 2:
            publish_run_root_checkpoints(
                macros,
                scratch,
                anchor=seed,
                source=run_source,
                normalized_offset=run_offset,
                odd_offset=run_odd_offset,
                run_length=complete,
                odd_run=True,
            )
        control.unified_skew_retry = True
    if control.remaining:
        if complete >= available or control.remaining != 1 or not control.current & 1:
            return
        control.pending_normalized_source = control.current
        half_step = consume_pending_odd_half_step(
            control.current,
            ledger=ledger,
            scratch=scratch,
            control_bits=control_bits,
            width_spine=width_spine,
            odd_ticks=control.odd_ticks,
            run_actions=control.run_actions,
            physical_f5=control.physical_f5,
        )
        control.current = half_step.endpoint
        control.odd_ticks = half_step.odd_ticks
        control.run_actions = half_step.run_actions
        control.physical_f5 = half_step.physical_f5
        control.remaining = 0
        control.phase = 1
