"""Consume admitted D8 source sections within the current Collatz run."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.sequences.collatz.run_prefix_checkpoints import (
    crosses_root_checkpoint,
    publish_d8_frame_root_checkpoints,
    publish_d8_root_checkpoints,
)
from number_compiler.sequences.collatz.temporal_dyadic import (
    D8CylinderFrame,
    D8TemporalTable,
    admit_d8_transition,
    bounded_run_length,
    d8_root_batch_admitted,
)
from number_compiler.sequences.collatz.temporal_f5_observer import append_dyadic_f5
from number_compiler.sequences.collatz.temporal_unified_skew_execution import (
    d8_frame_has_guarded_seam,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.dyadic_return_runs import (
        RunArithmeticWorkspace,
    )
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.collatz.innovation_input_tape import (
        ParityProgramBuilder,
    )
    from number_compiler.sequences.collatz.joint_temporal_action import (
        CollatzJointTemporalBuilder,
    )
    from number_compiler.sequences.collatz.source_cylinder_cache import (
        CollatzDyadicMacros,
    )
    from number_compiler.sequences.collatz.tape_width import (
        CollatzWidthSpineAccumulator,
    )
    from number_compiler.sequences.collatz.temporal_run_state import CollatzRunControl

_MAX_CYLINDER_BATCH_SYMBOLS = 64


def consume_d8_run_section(
    control: CollatzRunControl,
    *,
    seed: int,
    low: int,
    homogeneous_symbols: int,
    control_bits: int,
    include_innovation_tape: bool,
    include_joint_cocycle: bool,
    include_width_spine: bool,
    ledger: ResourceLedger,
    scratch: RunArithmeticWorkspace,
    width_spine: CollatzWidthSpineAccumulator,
    joint_builder: CollatzJointTemporalBuilder,
    parity_builder: ParityProgramBuilder | None,
    macros: CollatzDyadicMacros | None,
) -> bool:
    """Return whether the exact D8 route consumed the current run section."""
    if control.remaining >= 8 and homogeneous_symbols < 8:
        scratch.require_bits(8 * (control.current.bit_length() + 4 * control_bits + 32))
        if control.d8_table is None:
            control.d8_table = D8TemporalTable.for_ledger(ledger)
        table: D8TemporalTable = control.d8_table
        if not include_joint_cocycle and (
            not d8_root_batch_admitted(control.current, control.remaining)
        ):
            # A joint demand retains completed rows through the framed path.
            d8_frame = (
                D8CylinderFrame(control.current)
                if parity_builder is not None
                or include_joint_cocycle
                or (include_width_spine and width_spine.complete)
                else None
            )
            d8_action = None
            d8_width_summary = None
            d8_transition = None
            if parity_builder is not None:
                if d8_frame is None:
                    raise AssertionError("innovation D8 request has no frame")
                (
                    advanced,
                    ones,
                    residue,
                    target_origin,
                    d8_width_summary,
                    d8_transition,
                ) = table.transition_with_parity_word(
                    d8_frame,
                    with_width=include_width_spine and width_spine.complete,
                )
                d8_action = d8_transition.action
            elif include_joint_cocycle:
                if d8_frame is None:
                    raise AssertionError("joint D8 request has no frame")
                (
                    advanced,
                    ones,
                    residue,
                    target_origin,
                    d8_width_summary,
                    d8_action,
                ) = table.transition_with_joint_action(
                    d8_frame,
                    with_width=include_width_spine and width_spine.complete,
                )
            elif include_width_spine and width_spine.complete:
                if d8_frame is None:
                    raise AssertionError("width D8 request has no frame")
                advanced, ones, _residue, target_origin, d8_width_summary = (
                    table.transition_with_width(d8_frame)
                )
            else:
                ones, target_origin = control.d8_table.select(control.current)
                advanced = None
            if control.remaining >= 8 + ones:
                admission = admit_d8_transition(
                    control.current,
                    advanced,
                    target_origin=target_origin,
                    odd_symbols=ones,
                    retain_joint_action=include_joint_cocycle,
                    materialize_frame=(
                        parity_builder is not None
                        or include_width_spine
                        and width_spine.complete
                    ),
                    ledger=ledger,
                )
                d8_endpoint = admission.endpoint
                if admission.survives:
                    d8_source = control.current
                    d8_offset = control.normalized
                    d8_odd_offset = control.one_symbols
                    if d8_width_summary is not None:
                        width_spine.record(d8_width_summary.blank)
                    if include_joint_cocycle:
                        if advanced is None:
                            raise AssertionError(
                                "joint D8 transition lost its receiving frame"
                            )
                        if d8_action is None:
                            raise AssertionError("joint D8 action was not selected")
                        joint_builder.begin_d8_batch(control.current)
                        joint_builder.append_d8_transition(
                            d8_action, ones, control.current & 255
                        )
                        control.current = joint_builder.finish_d8_batch(
                            macros, advanced
                        )
                    else:
                        if d8_endpoint is None:
                            raise AssertionError("D8 endpoint was not evaluated")
                        control.current = d8_endpoint
                    if parity_builder is not None:
                        if d8_transition is None or advanced is None:
                            raise AssertionError("D8 parity word was not selected")
                        parity_builder.begin_d8_batch(d8_source, d8_frame)
                        parity_builder.append_d8_transition(d8_transition)
                        parity_builder.finish_d8_batch(control.current, advanced)
                    if (
                        control.normalized_f5 is not None
                        and control.physical_f5 is not None
                    ):
                        multiplier = 3**ones
                        control.normalized_f5, control.physical_f5 = append_dyadic_f5(
                            control.normalized_f5,
                            control.physical_f5,
                            multiplier,
                            target_origin,
                            low,
                        )
                    control.odd_ticks += ones
                    control.division_ticks += 8
                    control.normalized += 8
                    control.one_symbols += ones
                    control.zero_symbols += 8 - ones
                    control.remaining -= 8 + ones
                    control.run_actions += 1
                    ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_DYADIC_D8_PUMPS)
                    ledger.bump(
                        _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_DYADIC_SYMBOLS, 8
                    )
                    if macros is not None:
                        publish_d8_root_checkpoints(
                            macros,
                            scratch,
                            anchor=seed,
                            source=d8_source,
                            normalized_offset=d8_offset,
                            odd_offset=d8_odd_offset,
                            endpoint=control.current,
                            odd_symbols=ones,
                        )
                    if include_joint_cocycle and macros is not None:
                        control.restart_width_segment(width_spine)
                    control.unified_skew_retry = True
                    return True
        else:
            frame = D8CylinderFrame(control.current)
            frame_width = control.current.bit_length()
            ledger.bump(
                _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_D8_SOURCE_WINDOW_BITS, 8
            )
            accepted = 0
            while (
                control.remaining >= 8
                and frame.consumed < _MAX_CYLINDER_BATCH_SYMBOLS
                and frame.consumed < frame.source.bit_length()
            ):
                block_frame = frame
                block_normalized_offset = control.normalized
                block_odd_offset = control.one_symbols
                frame_bits = max(frame.origin.bit_length(), frame.gain.bit_length())
                scratch.require_bits(
                    8
                    * (
                        control.current.bit_length()
                        + frame_bits
                        + 4 * control_bits
                        + 48
                    )
                )
                local = frame.local_word()
                residue = local & 255
                ledger.bump(
                    _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_D8_FRAME_OPERAND_BITS,
                    local.bit_length() + frame.gain.bit_length(),
                )
                capped = bounded_run_length(residue)
                homogeneous = min(
                    capped, control.remaining // 2 if residue & 1 else control.remaining
                )
                if homogeneous >= 8:
                    break
                d8_width_summary = None
                d8_action = None
                d8_transition = None
                if parity_builder is not None:
                    (
                        advanced,
                        ones,
                        residue,
                        target_origin,
                        d8_width_summary,
                        d8_transition,
                    ) = table.transition_with_parity_word(
                        frame,
                        with_width=include_width_spine and width_spine.complete,
                        with_joint=include_joint_cocycle,
                    )
                    d8_action = d8_transition.action
                elif include_joint_cocycle:
                    (
                        advanced,
                        ones,
                        residue,
                        target_origin,
                        d8_width_summary,
                        d8_action,
                    ) = table.transition_with_joint_action(
                        frame,
                        with_width=include_width_spine and width_spine.complete,
                    )
                else:
                    advanced, ones, residue, target_origin = table.transition(frame)
                if control.remaining < 8 + ones:
                    break
                # Let exact runs reach the earliest normalized 1↔2 entry.
                if advanced.source.bit_length() <= advanced.consumed + 2:
                    ledger.bump(
                        _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_D8_ENDPOINT_EVALUATIONS
                    )
                if not advanced.above_cycle():
                    break
                if include_joint_cocycle:
                    if d8_width_summary is not None:
                        width_spine.record(d8_width_summary.blank)
                        frame_width = d8_width_summary.target_width
                elif include_width_spine and width_spine.complete:
                    d8_width = table.width_summary_for_transition(
                        frame, advanced, ones, frame_width
                    )
                    d8_width_summary = d8_width
                    width_spine.record(d8_width.blank)
                    frame_width = d8_width.target_width
                if include_joint_cocycle:
                    if d8_action is None:
                        raise AssertionError("joint D8 action was not selected")
                    if accepted == 0:
                        joint_builder.begin_d8_batch(control.current)
                    joint_builder.append_d8_transition(d8_action, ones, residue)
                if parity_builder is not None:
                    if d8_transition is None:
                        raise AssertionError("parity D8 transition was not selected")
                    if accepted == 0:
                        parity_builder.begin_d8_batch(control.current, block_frame)
                    parity_builder.append_d8_transition(d8_transition)
                if (
                    control.normalized_f5 is not None
                    and control.physical_f5 is not None
                ):
                    multiplier = 3**ones
                    control.normalized_f5, control.physical_f5 = append_dyadic_f5(
                        control.normalized_f5,
                        control.physical_f5,
                        multiplier,
                        target_origin,
                        residue,
                    )
                frame = advanced
                accepted += 1
                control.odd_ticks += ones
                control.division_ticks += 8
                control.normalized += 8
                control.one_symbols += ones
                control.zero_symbols += 8 - ones
                control.remaining -= 8 + ones
                control.run_actions += 1
                ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_DYADIC_D8_PUMPS)
                ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_DYADIC_SYMBOLS, 8)
                if macros is not None and crosses_root_checkpoint(
                    block_normalized_offset, 8, seed.bit_length()
                ):
                    publish_d8_frame_root_checkpoints(
                        macros,
                        scratch,
                        anchor=seed,
                        source_frame=block_frame,
                        normalized_offset=block_normalized_offset,
                        odd_offset=block_odd_offset,
                        endpoint_frame=frame,
                        odd_symbols=ones,
                        ledger=ledger,
                    )
                if (include_joint_cocycle or include_innovation_tape) and (
                    d8_frame_has_guarded_seam(advanced, control.remaining, ledger)
                ):
                    break
            if accepted:
                scratch.require_bits(
                    8
                    * (
                        control.current.bit_length()
                        + frame.gain.bit_length()
                        + 4 * control_bits
                        + 48
                    )
                )
                control.current = (
                    joint_builder.finish_d8_batch(macros, frame)
                    if include_joint_cocycle
                    else frame.materialize()
                )
                if parity_builder is not None:
                    parity_builder.finish_d8_batch(control.current, frame)
                if not include_joint_cocycle:
                    ledger.bump(
                        _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_D8_FRAME_MATERIALIZATIONS
                    )
                    ledger.bump(
                        _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_D8_ENDPOINT_EVALUATIONS
                    )
                if not include_joint_cocycle:
                    ledger.bump(
                        _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_RUN_OPERAND_BITS,
                        frame.source.bit_length()
                        + frame.gain.bit_length()
                        + control.current.bit_length(),
                    )
                if include_joint_cocycle and macros is not None:
                    control.restart_width_segment(width_spine)
                control.unified_skew_retry = True
                return True
    return False
