"""Execute one admitted Collatz temporal run inside its resource scopes."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.fields.blank_ledger import BlankLedger
from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.sequences.collatz.border_identity import (
    ENTRY_89_AT_NINE,
    BoundaryOccurrenceProducerStamp,
)
from number_compiler.sequences.collatz.boundary_macros import (
    BoundaryActionTemplateMemo,
)
from number_compiler.sequences.collatz.conditional_scheduler_route import (
    try_consume_conditional_route,
)
from number_compiler.sequences.collatz.joint_temporal_action import (
    CollatzJointTemporalBuilder,
)
from number_compiler.sequences.collatz.physical_boundary_route import (
    leading_homogeneous_run,
)
from number_compiler.sequences.collatz.run_prefix_checkpoints import (
    _crosses_root_checkpoint,
    _publish_d8_frame_root_checkpoints,
    _publish_d8_root_checkpoints,
    _publish_run_root_checkpoints,
    defer_unified_skew_reentry_for_root_checkpoint,
    observe_temporal_run_prefix,
    temporal_run_share_width,
)
from number_compiler.sequences.collatz.source_cylinder_cache import CollatzDyadicMacros
from number_compiler.sequences.collatz.tape_width import (
    CollatzWidthSpineAccumulator,
)
from number_compiler.sequences.collatz.temporal_border_return_execution import (
    admit_physical_boundary_plan,
    consume_border_return,
    consume_named_boundary,
    minimum_useful_border_extent,
)
from number_compiler.sequences.collatz.temporal_dyadic import (
    D8CylinderFrame,
    D8TemporalTable,
    admit_d8_transition,
    bounded_run_length,
    d8_root_batch_admitted,
)
from number_compiler.sequences.collatz.temporal_dyadic_cache_execution import (
    try_consume_cached_dyadic_action,
)
from number_compiler.sequences.collatz.temporal_f5_observer import (
    CollatzF5AffineAction,
    _append_dyadic_f5,
    _run_zero_f5,
)
from number_compiler.sequences.collatz.temporal_mixed_execution import (
    MixedRouteNotAdmitted,
    MixedRunExecutorState,
    consume_cached_mixed_state,
    consume_initial_mixed_route,
    select_and_consume_mixed_run,
    select_mixed_macro,
)
from number_compiler.sequences.collatz.temporal_run_finalize import (
    finalize_collatz_temporal_run,
)
from number_compiler.sequences.collatz.temporal_run_pumping import (
    pump_normalized_one_cycle,
    pump_normalized_ones,
)
from number_compiler.sequences.collatz.temporal_run_state import (
    apply_boundary_application as build_boundary_application,
)
from number_compiler.sequences.collatz.temporal_run_state import (
    executor_state,
    prepare_run_control,
)
from number_compiler.sequences.collatz.temporal_unified_skew_execution import (
    attempt_unified_skew_reentry,
    d8_frame_has_guarded_seam,
)
from number_compiler.sequences.collatz.terminal_run_execution import (
    consume_pending_odd_half_step,
    consume_terminal_power_two,
)

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.border_return_grammar import (
        BorderReturnMacro,
    )
    from number_compiler.sequences.collatz.boundary_macros import (
        CollatzBoundaryMacro,
    )
    from number_compiler.sequences.collatz.innovation_input_tape import (
        ParityProgramBuilder,
    )
    from number_compiler.sequences.collatz.temporal_run_result import (
        CollatzTemporalRunQuotient,
    )

_MAX_CYLINDER_BATCH_SYMBOLS = 64


def execute_collatz_temporal_run(
    seed: int,
    physical_ticks: int,
    *,
    ledger: ResourceLedger,
    include_f5: bool,
    include_width_spine: bool,
    include_joint_cocycle: bool,
    include_innovation_tape: bool,
    require_mixed_prefix: bool,
    innovation_modulus: int | None,
    macros: CollatzDyadicMacros | None,
    scratch: RunArithmeticWorkspace,
    joint_builder: CollatzJointTemporalBuilder,
    parity_builder: ParityProgramBuilder | None,
    boundary_templates: BoundaryActionTemplateMemo,
) -> CollatzTemporalRunQuotient:
    """Run the production source selector and finalize its admitted result."""
    control_bits = prepare_run_control(seed, physical_ticks, scratch)
    ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_RUN_QUOTIENT_COMPILATIONS)
    current = seed
    remaining = physical_ticks
    normalized_f5 = CollatzF5AffineAction.identity() if include_f5 else None
    physical_f5 = CollatzF5AffineAction.identity() if include_f5 else None
    odd_ticks = division_ticks = normalized = phase = 0
    run_actions = zero_symbols = one_symbols = cycle_repetitions = 0
    width_spine = CollatzWidthSpineAccumulator(ledger, requested=include_width_spine)
    first_boundary_stamp: BoundaryOccurrenceProducerStamp | None = None
    first_boundary_macro: CollatzBoundaryMacro | BorderReturnMacro | None = None
    unified_skew_chain = None
    # Retry per authenticated seam; failed selection holds the source unchanged.
    unified_skew_retry = not require_mixed_prefix
    pending_normalized_source: int | None = None
    d8_table: D8TemporalTable | None = None
    lookup_enabled = macros is not None
    previous_source, previous_width, previous_ones = seed, 0, 0
    share_width = temporal_run_share_width(seed, physical_ticks)

    def current_state() -> MixedRunExecutorState:
        return executor_state(
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

    def apply_boundary_application(
        state: MixedRunExecutorState,
        macro: CollatzBoundaryMacro | BorderReturnMacro | None,
        *,
        boundary_offset: int | None = None,
        rearm_unified: bool = False,
    ) -> None:
        nonlocal current, remaining, normalized, division_ticks, odd_ticks
        nonlocal one_symbols, zero_symbols, run_actions, normalized_f5, physical_f5
        nonlocal first_boundary_stamp, first_boundary_macro
        nonlocal previous_source, previous_width, previous_ones, unified_skew_retry
        applied = build_boundary_application(
            state,
            macro,
            seed=seed,
            physical_ticks=physical_ticks,
            remaining=remaining,
            include_innovation_tape=include_innovation_tape,
            first_boundary_stamp=first_boundary_stamp,
            first_boundary_macro=first_boundary_macro,
            unified_skew_retry=unified_skew_retry,
            boundary_offset=boundary_offset,
            rearm_unified=rearm_unified,
        )
        current, remaining, normalized, division_ticks, odd_ticks = applied.state[:5]
        one_symbols, zero_symbols, run_actions = applied.state[5:8]
        normalized_f5, physical_f5 = applied.state[8:]
        first_boundary_stamp = applied.first_boundary_stamp
        first_boundary_macro = applied.first_boundary_macro
        previous_source, previous_width, previous_ones = (
            applied.previous_source,
            applied.previous_width,
            applied.previous_ones,
        )
        unified_skew_retry = applied.unified_skew_retry

    if require_mixed_prefix:
        initial, d8_table = consume_initial_mixed_route(
            seed,
            remaining,
            control_bits=control_bits,
            templates=boundary_templates,
            ledger=ledger,
            d8_table=d8_table,
            include_width=width_spine.complete,
            width_spine=width_spine,
            include_joint=include_joint_cocycle,
            joint_builder=joint_builder,
            parity_builder=parity_builder,
            macros=macros,
            scratch=scratch,
            normalized_f5=normalized_f5,
            physical_f5=physical_f5,
        )
        if initial is None:
            raise MixedRouteNotAdmitted
        apply_boundary_application(initial, None)

    while remaining:
        scratch.require_bits(8 * (current.bit_length() + 4 * control_bits + 16))
        observe_temporal_run_prefix(
            macros,
            width_spine,
            previous_source=previous_source,
            previous_width=previous_width,
            previous_ones=previous_ones,
            current=current,
            normalized=normalized,
            one_symbols=one_symbols,
            anchor=seed,
            share_width=share_width,
        )
        previous_source, previous_width, previous_ones = (
            current,
            normalized,
            one_symbols,
        )
        cycle = pump_normalized_one_cycle(
            current_state(),
            ledger=ledger,
            width_spine=width_spine,
            include_joint=include_joint_cocycle,
            joint_builder=joint_builder,
            parity_builder=parity_builder,
        )
        if cycle is not None:
            state, repetitions = cycle
            (
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
            ) = state
            cycle_repetitions += repetitions
            if repetitions:
                unified_skew_retry = True
            if not remaining:
                break

        if macros is not None and remaining >= 16:
            cached_state = consume_cached_mixed_state(
                current_state(),
                ledger=ledger,
                include_width=width_spine.complete,
                width_spine=width_spine,
                include_joint=include_joint_cocycle,
                joint_builder=joint_builder,
                parity_builder=parity_builder,
                macros=macros,
                scratch=scratch,
            )
            if cached_state is not None:
                apply_boundary_application(cached_state, None, rearm_unified=True)
                continue

        cached_state, lookup_enabled = try_consume_cached_dyadic_action(
            current_state(),
            lookup_enabled,
            ledger=ledger,
            macros=macros,
            scratch=scratch,
            include_innovation_tape=include_innovation_tape,
            include_width_spine=include_width_spine,
            width_spine=width_spine,
            include_joint_cocycle=include_joint_cocycle,
            joint_builder=joint_builder,
        )
        if cached_state is not None:
            apply_boundary_application(cached_state, None, rearm_unified=True)
            continue

        if current & 1 and remaining >= 5:
            terminal = consume_terminal_power_two(
                current,
                remaining,
                normalized=normalized,
                division_ticks=division_ticks,
                odd_ticks=odd_ticks,
                one_symbols=one_symbols,
                zero_symbols=zero_symbols,
                run_actions=run_actions,
                normalized_f5=normalized_f5,
                physical_f5=physical_f5,
                ledger=ledger,
                scratch=scratch,
                control_bits=control_bits,
                include_joint=include_joint_cocycle,
                width_spine=width_spine,
                joint_builder=joint_builder,
                parity_builder=parity_builder,
            )
            if terminal is not None:
                macro = terminal.macro
                current = macro.endpoint
                remaining = terminal.remaining
                normalized = terminal.normalized
                division_ticks = terminal.division_ticks
                odd_ticks = terminal.odd_ticks
                one_symbols = terminal.one_symbols
                zero_symbols = terminal.zero_symbols
                run_actions = terminal.run_actions
                normalized_f5 = terminal.normalized_f5
                physical_f5 = terminal.physical_f5
                unified_skew_retry = True
                continue

        low, available, homogeneous_symbols = leading_homogeneous_run(
            current, remaining
        )
        homogeneous_prefix = homogeneous_symbols >= 8

        # Avoid crossing a fresh root checkpoint before its complete cylinder.
        defer_for_root_checkpoint = defer_unified_skew_reentry_for_root_checkpoint(
            macros,
            share_width,
            normalized,
            include_joint=include_joint_cocycle,
            include_innovation=include_innovation_tape,
            width_complete=width_spine.complete,
        )
        reentry = None
        if not defer_for_root_checkpoint:
            unified_skew_retry, reentry = attempt_unified_skew_reentry(
                seed,
                current,
                remaining,
                physical_ticks,
                retry=unified_skew_retry,
                require_mixed_prefix=require_mixed_prefix,
                homogeneous_prefix=homogeneous_prefix,
                normalized=normalized,
                division_ticks=division_ticks,
                odd_ticks=odd_ticks,
                one_symbols=one_symbols,
                zero_symbols=zero_symbols,
                run_actions=run_actions,
                control_bits=control_bits,
                templates=boundary_templates,
                ledger=ledger,
                scratch=scratch,
                include_joint=include_joint_cocycle,
                width_spine=width_spine,
                joint_builder=joint_builder,
                parity_builder=parity_builder,
                normalized_f5=normalized_f5,
                physical_f5=physical_f5,
                macros=macros,
                include_quadratic_clock=include_innovation_tape,
            )
        if reentry is not None:
            state, chain, global_offset, witness = reentry
            apply_boundary_application(state, witness, boundary_offset=global_offset)
            # Do not label a later-source chain as the root-prefix chain.
            if chain.source == seed:
                unified_skew_chain = chain
            unified_skew_retry = True
            continue

        new_state = try_consume_conditional_route(
            current_state(),
            require_mixed_prefix=require_mixed_prefix,
            homogeneous_prefix=homogeneous_prefix,
            deferred_for_root_checkpoint=defer_for_root_checkpoint,
            include_width_spine=include_width_spine,
            include_innovation_tape=include_innovation_tape,
            parity_route_requested=parity_builder is not None,
            source=current,
            remaining_ticks=remaining,
            scratch=scratch,
            control_bits=control_bits,
            include_joint=include_joint_cocycle,
            joint_builder=joint_builder,
            ledger=ledger,
            macros=macros,
        )
        if new_state is not None:
            apply_boundary_application(new_state, None, rearm_unified=True)
            continue

        border_state, border = None, None
        # Rebasing a root-relative D8 fiber would rematerialize its high fiber.
        root_d8_batch_admitted = d8_root_batch_admitted(current, remaining)
        boundary_plan = admit_physical_boundary_plan(current, remaining, ledger)
        if not homogeneous_prefix and not root_d8_batch_admitted:
            border_state, border = consume_border_return(
                current_state(),
                seed=seed,
                ledger=ledger,
                scratch=scratch,
                control_bits=control_bits,
                include_joint=include_joint_cocycle,
                width_spine=width_spine,
                joint_builder=joint_builder,
                parity_builder=parity_builder,
                macros=macros,
                minimum_useful_physical_ticks=minimum_useful_border_extent(
                    boundary_plan
                ),
            )
        if border_state is not None and border is not None:
            apply_boundary_application(border_state, border)
            width_spine.reset_segment()
            lookup_enabled = macros is not None
            continue

        # Partial requests fall back to exact runs when the guard does not fit.
        if (
            boundary_plan is not None
            and boundary_plan.identity == ENTRY_89_AT_NINE
            and not include_innovation_tape
            and not include_joint_cocycle
        ):
            boundary_plan = None
        selected_mixed = None
        if (
            not defer_for_root_checkpoint
            and boundary_plan is not None
            and boundary_plan.physical_ticks < remaining
            and remaining >= 128
            and current.bit_length() >= 64
            and not homogeneous_prefix
        ):
            ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_BOUNDARY_COMPARISON_ATTEMPTS)
            selected_mixed, d8_table = select_mixed_macro(
                current,
                remaining,
                templates=boundary_templates,
                ledger=ledger,
                d8_table=d8_table,
            )
            if (
                selected_mixed is not None
                and selected_mixed.physical_ticks > boundary_plan.physical_ticks
            ):
                boundary_plan = None
                ledger.bump(
                    _collatz_keys.COLLATZ_PHYSICAL_BOUNDARY_COMPARISON_OVERRIDES
                )
        if boundary_plan is not None:
            boundary_state, named_boundary, lookup_enabled = consume_named_boundary(
                current_state(),
                boundary_plan,
                seed=seed,
                ledger=ledger,
                scratch=scratch,
                control_bits=control_bits,
                templates=boundary_templates,
                include_joint=include_joint_cocycle,
                width_spine=width_spine,
                joint_builder=joint_builder,
                parity_builder=parity_builder,
                macros=macros,
                prior_lookup_enabled=lookup_enabled,
            )
            apply_boundary_application(boundary_state, named_boundary)
            continue

        # Use mixed discovery only where its bounded preview can replace work.
        if not defer_for_root_checkpoint and (
            selected_mixed is not None
            or (
                not homogeneous_prefix
                and remaining >= 128
                and current.bit_length() >= 64
            )
        ):
            progress, d8_table = select_and_consume_mixed_run(
                current,
                remaining,
                selected=selected_mixed,
                templates=boundary_templates,
                ledger=ledger,
                d8_table=d8_table,
                include_width=width_spine.complete,
                width_spine=width_spine,
                include_joint=include_joint_cocycle,
                joint_builder=joint_builder,
                parity_builder=parity_builder,
                macros=macros,
                scratch=scratch,
                normalized_f5=normalized_f5,
                physical_f5=physical_f5,
                normalized=normalized,
                division_ticks=division_ticks,
                odd_ticks=odd_ticks,
                one_symbols=one_symbols,
                zero_symbols=zero_symbols,
                run_actions=run_actions,
            )
            if progress is not None:
                current, remaining, normalized, division_ticks, odd_ticks = (
                    progress.current,
                    progress.remaining,
                    progress.normalized,
                    progress.division_ticks,
                    progress.odd_ticks,
                )
                one_symbols, zero_symbols = (
                    progress.one_symbols,
                    progress.zero_symbols,
                )
                run_actions = progress.run_actions
                normalized_f5 = progress.application.normalized_f5
                physical_f5 = progress.application.physical_f5
                unified_skew_retry = True
                previous_source, previous_width, previous_ones = (
                    current,
                    normalized,
                    one_symbols,
                )
                continue

        if remaining >= 8 and homogeneous_symbols < 8:
            scratch.require_bits(8 * (current.bit_length() + 4 * control_bits + 32))
            if d8_table is None:
                d8_table = D8TemporalTable.for_ledger(ledger)
            if not include_joint_cocycle and (
                not d8_root_batch_admitted(current, remaining)
            ):
                # A joint demand retains completed rows through the framed path.
                d8_frame = (
                    D8CylinderFrame(current)
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
                    ) = d8_table.transition_with_parity_word(
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
                    ) = d8_table.transition_with_joint_action(
                        d8_frame,
                        with_width=include_width_spine and width_spine.complete,
                    )
                elif include_width_spine and width_spine.complete:
                    if d8_frame is None:
                        raise AssertionError("width D8 request has no frame")
                    advanced, ones, _residue, target_origin, d8_width_summary = (
                        d8_table.transition_with_width(d8_frame)
                    )
                else:
                    ones, target_origin = d8_table.select(current)
                    advanced = None
                if remaining >= 8 + ones:
                    admission = admit_d8_transition(
                        current,
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
                        d8_source = current
                        d8_offset = normalized
                        d8_odd_offset = one_symbols
                        if d8_width_summary is not None:
                            width_spine.record(d8_width_summary.blank)
                        if include_joint_cocycle:
                            if advanced is None:
                                raise AssertionError(
                                    "joint D8 transition lost its receiving frame"
                                )
                            if d8_action is None:
                                raise AssertionError("joint D8 action was not selected")
                            joint_builder.begin_d8_batch(current)
                            joint_builder.append_d8_transition(
                                d8_action, ones, current & 255
                            )
                            current = joint_builder.finish_d8_batch(macros, advanced)
                        else:
                            if d8_endpoint is None:
                                raise AssertionError("D8 endpoint was not evaluated")
                            current = d8_endpoint
                        if parity_builder is not None:
                            if d8_transition is None or advanced is None:
                                raise AssertionError("D8 parity word was not selected")
                            parity_builder.begin_d8_batch(d8_source, d8_frame)
                            parity_builder.append_d8_transition(d8_transition)
                            parity_builder.finish_d8_batch(current, advanced)
                        if normalized_f5 is not None and physical_f5 is not None:
                            multiplier = 3**ones
                            normalized_f5, physical_f5 = _append_dyadic_f5(
                                normalized_f5,
                                physical_f5,
                                multiplier,
                                target_origin,
                                low,
                            )
                        odd_ticks += ones
                        division_ticks += 8
                        normalized += 8
                        one_symbols += ones
                        zero_symbols += 8 - ones
                        remaining -= 8 + ones
                        run_actions += 1
                        ledger.bump(
                            _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_DYADIC_D8_PUMPS
                        )
                        ledger.bump(
                            _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_DYADIC_SYMBOLS, 8
                        )
                        if macros is not None:
                            _publish_d8_root_checkpoints(
                                macros,
                                scratch,
                                anchor=seed,
                                source=d8_source,
                                normalized_offset=d8_offset,
                                odd_offset=d8_odd_offset,
                                endpoint=current,
                                odd_symbols=ones,
                            )
                        if include_joint_cocycle and macros is not None:
                            previous_source, previous_width, previous_ones = (
                                current,
                                normalized,
                                one_symbols,
                            )
                            width_spine.reset_segment()
                        unified_skew_retry = True
                        continue
            else:
                frame = D8CylinderFrame(current)
                frame_width = current.bit_length()
                ledger.bump(
                    _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_D8_SOURCE_WINDOW_BITS, 8
                )
                accepted = 0
                while (
                    remaining >= 8
                    and frame.consumed < _MAX_CYLINDER_BATCH_SYMBOLS
                    and frame.consumed < frame.source.bit_length()
                ):
                    block_frame = frame
                    block_normalized_offset = normalized
                    block_odd_offset = one_symbols
                    frame_bits = max(frame.origin.bit_length(), frame.gain.bit_length())
                    scratch.require_bits(
                        8 * (current.bit_length() + frame_bits + 4 * control_bits + 48)
                    )
                    local = frame.local_word()
                    residue = local & 255
                    ledger.bump(
                        _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_D8_FRAME_OPERAND_BITS,
                        local.bit_length() + frame.gain.bit_length(),
                    )
                    capped = bounded_run_length(residue)
                    homogeneous = min(
                        capped, remaining // 2 if residue & 1 else remaining
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
                        ) = d8_table.transition_with_parity_word(
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
                        ) = d8_table.transition_with_joint_action(
                            frame,
                            with_width=include_width_spine and width_spine.complete,
                        )
                    else:
                        advanced, ones, residue, target_origin = d8_table.transition(
                            frame
                        )
                    if remaining < 8 + ones:
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
                        d8_width = d8_table._width_summary_for_transition(
                            frame, advanced, ones, frame_width
                        )
                        d8_width_summary = d8_width
                        width_spine.record(d8_width.blank)
                        frame_width = d8_width.target_width
                    if include_joint_cocycle:
                        if d8_action is None:
                            raise AssertionError("joint D8 action was not selected")
                        if accepted == 0:
                            joint_builder.begin_d8_batch(current)
                        joint_builder.append_d8_transition(d8_action, ones, residue)
                    if parity_builder is not None:
                        if d8_transition is None:
                            raise AssertionError(
                                "parity D8 transition was not selected"
                            )
                        if accepted == 0:
                            parity_builder.begin_d8_batch(current, block_frame)
                        parity_builder.append_d8_transition(d8_transition)
                    if normalized_f5 is not None and physical_f5 is not None:
                        multiplier = 3**ones
                        normalized_f5, physical_f5 = _append_dyadic_f5(
                            normalized_f5,
                            physical_f5,
                            multiplier,
                            target_origin,
                            residue,
                        )
                    frame = advanced
                    accepted += 1
                    odd_ticks += ones
                    division_ticks += 8
                    normalized += 8
                    one_symbols += ones
                    zero_symbols += 8 - ones
                    remaining -= 8 + ones
                    run_actions += 1
                    ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_DYADIC_D8_PUMPS)
                    ledger.bump(
                        _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_DYADIC_SYMBOLS, 8
                    )
                    if macros is not None and _crosses_root_checkpoint(
                        block_normalized_offset, 8, seed.bit_length()
                    ):
                        _publish_d8_frame_root_checkpoints(
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
                        d8_frame_has_guarded_seam(advanced, remaining, ledger)
                    ):
                        break
                if accepted:
                    scratch.require_bits(
                        8
                        * (
                            current.bit_length()
                            + frame.gain.bit_length()
                            + 4 * control_bits
                            + 48
                        )
                    )
                    current = (
                        joint_builder.finish_d8_batch(macros, frame)
                        if include_joint_cocycle
                        else frame.materialize()
                    )
                    if parity_builder is not None:
                        parity_builder.finish_d8_batch(current, frame)
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
                            + current.bit_length(),
                        )
                    if include_joint_cocycle and macros is not None:
                        previous_source, previous_width, previous_ones = (
                            current,
                            normalized,
                            one_symbols,
                        )
                        width_spine.reset_segment()
                    unified_skew_retry = True
                    continue

        if current & 1 == 0:
            length = min(available, remaining)
            run_source = current
            run_offset = normalized
            run_odd_offset = one_symbols
            before_bits = current.bit_length()
            joint_source = current
            if parity_builder is not None:
                current = parity_builder.append_zero_run(run_source, length)
            else:
                current >>= length
            if include_joint_cocycle:
                joint_builder.append_run(joint_source, length, odd=False)
            if width_spine.complete:
                after_bits = current.bit_length()
                segment = BlankLedger(
                    after_bits - before_bits,
                    min(0, after_bits - before_bits),
                    max(0, after_bits - before_bits),
                )
                width_spine.record(segment)
            if normalized_f5 is not None and physical_f5 is not None:
                f5 = _run_zero_f5(length)
                normalized_f5 = normalized_f5.then(f5)
                physical_f5 = physical_f5.then(f5)
            remaining -= length
            division_ticks += length
            normalized += length
            zero_symbols += length
            run_actions += 1
            ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_ZERO_RUN_PUMPS)
            ledger.bump(
                _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_ZERO_RUN_SYMBOLS, length
            )
            ledger.bump(
                _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_RUN_OPERAND_BITS,
                before_bits + current.bit_length() + length.bit_length(),
            )
            if macros is not None and current > 2:
                _publish_run_root_checkpoints(
                    macros,
                    scratch,
                    anchor=seed,
                    source=run_source,
                    normalized_offset=run_offset,
                    odd_offset=run_odd_offset,
                    run_length=length,
                    odd_run=False,
                )
            unified_skew_retry = True
            continue

        complete = min(available, remaining // 2)
        if complete:
            run_source = current
            run_offset = normalized
            run_odd_offset = one_symbols
            current, normalized_f5, physical_f5 = pump_normalized_ones(
                current,
                complete,
                scratch=scratch,
                control_bits=control_bits,
                width_spine=width_spine,
                joint_builder=joint_builder if include_joint_cocycle else None,
                parity_builder=parity_builder,
                normalized_f5=normalized_f5,
                physical_f5=physical_f5,
            )
            remaining -= 2 * complete
            odd_ticks += complete
            division_ticks += complete
            normalized += complete
            one_symbols += complete
            run_actions += 1
            if macros is not None and current > 2:
                _publish_run_root_checkpoints(
                    macros,
                    scratch,
                    anchor=seed,
                    source=run_source,
                    normalized_offset=run_offset,
                    odd_offset=run_odd_offset,
                    run_length=complete,
                    odd_run=True,
                )
            unified_skew_retry = True
        if remaining:
            if complete >= available or remaining != 1 or not current & 1:
                continue
            pending_normalized_source = current
            half_step = consume_pending_odd_half_step(
                current,
                ledger=ledger,
                scratch=scratch,
                control_bits=control_bits,
                width_spine=width_spine,
                odd_ticks=odd_ticks,
                run_actions=run_actions,
                physical_f5=physical_f5,
            )
            current = half_step.endpoint
            odd_ticks = half_step.odd_ticks
            run_actions = half_step.run_actions
            physical_f5 = half_step.physical_f5
            remaining = 0
            phase = 1

    return finalize_collatz_temporal_run(
        seed=seed,
        physical_ticks=physical_ticks,
        current=current,
        phase=phase,
        ledger=ledger,
        macros=macros,
        previous_source=previous_source,
        previous_width=previous_width,
        previous_ones=previous_ones,
        normalized=normalized,
        one_symbols=one_symbols,
        share_width=share_width,
        width_spine=width_spine,
        division_ticks=division_ticks,
        odd_ticks=odd_ticks,
        run_actions=run_actions,
        include_joint_cocycle=include_joint_cocycle,
        joint_builder=joint_builder,
        parity_builder=parity_builder,
        innovation_modulus=innovation_modulus,
        pending_normalized_source=pending_normalized_source,
        zero_symbols=zero_symbols,
        cycle_repetitions=cycle_repetitions,
        normalized_f5=normalized_f5,
        physical_f5=physical_f5,
        first_boundary_stamp=first_boundary_stamp,
        first_boundary_macro=first_boundary_macro,
        unified_skew_chain=unified_skew_chain,
    )
