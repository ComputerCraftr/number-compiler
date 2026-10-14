"""Execute one admitted Collatz temporal run inside its resource scopes."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.fields.blank_ledger import BlankLedger
from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.boundary_macros import (
    BoundaryActionTemplateMemo,
)
from number_compiler.sequences.collatz.joint_temporal_action import (
    CollatzJointTemporalBuilder,
)
from number_compiler.sequences.collatz.physical_boundary_route import (
    leading_homogeneous_run,
)
from number_compiler.sequences.collatz.run_prefix_checkpoints import (
    _crosses_root_checkpoint,
    _publish_d8_root_checkpoints,
    _publish_run_root_checkpoints,
    observe_temporal_run_prefix,
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
from number_compiler.sequences.collatz.temporal_cycle_execution import (
    pump_normalized_one_cycle,
)
from number_compiler.sequences.collatz.temporal_dyadic import (
    D8CylinderFrame,
    D8TemporalTable,
    bounded_run_length,
)
from number_compiler.sequences.collatz.temporal_dyadic_cache_execution import (
    try_consume_cached_dyadic_action,
)
from number_compiler.sequences.collatz.temporal_f5_observer import (
    ODD_HALF_F5,
    CollatzF5AffineAction,
    _append_dyadic_f5,
    _run_one_f5,
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
from number_compiler.sequences.collatz.terminal_run_execution import (
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
_MIN_CYLINDER_SOURCE_BITS = 131_072


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
    control_bits = max(1, physical_ticks.bit_length())
    scratch.require_bits(8 * (seed.bit_length() + 4 * control_bits + 16))
    ledger.bump("collatz_physical_temporal_run_quotient_compilations")
    current = seed
    remaining = physical_ticks
    # Source selection composes only the selected finite action.
    normalized_f5 = CollatzF5AffineAction.identity() if include_f5 else None
    physical_f5 = CollatzF5AffineAction.identity() if include_f5 else None
    odd_ticks = division_ticks = normalized = phase = 0
    run_actions = zero_symbols = one_symbols = cycle_repetitions = 0
    width_spine = CollatzWidthSpineAccumulator(ledger, requested=include_width_spine)
    first_boundary: tuple[int, int, int, str] | None = None
    first_boundary_macro: CollatzBoundaryMacro | BorderReturnMacro | None = None
    pending_normalized_source: int | None = None
    d8_table: D8TemporalTable | None = None
    lookup_enabled = macros is not None
    previous_source, previous_width, previous_ones = seed, 0, 0
    share_width = 1 << (
        min(max(8, seed.bit_length()), max(8, physical_ticks // 2)).bit_length() - 1
    )

    def apply_boundary_application(
        state: MixedRunExecutorState,
        macro: CollatzBoundaryMacro | BorderReturnMacro,
    ) -> None:
        nonlocal current, remaining, normalized, division_ticks, odd_ticks
        nonlocal one_symbols, zero_symbols, run_actions, normalized_f5, physical_f5
        nonlocal first_boundary, first_boundary_macro
        nonlocal previous_source, previous_width, previous_ones
        if first_boundary is None and include_innovation_tape:
            first_boundary = (
                physical_ticks - remaining,
                current,
                macro.physical_ticks,
                macro.family,
            )
            first_boundary_macro = macro
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
        previous_source, previous_width, previous_ones = (
            current,
            normalized,
            one_symbols,
        )

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
        ) = initial
        previous_source, previous_width, previous_ones = (
            current,
            normalized,
            one_symbols,
        )

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
            MixedRunExecutorState(
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
            ),
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
            if not remaining:
                break

        if macros is not None and remaining >= 16:
            cached_state = consume_cached_mixed_state(
                MixedRunExecutorState(
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
                ),
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
                ) = cached_state
                previous_source, previous_width, previous_ones = (
                    current,
                    normalized,
                    one_symbols,
                )
                continue

        cached_state, lookup_enabled = try_consume_cached_dyadic_action(
            MixedRunExecutorState(
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
            ),
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
            ) = cached_state
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
                continue

        low, available, homogeneous_symbols = leading_homogeneous_run(
            current, remaining
        )
        homogeneous_prefix = homogeneous_symbols >= 8

        # Keep maximal homogeneous actions on their existing powered path.
        border_state, border = None, None
        # Root-relative D8 also owns large fibers: a border rebase would split
        # the admitted source and rematerialize its high fiber.
        root_d8_batch_admitted = (
            current.bit_length() > _MIN_CYLINDER_SOURCE_BITS and remaining >= 32
        )
        boundary_plan = admit_physical_boundary_plan(current, remaining, ledger)
        if not homogeneous_prefix and not root_d8_batch_admitted:
            border_state, border = consume_border_return(
                MixedRunExecutorState(
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
                ),
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

        # The macro owns its completing half-step; partial requests fall back
        # to exact run execution when the guard does not fit.
        if (
            boundary_plan is not None
            and boundary_plan.family == "989"
            and not include_innovation_tape
            and not include_joint_cocycle
        ):
            # Do not build observer-only certificates on ordinary requests.
            boundary_plan = None
        selected_mixed = None
        if (
            boundary_plan is not None
            and boundary_plan.physical_ticks < remaining
            and remaining >= 128
            and current.bit_length() >= 64
            and not homogeneous_prefix
        ):
            ledger.bump("collatz_physical_boundary_comparison_attempts")
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
                ledger.bump("collatz_physical_boundary_comparison_overrides")
        if boundary_plan is not None:
            boundary_state, named_boundary, lookup_enabled = consume_named_boundary(
                MixedRunExecutorState(
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
                ),
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
        if selected_mixed is not None or (
            not homogeneous_prefix and remaining >= 128 and current.bit_length() >= 64
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
                current.bit_length() <= _MIN_CYLINDER_SOURCE_BITS or remaining < 32
            ):
                # A joint demand retains completed rows through the framed
                # batch path.
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
                if remaining >= 8 + ones:
                    d8_endpoint: int | None = None
                    if include_joint_cocycle:
                        survives = advanced.above_cycle()
                    else:
                        if (
                            parity_builder is not None
                            or include_width_spine
                            and width_spine.complete
                        ):
                            d8_endpoint = advanced.materialize()
                            ledger.bump(
                                "collatz_physical_temporal_d8_frame_materializations"
                            )
                        else:
                            d8_endpoint = target_origin + 3**ones * (current >> 8)
                        ledger.bump("collatz_physical_temporal_d8_endpoint_evaluations")
                        survives = d8_endpoint > 2
                    ledger.bump(
                        "collatz_physical_temporal_run_operand_bits",
                        current.bit_length()
                        + (d8_endpoint.bit_length() if d8_endpoint is not None else 0)
                        + 26,
                    )
                    if survives:
                        d8_source = current
                        d8_offset = normalized
                        d8_odd_offset = one_symbols
                        if d8_width_summary is not None:
                            width_spine.record(d8_width_summary.blank)
                        if include_joint_cocycle:
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
                            if d8_transition is None:
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
                        ledger.bump("collatz_physical_temporal_dyadic_d8_pumps")
                        ledger.bump("collatz_physical_temporal_dyadic_symbols", 8)
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
                        continue
            else:
                frame = D8CylinderFrame(current)
                frame_width = current.bit_length()
                ledger.bump("collatz_physical_temporal_d8_source_window_bits", 8)
                accepted = 0
                # Consume bounded source windows, then resume exact runs.
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
                        "collatz_physical_temporal_d8_frame_operand_bits",
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
                    if parity_builder is not None:
                        (
                            advanced,
                            ones,
                            residue,
                            target_origin,
                            d8_width_summary,
                            parity_transition,
                        ) = d8_table.transition_with_parity_word(
                            frame,
                            with_width=include_width_spine and width_spine.complete,
                            with_joint=include_joint_cocycle,
                        )
                        d8_action = parity_transition.action
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
                    # Let exact runs reach the earliest cycle entry before
                    # pumping the normalized 1↔2 cycle.
                    if advanced.source.bit_length() <= advanced.consumed + 2:
                        ledger.bump("collatz_physical_temporal_d8_endpoint_evaluations")
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
                        if accepted == 0:
                            parity_builder.begin_d8_batch(current, block_frame)
                        parity_builder.append_d8_transition(parity_transition)
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
                    ledger.bump("collatz_physical_temporal_dyadic_d8_pumps")
                    ledger.bump("collatz_physical_temporal_dyadic_symbols", 8)
                    if macros is not None and _crosses_root_checkpoint(
                        block_normalized_offset, 8, seed.bit_length()
                    ):
                        # Materialize only at logarithmically many root points.
                        block_source_value = block_frame.materialize()
                        block_endpoint = frame.materialize()
                        ledger.bump(
                            "collatz_temporal_root_checkpoint_frame_materializations",
                            2,
                        )
                        ledger.bump(
                            "collatz_temporal_root_checkpoint_frame_operand_bits",
                            block_source_value.bit_length()
                            + block_endpoint.bit_length(),
                        )
                        _publish_d8_root_checkpoints(
                            macros,
                            scratch,
                            anchor=seed,
                            source=block_source_value,
                            normalized_offset=block_normalized_offset,
                            odd_offset=block_odd_offset,
                            endpoint=block_endpoint,
                            odd_symbols=ones,
                        )
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
                            "collatz_physical_temporal_d8_frame_materializations"
                        )
                        ledger.bump("collatz_physical_temporal_d8_endpoint_evaluations")
                    if not include_joint_cocycle:
                        ledger.bump(
                            "collatz_physical_temporal_run_operand_bits",
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
            ledger.bump("collatz_physical_temporal_zero_run_pumps")
            ledger.bump("collatz_physical_temporal_zero_run_symbols", length)
            ledger.bump(
                "collatz_physical_temporal_run_operand_bits",
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
            continue

        complete = min(available, remaining // 2)
        if complete:
            run_source = current
            run_offset = normalized
            run_odd_offset = one_symbols
            scratch.require_bits(
                8 * (current.bit_length() + 2 * complete + 4 * control_bits + 16)
            )
            before_bits = current.bit_length()
            joint_source = current
            if include_joint_cocycle:
                joint_builder.append_run(joint_source, complete, odd=True)
            if parity_builder is not None:
                current, power3 = parity_builder.append_one_run(run_source, complete)
            else:
                power3 = 3**complete
                current = power3 * ((current + 1) >> complete) - 1
            if width_spine.complete:
                displacement = current.bit_length() - before_bits
                # Each odd raw cell is at most one bit above its normalized
                # boundary.
                segment = BlankLedger(displacement, 0, displacement + 1)
                width_spine.record(segment)
            if normalized_f5 is not None and physical_f5 is not None:
                f5 = _run_one_f5(complete)
                normalized_f5 = normalized_f5.then(f5)
                physical_f5 = physical_f5.then(f5)
            remaining -= 2 * complete
            odd_ticks += complete
            division_ticks += complete
            normalized += complete
            one_symbols += complete
            run_actions += 1
            ledger.bump("collatz_physical_temporal_one_run_pumps")
            ledger.bump("collatz_physical_temporal_one_run_symbols", complete)
            ledger.bump(
                "collatz_physical_temporal_run_operand_bits",
                before_bits
                + power3.bit_length()
                + current.bit_length()
                + complete.bit_length(),
            )
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
        if remaining:
            if complete >= available or remaining != 1 or not current & 1:
                continue
            scratch.require_bits(8 * (current.bit_length() + 4 * control_bits + 18))
            before_bits = current.bit_length()
            ledger.bump(
                "collatz_physical_temporal_run_operand_bits",
                current.bit_length() + 2,
            )
            pending_normalized_source = current
            current = 3 * current + 1
            if width_spine.complete:
                displacement = current.bit_length() - before_bits
                segment = BlankLedger(
                    displacement,
                    min(0, displacement),
                    max(0, displacement),
                )
                width_spine.record(segment)
            if physical_f5 is not None:
                physical_f5 = physical_f5.then(ODD_HALF_F5)
            odd_ticks += 1
            remaining = 0
            phase = 1
            run_actions += 1
            ledger.bump("collatz_physical_temporal_odd_half_steps")

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
        first_boundary=first_boundary,
        first_boundary_macro=first_boundary_macro,
    )
