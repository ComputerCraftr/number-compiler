"""Execute one admitted Collatz temporal run inside its resource scopes."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.sequences.collatz.border_identity import (
    ENTRY_89_AT_NINE,
)
from number_compiler.sequences.collatz.boundary_templates import (
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
from number_compiler.sequences.collatz.temporal_d8_execution import (
    consume_d8_run_section,
)
from number_compiler.sequences.collatz.temporal_dyadic import (
    d8_root_batch_admitted,
)
from number_compiler.sequences.collatz.temporal_dyadic_cache_execution import (
    try_consume_cached_dyadic_action,
)
from number_compiler.sequences.collatz.temporal_f5_observer import (
    ODD_HALF_F5,
    CollatzF5AffineAction,
    project_dyadic_fields_f5,
)
from number_compiler.sequences.collatz.temporal_mixed_execution import (
    MixedRouteNotAdmitted,
    consume_cached_mixed_state,
    consume_initial_mixed_route,
    select_and_consume_mixed_run,
    select_mixed_macro,
)
from number_compiler.sequences.collatz.temporal_run_finalize import (
    finalize_collatz_temporal_run,
)
from number_compiler.sequences.collatz.temporal_run_pumping import (
    consume_homogeneous_run,
    pump_normalized_one_cycle,
    try_consume_joint_harmonic_band,
)
from number_compiler.sequences.collatz.temporal_run_state import (
    CollatzRunControl,
    prepare_run_control,
)
from number_compiler.sequences.collatz.temporal_unified_skew_execution import (
    attempt_unified_skew_reentry,
    has_unified_source_parent,
)
from number_compiler.sequences.collatz.temporal_weighted_right_execution import (
    consume_weighted_right_run,
)
from number_compiler.sequences.collatz.terminal_run_execution import (
    consume_terminal_power_two,
)

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.innovation_input_tape import (
        ParityProgramBuilder,
    )
    from number_compiler.sequences.collatz.temporal_run_result import (
        CollatzTemporalRunQuotient,
    )


def _consume_diagonal_source_window(
    control: CollatzRunControl,
    *,
    seed: int,
    ledger: ResourceLedger,
    scratch: RunArithmeticWorkspace,
    macros: CollatzDyadicMacros | None,
    width_spine: CollatzWidthSpineAccumulator,
    joint_builder: CollatzJointTemporalBuilder,
    parity_builder: ParityProgramBuilder | None,
) -> bool:
    """Consume one bounded source-seamed action before repeated D8 work."""
    from number_compiler.sequences.collatz.diagonal_source_window import (
        CollatzDiagonalWindow,
        source_window_checkpoint_steps,
    )

    if (
        control.remaining < 64
        or control.current.bit_length() < 32
        or control.include_innovation_tape
        and parity_builder is None
        or control.include_innovation_tape
        and control.first_boundary_stamp is None
    ):
        return False
    source = control.current

    def record_window_step() -> None:
        ledger.bump(_collatz_keys.COLLATZ_HASHLIFE_PRIMITIVE_STEPS)
        ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_NTH_DIAGONAL_PRODUCER_STEPS)

    def record_window_work(operand_bits: int) -> None:
        ledger.bump(
            _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_NTH_DIAGONAL_PRODUCER_OPERAND_BITS,
            operand_bits,
        )

    window = CollatzDiagonalWindow.from_source_window(
        source,
        control.remaining,
        max_normalized=256,
        retain_parity_mask=parity_builder is not None,
        retain_field_action=(
            control.joint_requested or control.normalized_f5 is not None
        ),
        prefix_steps=(
            source_window_checkpoint_steps(control.normalized, 256)
            if macros is not None
            else ()
        ),
        record_step=record_window_step,
        reserve_bits=scratch.require_bits,
        record_work=record_window_work,
    )
    window.require_issued()
    if window.action.steps < 32:
        return False

    field_action = (
        window.require_field_action()
        if control.joint_requested or control.normalized_f5 is not None
        else None
    )
    if macros is not None:
        previous_source = source
        previous_steps = 0
        previous_ones = 0
        for prefix in window.prefixes:
            macros.observe(
                previous_source,
                prefix.action.steps - previous_steps,
                prefix.odd_symbols - previous_ones,
                prefix.normalized_endpoint,
                anchor=seed,
            )
            previous_source = prefix.normalized_endpoint
            previous_steps = prefix.action.steps
            previous_ones = prefix.odd_symbols
        if previous_steps < window.action.steps:
            macros.observe(
                previous_source,
                window.action.steps - previous_steps,
                window.odd_symbols - previous_ones,
                window.normalized_endpoint,
                anchor=seed,
            )

    if parity_builder is not None:
        parity_builder.append_diagonal_window(
            window,
            reserve_bits=scratch.require_bits,
            max_width=512,
        )
    if control.joint_requested:
        if field_action is None:
            raise AssertionError("joint carry demand did not retain its field action")
        joint_builder.require_steps(source, window.action.steps)
        joint_builder.append(
            field_action,
            source,
            window.odd_symbols,
            window.normalized_endpoint,
            cache=False,
        )
    if control.normalized_f5 is not None:
        if control.physical_f5 is None or field_action is None:
            raise AssertionError("physical F5 action was not provisioned")
        projection = project_dyadic_fields_f5(field_action)
        control.normalized_f5 = control.normalized_f5.then(projection)
        control.physical_f5 = control.physical_f5.then(projection)
        if window.phase:
            control.physical_f5 = control.physical_f5.then(ODD_HALF_F5)

    control.current = window.physical_endpoint
    control.remaining -= window.physical_ticks
    control.normalized += window.action.steps
    control.division_ticks += window.action.steps
    control.odd_ticks += window.odd_symbols + window.phase
    control.one_symbols += window.odd_symbols
    control.zero_symbols += window.action.steps - window.odd_symbols
    control.phase = window.phase
    control.pending_normalized_source = (
        window.normalized_endpoint if window.phase else None
    )
    control.weighted_binding = None
    control.weighted_cursor_source = None
    control.run_actions += 1
    control.unified_skew_retry = True
    if macros is not None:
        # The source-window producer already published every aligned prefix,
        # including its final endpoint. Move the publication cursor with the
        # committed action so the next loop cannot replay the cumulative span
        # as a second root-prefix observation.
        control.restart_width_segment(width_spine)
    ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_NTH_DIAGONAL_SOURCE_WINDOWS)
    ledger.bump(
        _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_NTH_DIAGONAL_CERTIFIED_SYMBOLS,
        window.action.steps,
    )
    return True


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
    prefer_source_closed_d8: bool,
    macros: CollatzDyadicMacros | None,
    scratch: RunArithmeticWorkspace,
    joint_builder: CollatzJointTemporalBuilder,
    parity_builder: ParityProgramBuilder | None,
    boundary_templates: BoundaryActionTemplateMemo,
) -> CollatzTemporalRunQuotient:
    """Run the production source selector and finalize its admitted result."""
    control_bits = prepare_run_control(seed, physical_ticks, scratch)
    ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_RUN_QUOTIENT_COMPILATIONS)
    control = CollatzRunControl(
        seed=seed,
        physical_ticks=physical_ticks,
        include_innovation_tape=include_innovation_tape,
        joint_requested=include_joint_cocycle,
        current=seed,
        remaining=physical_ticks,
        previous_source=seed,
        unified_skew_retry=not require_mixed_prefix,
        lookup_enabled=macros is not None,
        normalized_f5=CollatzF5AffineAction.identity() if include_f5 else None,
        physical_f5=CollatzF5AffineAction.identity() if include_f5 else None,
    )
    width_spine = CollatzWidthSpineAccumulator(ledger, requested=include_width_spine)
    share_width = temporal_run_share_width(seed, physical_ticks)

    if require_mixed_prefix:
        initial, control.d8_table = consume_initial_mixed_route(
            seed,
            control.remaining,
            control_bits=control_bits,
            templates=boundary_templates,
            ledger=ledger,
            d8_table=control.d8_table,
            include_width=width_spine.complete,
            width_spine=width_spine,
            include_joint=control.joint_requested,
            joint_builder=joint_builder,
            parity_builder=parity_builder,
            macros=macros,
            scratch=scratch,
            normalized_f5=control.normalized_f5,
            physical_f5=control.physical_f5,
        )
        if initial is None:
            raise MixedRouteNotAdmitted
        control.apply_boundary(initial, None)

    while control.remaining:
        scratch.require_bits(8 * (control.current.bit_length() + 4 * control_bits + 16))
        observe_temporal_run_prefix(
            macros,
            width_spine,
            previous_source=control.previous_source,
            previous_width=control.previous_width,
            previous_ones=control.previous_ones,
            current=control.current,
            normalized=control.normalized,
            one_symbols=control.one_symbols,
            anchor=seed,
            share_width=share_width,
        )
        control.previous_source, control.previous_width, control.previous_ones = (
            control.current,
            control.normalized,
            control.one_symbols,
        )
        cycle = pump_normalized_one_cycle(
            control.snapshot(),
            ledger=ledger,
            width_spine=width_spine,
            include_joint=control.joint_requested,
            joint_builder=joint_builder,
            parity_builder=parity_builder,
        )
        if cycle is not None:
            state, repetitions = cycle
            (
                control.current,
                control.remaining,
                control.normalized,
                control.division_ticks,
                control.odd_ticks,
                control.one_symbols,
                control.zero_symbols,
                control.run_actions,
                control.normalized_f5,
                control.physical_f5,
            ) = state
            control.cycle_repetitions += repetitions
            if repetitions:
                control.unified_skew_retry = True
            if not control.remaining:
                break

        if macros is not None and control.remaining >= 16:
            cached_state = consume_cached_mixed_state(
                control.snapshot(),
                ledger=ledger,
                include_width=width_spine.complete,
                width_spine=width_spine,
                include_joint=control.joint_requested,
                joint_builder=joint_builder,
                parity_builder=parity_builder,
                macros=macros,
                scratch=scratch,
            )
            if cached_state is not None:
                control.apply_boundary(cached_state, None, rearm_unified=True)
                continue

        cached_state, control.lookup_enabled = try_consume_cached_dyadic_action(
            control.snapshot(),
            control.lookup_enabled,
            ledger=ledger,
            macros=macros,
            scratch=scratch,
            include_innovation_tape=include_innovation_tape,
            include_width_spine=include_width_spine,
            width_spine=width_spine,
            include_joint_cocycle=control.joint_requested,
            joint_builder=joint_builder,
        )
        if cached_state is not None:
            control.apply_boundary(cached_state, None, rearm_unified=True)
            continue

        if control.current & 1 and control.remaining >= 5:
            terminal = consume_terminal_power_two(
                control.current,
                control.remaining,
                normalized=control.normalized,
                division_ticks=control.division_ticks,
                odd_ticks=control.odd_ticks,
                one_symbols=control.one_symbols,
                zero_symbols=control.zero_symbols,
                run_actions=control.run_actions,
                normalized_f5=control.normalized_f5,
                physical_f5=control.physical_f5,
                ledger=ledger,
                scratch=scratch,
                control_bits=control_bits,
                include_joint=control.joint_requested,
                width_spine=width_spine,
                joint_builder=joint_builder,
                parity_builder=parity_builder,
            )
            if terminal is not None:
                macro = terminal.macro
                control.current = macro.endpoint
                control.remaining = terminal.remaining
                control.normalized = terminal.normalized
                control.division_ticks = terminal.division_ticks
                control.odd_ticks = terminal.odd_ticks
                control.one_symbols = terminal.one_symbols
                control.zero_symbols = terminal.zero_symbols
                control.run_actions = terminal.run_actions
                control.normalized_f5 = terminal.normalized_f5
                control.physical_f5 = terminal.physical_f5
                control.unified_skew_retry = True
                continue

        if try_consume_joint_harmonic_band(
            control,
            seed=seed,
            control_bits=control_bits,
            ledger=ledger,
            scratch=scratch,
            width_spine=width_spine,
            joint_builder=joint_builder,
            parity_builder=parity_builder,
            macros=macros,
            require_mixed_prefix=require_mixed_prefix,
        ):
            continue

        # The root consumer may request an exact bounded source-window cut.
        # Cached parents and terminal powers were already offered above.
        # Only after a negative registered-parent check can endpoint/joint
        # demand skip speculative named/mixed discovery. The D8 row and any
        # retained joint carry action remain source-certified, and the next
        # iteration rechecks all named macro guards at its new source.
        # Width and independent F5 consumers keep their prior route. A
        # complete innovation demand may use the same window only after its
        # first authenticated boundary witness has been retained.
        observed_leading_run: tuple[int, int, int] | None = None
        if (
            prefer_source_closed_d8
            and (
                not include_f5 or control.joint_requested or parity_builder is not None
            )
            and not include_width_spine
            and (not include_innovation_tape or parity_builder is not None)
            and (
                not include_innovation_tape or control.first_boundary_stamp is not None
            )
            and not require_mixed_prefix
            and control.remaining >= 64
            and control.current.bit_length() >= 32
            and (control.current & 255) not in (0, 255)
        ):
            observed_leading_run = leading_homogeneous_run(
                control.current, control.remaining
            )
            _, _, run_symbols = observed_leading_run
            if run_symbols < 8 and _consume_diagonal_source_window(
                control,
                seed=seed,
                ledger=ledger,
                scratch=scratch,
                macros=macros,
                width_spine=width_spine,
                joint_builder=joint_builder,
                parity_builder=parity_builder,
            ):
                continue

            # A positive catalog probe is only candidate presence. Cached
            # issued actions and terminal powers have already been consumed
            # above, so it must not veto an independently exact finite source
            # window. Retain the old negative-probe condition for the D8
            # fallback, whose admission still depends on that route.
            if (
                not has_unified_source_parent(control.current, control.remaining)
                and not include_innovation_tape
                and run_symbols < 8
                and consume_d8_run_section(
                    control,
                    seed=seed,
                    low=control.current & 255,
                    homogeneous_symbols=run_symbols,
                    control_bits=control_bits,
                    include_innovation_tape=False,
                    include_joint_cocycle=control.joint_requested,
                    include_width_spine=False,
                    ledger=ledger,
                    scratch=scratch,
                    width_spine=width_spine,
                    joint_builder=joint_builder,
                    parity_builder=None,
                    macros=macros,
                )
            ):
                ledger.bump(
                    _collatz_keys.COLLATZ_PHYSICAL_TEMPORAL_NTH_SOURCE_PUNCTURE_D8_CUTS
                )
                continue

        # Demand a source-certified weighted right transition before speculative
        # border discovery, but only when it replaces a long admitted run.
        if consume_weighted_right_run(
            control,
            seed=seed,
            ledger=ledger,
            scratch=scratch,
            control_bits=control_bits,
            templates=boundary_templates,
            width_spine=width_spine,
            joint_builder=joint_builder,
            parity_builder=parity_builder,
            macros=macros,
        ):
            continue

        if observed_leading_run is None:
            observed_leading_run = leading_homogeneous_run(
                control.current, control.remaining
            )
        low, available, homogeneous_symbols = observed_leading_run
        homogeneous_prefix = homogeneous_symbols >= 8

        # Avoid crossing a fresh root checkpoint before its complete cylinder.
        defer_for_root_checkpoint = defer_unified_skew_reentry_for_root_checkpoint(
            macros,
            share_width,
            control.normalized,
            include_joint=control.joint_requested,
            include_innovation=include_innovation_tape,
            width_complete=width_spine.complete,
        )
        reentry = None
        if not defer_for_root_checkpoint:
            control.unified_skew_retry, reentry = attempt_unified_skew_reentry(
                seed,
                control.current,
                control.remaining,
                physical_ticks,
                retry=control.unified_skew_retry,
                require_mixed_prefix=require_mixed_prefix,
                homogeneous_prefix=homogeneous_prefix,
                normalized=control.normalized,
                division_ticks=control.division_ticks,
                odd_ticks=control.odd_ticks,
                one_symbols=control.one_symbols,
                zero_symbols=control.zero_symbols,
                run_actions=control.run_actions,
                control_bits=control_bits,
                templates=boundary_templates,
                ledger=ledger,
                scratch=scratch,
                include_joint=control.joint_requested,
                width_spine=width_spine,
                joint_builder=joint_builder,
                parity_builder=parity_builder,
                normalized_f5=control.normalized_f5,
                physical_f5=control.physical_f5,
                macros=macros,
                include_quadratic_clock=include_innovation_tape,
            )
        if reentry is not None:
            state, chain, global_offset, witness = reentry
            control.apply_boundary(state, witness, boundary_offset=global_offset)
            # Do not label a later-source chain as the root-prefix chain.
            if chain.source == seed:
                control.unified_skew_chain = chain
            control.unified_skew_retry = True
            continue

        new_state = try_consume_conditional_route(
            control.snapshot(),
            require_mixed_prefix=require_mixed_prefix,
            homogeneous_prefix=homogeneous_prefix,
            deferred_for_root_checkpoint=defer_for_root_checkpoint,
            include_width_spine=include_width_spine,
            include_innovation_tape=include_innovation_tape,
            parity_route_requested=parity_builder is not None,
            source=control.current,
            remaining_ticks=control.remaining,
            scratch=scratch,
            control_bits=control_bits,
            include_joint=control.joint_requested,
            joint_builder=joint_builder,
            ledger=ledger,
            macros=macros,
        )
        if new_state is not None:
            control.apply_boundary(new_state, None, rearm_unified=True)
            continue

        border_state, border = None, None
        # Rebasing a root-relative D8 fiber would rematerialize its high fiber.
        root_d8_batch_admitted = d8_root_batch_admitted(
            control.current, control.remaining
        )
        boundary_plan = admit_physical_boundary_plan(
            control.current, control.remaining, ledger
        )
        if not homogeneous_prefix and not root_d8_batch_admitted:
            border_state, border = consume_border_return(
                control.snapshot(),
                seed=seed,
                ledger=ledger,
                scratch=scratch,
                control_bits=control_bits,
                include_joint=control.joint_requested,
                width_spine=width_spine,
                joint_builder=joint_builder,
                parity_builder=parity_builder,
                macros=macros,
                minimum_useful_physical_ticks=minimum_useful_border_extent(
                    boundary_plan
                ),
            )
        if border_state is not None and border is not None:
            control.apply_boundary(border_state, border)
            width_spine.reset_segment()
            control.lookup_enabled = macros is not None
            continue

        # Partial requests fall back to exact runs when the guard does not fit.
        if (
            boundary_plan is not None
            and boundary_plan.identity == ENTRY_89_AT_NINE
            and not include_innovation_tape
            and not control.joint_requested
        ):
            boundary_plan = None
        selected_mixed = None
        if (
            not defer_for_root_checkpoint
            and boundary_plan is not None
            and boundary_plan.physical_ticks < control.remaining
            and control.remaining >= 128
            and control.current.bit_length() >= 64
            and not homogeneous_prefix
        ):
            ledger.bump(_collatz_keys.COLLATZ_PHYSICAL_BOUNDARY_COMPARISON_ATTEMPTS)
            selected_mixed, control.d8_table = select_mixed_macro(
                control.current,
                control.remaining,
                templates=boundary_templates,
                ledger=ledger,
                d8_table=control.d8_table,
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
            boundary_state, named_boundary, control.lookup_enabled = (
                consume_named_boundary(
                    control.snapshot(),
                    boundary_plan,
                    seed=seed,
                    ledger=ledger,
                    scratch=scratch,
                    control_bits=control_bits,
                    templates=boundary_templates,
                    include_joint=control.joint_requested,
                    width_spine=width_spine,
                    joint_builder=joint_builder,
                    parity_builder=parity_builder,
                    macros=macros,
                    prior_lookup_enabled=control.lookup_enabled,
                )
            )
            control.apply_boundary(boundary_state, named_boundary)
            continue

        # Use mixed discovery only where its bounded preview can replace work.
        if not defer_for_root_checkpoint and (
            selected_mixed is not None
            or (
                not homogeneous_prefix
                and control.remaining >= 128
                and control.current.bit_length() >= 64
            )
        ):
            progress, control.d8_table = select_and_consume_mixed_run(
                control.current,
                control.remaining,
                selected=selected_mixed,
                templates=boundary_templates,
                ledger=ledger,
                d8_table=control.d8_table,
                include_width=width_spine.complete,
                width_spine=width_spine,
                include_joint=control.joint_requested,
                joint_builder=joint_builder,
                parity_builder=parity_builder,
                macros=macros,
                scratch=scratch,
                normalized_f5=control.normalized_f5,
                physical_f5=control.physical_f5,
                normalized=control.normalized,
                division_ticks=control.division_ticks,
                odd_ticks=control.odd_ticks,
                one_symbols=control.one_symbols,
                zero_symbols=control.zero_symbols,
                run_actions=control.run_actions,
            )
            if progress is not None:
                (
                    control.current,
                    control.remaining,
                    control.normalized,
                    control.division_ticks,
                    control.odd_ticks,
                ) = (
                    progress.current,
                    progress.remaining,
                    progress.normalized,
                    progress.division_ticks,
                    progress.odd_ticks,
                )
                control.one_symbols, control.zero_symbols = (
                    progress.one_symbols,
                    progress.zero_symbols,
                )
                control.run_actions = progress.run_actions
                control.normalized_f5 = progress.application.normalized_f5
                control.physical_f5 = progress.application.physical_f5
                control.unified_skew_retry = True
                (
                    control.previous_source,
                    control.previous_width,
                    control.previous_ones,
                ) = (
                    control.current,
                    control.normalized,
                    control.one_symbols,
                )
                continue

        if consume_d8_run_section(
            control,
            seed=seed,
            low=low,
            homogeneous_symbols=homogeneous_symbols,
            control_bits=control_bits,
            include_innovation_tape=include_innovation_tape,
            include_joint_cocycle=control.joint_requested,
            include_width_spine=include_width_spine,
            ledger=ledger,
            scratch=scratch,
            width_spine=width_spine,
            joint_builder=joint_builder,
            parity_builder=parity_builder,
            macros=macros,
        ):
            continue

        consume_homogeneous_run(
            control,
            seed=seed,
            available=available,
            control_bits=control_bits,
            include_joint_cocycle=control.joint_requested,
            ledger=ledger,
            scratch=scratch,
            width_spine=width_spine,
            joint_builder=joint_builder,
            parity_builder=parity_builder,
            macros=macros,
        )

    return finalize_collatz_temporal_run(
        seed=seed,
        physical_ticks=physical_ticks,
        current=control.current,
        phase=control.phase,
        ledger=ledger,
        macros=macros,
        previous_source=control.previous_source,
        previous_width=control.previous_width,
        previous_ones=control.previous_ones,
        normalized=control.normalized,
        one_symbols=control.one_symbols,
        share_width=share_width,
        width_spine=width_spine,
        division_ticks=control.division_ticks,
        odd_ticks=control.odd_ticks,
        run_actions=control.run_actions,
        include_joint_cocycle=control.joint_requested,
        joint_builder=joint_builder,
        parity_builder=parity_builder,
        innovation_modulus=innovation_modulus,
        pending_normalized_source=control.pending_normalized_source,
        zero_symbols=control.zero_symbols,
        cycle_repetitions=control.cycle_repetitions,
        normalized_f5=control.normalized_f5,
        physical_f5=control.physical_f5,
        first_boundary_stamp=control.first_boundary_stamp,
        first_boundary_macro=control.first_boundary_macro,
        unified_skew_chain=control.unified_skew_chain,
    )
