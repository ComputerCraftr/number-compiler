"""Source-bound Collatz temporal quotient by maximal parity runs.

The normalized map uses ``H0(x)=x/2`` and ``H1(x)=(3*x+1)/2``. Exact
2-adic valuations select maximal zero and one runs, which are applied with
closed affine powers. Mixed wide sources use an accounted finite D8
source-section transducer; they do not construct a global parity itinerary or
physical branch tree. The pinned ``1 -> 4 -> 2 -> 1`` cycle is source-bound
and powered. Optional F5 views remain observations, never branch authority;
their root-fiber algebra does not replace exact source authentication.
"""

from __future__ import annotations

from contextlib import nullcontext

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.fields.blank_ledger import BlankLedger
from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.boundary_macro_prefixes import (
    _publish_boundary_macro_prefixes,
)
from number_compiler.sequences.collatz.boundary_macros import (
    BoundaryActionTemplateMemo,
    admit_boundary_macro_plan,
    select_admitted_boundary_macro,
)
from number_compiler.sequences.collatz.joint_temporal_action import (
    CollatzJointTemporalBuilder,
)
from number_compiler.sequences.collatz.run_prefix_checkpoints import (
    _crosses_root_checkpoint,
    _publish_d8_root_checkpoints,
    _publish_run_root_checkpoints,
)
from number_compiler.sequences.collatz.tape_width import (
    CollatzWidthSpineAccumulator,
    charge_width_repeat,
)
from number_compiler.sequences.collatz.temporal_dyadic import (
    D8CylinderFrame,
    D8TemporalTable,
)
from number_compiler.sequences.collatz.temporal_f5_observer import (
    _CYCLE_F5,
    F5_AFFINE_ALPHABET,
    HENSEL_ONE_F5,
    HENSEL_ZERO_F5,
    ODD_HALF_F5,
    CollatzAnonymousF5Fiber,
    CollatzF5AffineAction,
    CollatzPoweredRootVietaProgram,
    CollatzRootFiberCertificate,
    _append_dyadic_f5,
    _run_one_f5,
    _run_zero_f5,
    root_fiber_certificate,
)
from number_compiler.sequences.collatz.temporal_run_result import (
    CollatzTemporalRunQuotient,
)

_MAX_CYLINDER_BATCH_SYMBOLS = 64
_MIN_CYLINDER_SOURCE_BITS = 131_072


def _bounded_run_length(residue: int) -> int:
    """Enough low-bit precision to choose between D8 and a homogeneous run."""
    if residue & 1:
        return v2_positive(residue + 1)
    return 8 if residue == 0 else v2_positive(residue)


def compile_collatz_temporal_run_quotient(
    seed: int,
    physical_ticks: int,
    *,
    ledger: ResourceLedger,
    include_f5: bool = False,
    shared_cache: bool = False,
    include_width_spine: bool = False,
    include_joint_cocycle: bool = False,
    include_innovation_tape: bool = False,
) -> CollatzTemporalRunQuotient:
    """Compile the exact source-bound action without a parity itinerary.

    Work uses maximal runs, finite D8 sections and the powered known cycle.
    It retains no physical successor leaf or global parity word. Run count can
    grow with requested ticks; arithmetic cost depends on operand widths.
    """
    if type(seed) is not int or seed <= 0:
        raise ValueError("Collatz temporal quotient requires a positive seed")
    if type(physical_ticks) is not int or physical_ticks < 0:
        raise ValueError("Collatz temporal quotient requires nonnegative ticks")
    if type(ledger) is not ResourceLedger:
        raise TypeError("Collatz temporal quotient requires its resource ledger")

    if type(include_f5) is not bool:
        raise TypeError("F5 projection selection must be Boolean")
    if type(shared_cache) is not bool:
        raise TypeError("shared cache flag must be Boolean")
    if type(include_width_spine) is not bool:
        raise TypeError("width-spine demand must be Boolean")
    if type(include_joint_cocycle) is not bool:
        raise TypeError("joint-cocycle demand must be Boolean")
    if type(include_innovation_tape) is not bool:
        raise TypeError("innovation-tape demand must be Boolean")
    from number_compiler.sequences.collatz.source_cylinder_cache import (
        CollatzDyadicMacros,
    )

    macros = (
        CollatzDyadicMacros(ledger, shared_cache=True)
        if shared_cache and seed.bit_length() >= 64
        else None
    )
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "collatz_physical")
    try:
        joint_builder = CollatzJointTemporalBuilder(
            ledger,
            scratch,
            seed,
            requested=include_joint_cocycle,
            shared_cache=shared_cache,
        )
    except BaseException as error:
        if macros is not None:
            macros.__exit__(type(error), error, error.__traceback__)
        raise
    with (
        scratch.scope(),
        macros if macros is not None else nullcontext(),
        joint_builder,
        BoundaryActionTemplateMemo(ledger) as boundary_templates,
    ):
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
        width_spine = CollatzWidthSpineAccumulator(
            ledger, requested=include_width_spine
        )
        first_boundary: tuple[int, int, int, str] | None = None
        first_boundary_macro = None
        d8_table: D8TemporalTable | None = None
        lookup_enabled = macros is not None
        previous_source, previous_width, previous_ones = seed, 0, 0
        share_width = 1 << (
            min(max(8, seed.bit_length()), max(8, physical_ticks // 2)).bit_length() - 1
        )
        discovery_before = ledger.counters.get(
            "collatz_physical_temporal_d8_discovery_symbols", 0
        )

        while remaining:
            scratch.require_bits(8 * (current.bit_length() + 4 * control_bits + 16))
            if macros is not None and previous_width < normalized <= share_width:
                macros.observe(
                    previous_source,
                    normalized - previous_width,
                    one_symbols - previous_ones,
                    current,
                    anchor=seed,
                    tape_width_summary=width_spine.segment_summary(
                        previous_source.bit_length(),
                        current.bit_length(),
                        normalized - previous_width,
                        one_symbols - previous_ones,
                    ),
                )
                width_spine.reset_segment()
            previous_source, previous_width, previous_ones = (
                current,
                normalized,
                one_symbols,
            )
            if current == 1 and remaining >= 3:
                repetitions, tail = divmod(remaining, 3)
                if repetitions:
                    cycle_source = current
                    if include_joint_cocycle:
                        joint_builder.append_cycle(cycle_source, repetitions)
                    cycle_repetitions += repetitions
                    odd_ticks += repetitions
                    division_ticks += 2 * repetitions
                    normalized += 2 * repetitions
                    one_symbols += repetitions
                    zero_symbols += repetitions
                    run_actions += 1
                    if normalized_f5 is not None and physical_f5 is not None:
                        cycle_f5 = _CYCLE_F5.power(repetitions)
                        normalized_f5 = normalized_f5.then(cycle_f5)
                        physical_f5 = physical_f5.then(cycle_f5)
                    if width_spine.complete:
                        cycle_blank = BlankLedger(0, 0, 2)
                        charge_width_repeat(ledger, cycle_blank, repetitions)
                        width_spine.record(cycle_blank.repeat(repetitions))
                    remaining = tail
                    ledger.bump("collatz_physical_temporal_cycle_pump_requests")
                    ledger.bump(
                        "collatz_physical_temporal_cycle_pump_repetitions", repetitions
                    )
                    if not remaining:
                        break

            if (
                lookup_enabled
                and macros is not None
                and remaining >= 16
                and current.bit_length() >= 64
                and _bounded_run_length(current & 255) < 8
                and not include_innovation_tape
            ):
                # A normalized symbol costs at least one physical tick. Admit
                # the exact retained odd count before applying a cached block.
                # Endpoint >2 proves no earlier normalized cycle entry.
                limit = min(remaining, max(8, current.bit_length()))
                width = 1 << (limit.bit_length() - 1)
                scratch.require_bits(16 * (current.bit_length() + 2 * width + 32))
                joint_record = None
                endpoint = 0
                if include_joint_cocycle:
                    paired = joint_builder.lookup_largest_macro(
                        macros,
                        current,
                        width,
                        remaining,
                        include_width=include_width_spine and width_spine.complete,
                    )
                    if paired is None:
                        cell = None
                        macro_width = None
                        endpoint = 0
                        lookup_enabled = False
                    else:
                        cell, joint_record, macro_width, endpoint = paired
                elif include_width_spine and width_spine.complete:
                    selected_with_width = macros.lookup_largest_with_width(
                        current, width, remaining
                    )
                    if selected_with_width is None:
                        cell = None
                        macro_width = None
                        lookup_enabled = False
                    else:
                        cell, macro_width = selected_with_width
                else:
                    cell = macros.lookup_largest(current, width, remaining)
                    macro_width = None
                    if cell is None:
                        lookup_enabled = False
                if cell is not None and endpoint == 0:
                    endpoint = cell.apply(current)
                if (
                    cell is not None
                    and endpoint > 2
                    and not (include_width_spine and macro_width is None)
                ):
                    width = cell.width
                    if joint_record is not None:
                        joint_builder.append(
                            joint_record[0], current, joint_record[1], endpoint
                        )
                        joint_builder.applied_cached_macro()
                    # Consume at most one retained occurrence per query route;
                    # subsequent discovery may publish bounded interior joins.
                    lookup_enabled = False
                    if normalized_f5 is not None and physical_f5 is not None:
                        # Every admitted width is dyadic and >=8, hence a
                        # multiple of four: 2**width == 1 in F5. Both the
                        # centered gain and translated offset need no division.
                        normalized_f5, physical_f5 = _append_dyadic_f5(
                            normalized_f5,
                            physical_f5,
                            cell.multiplier,
                            cell.target_origin,
                            cell.residue,
                        )
                    if include_width_spine and width_spine.complete:
                        if macro_width is None:
                            width_spine.invalidate()
                        else:
                            if (
                                macro_width.source_width != current.bit_length()
                                or macro_width.normalized_symbols != width
                                or macro_width.odd_steps != cell.odd_symbols
                                or macro_width.physical_ticks
                                != width + cell.odd_symbols
                                or macro_width.target_width != endpoint.bit_length()
                            ):
                                raise ValueError(
                                    "cached Collatz width spine differs from macro"
                                )
                            width_spine.record(macro_width.blank)
                    current = endpoint
                    odd_ticks += cell.odd_symbols
                    division_ticks += width
                    normalized += width
                    one_symbols += cell.odd_symbols
                    zero_symbols += width - cell.odd_symbols
                    remaining -= width + cell.odd_symbols
                    macros.applied()
                    run_actions += 1
                    ledger.bump(
                        "collatz_physical_temporal_run_operand_bits",
                        cell.multiplier.bit_length()
                        + endpoint.bit_length()
                        + cell.residue.bit_length(),
                    )
                    continue

            # Build a guarded boundary action only after an admitted cached
            # occurrence has had the chance to satisfy this exact source. The
            # macro includes its completing physical half-step, so partial
            # requests retain the exact run executor when the guard does not fit.
            boundary_plan = admit_boundary_macro_plan(current, remaining)
            ledger.bump("collatz_physical_boundary_plan_checks")
            ledger.bump(
                "collatz_physical_boundary_plan_operand_bits",
                current.bit_length() + remaining.bit_length(),
            )
            if (
                boundary_plan is not None
                and boundary_plan.family == "989"
                and not include_innovation_tape
                and not include_joint_cocycle
            ):
                # This is already an ordinary maximal odd run. Keep the
                # observer-specific certificate out of unrequested work.
                boundary_plan = None
            if boundary_plan is not None:
                family = boundary_plan.family
                repetitions = boundary_plan.repetitions
                normalized_steps = (
                    2 * repetitions + 1
                    if family in ("421", "4721")
                    else repetitions + 2
                    if family == "630"
                    else repetitions
                )
                scratch.require_bits(
                    8
                    * (
                        current.bit_length()
                        + 4 * normalized_steps
                        + 4 * control_bits
                        + 32
                    )
                )
                boundary = select_admitted_boundary_macro(
                    boundary_plan, templates=boundary_templates
                )
                if (
                    boundary is None
                    or boundary.family != family
                    or boundary.repetitions != repetitions
                    or boundary.normalized_symbols != normalized_steps
                ):
                    raise AssertionError("Collatz boundary changed after admission")
                before = current
                if first_boundary is None and include_innovation_tape:
                    first_boundary = (
                        physical_ticks - remaining,
                        before,
                        boundary.physical_ticks,
                        boundary.family,
                    )
                    first_boundary_macro = boundary
                if include_joint_cocycle:
                    joint_builder.require_steps(before, boundary.normalized_symbols)
                    joint_builder.append(
                        boundary.fields,
                        before,
                        boundary.odd_symbols,
                        boundary.endpoint,
                    )
                if width_spine.complete:
                    width_spine.record(boundary.width_blank)
                if normalized_f5 is not None and physical_f5 is not None:
                    f5 = boundary.f5_action()
                    normalized_f5 = normalized_f5.then(f5)
                    physical_f5 = physical_f5.then(f5)
                current = boundary.endpoint
                remaining -= boundary.physical_ticks
                normalized += boundary.normalized_symbols
                division_ticks += boundary.normalized_symbols
                odd_ticks += boundary.odd_symbols
                one_symbols += boundary.odd_symbols
                zero_symbols += boundary.normalized_symbols - boundary.odd_symbols
                run_actions += 1
                ledger.bump(f"collatz_physical_boundary_{family}_macro_actions")
                ledger.bump(
                    f"collatz_physical_boundary_{family}_macro_repetitions",
                    boundary.repetitions,
                )
                ledger.bump(
                    f"collatz_physical_boundary_{family}_macro_physical_ticks",
                    boundary.physical_ticks,
                )
                ledger.bump(
                    "collatz_physical_temporal_run_operand_bits",
                    before.bit_length()
                    + boundary.endpoint.bit_length()
                    + boundary.fields.gain.bit_length()
                    + boundary.fields.sum_gain.bit_length(),
                )
                if macros is not None:
                    try:
                        _publish_boundary_macro_prefixes(
                            boundary,
                            macros,
                            scratch,
                            anchor=seed,
                            normalized_offset=normalized - boundary.normalized_symbols,
                            odd_offset=one_symbols - boundary.odd_symbols,
                        )
                        lookup_enabled = True
                    except BlockContextBudgetExceeded:
                        # The exact macro has already advanced the source.
                        # Prefix publication is an optional future-cache aid.
                        macros.frontier.clear()
                        lookup_enabled = False
                        ledger.bump("collatz_boundary_prefix_budget_bypasses")
                    previous_source, previous_width, previous_ones = (
                        current,
                        normalized,
                        one_symbols,
                    )
                width_spine.reset_segment()
                continue

            low = current & 255
            available = _bounded_run_length(low)
            homogeneous_symbols = min(
                available, remaining // 2 if low & 1 else remaining
            )
            if remaining >= 8 and homogeneous_symbols < 8:
                scratch.require_bits(8 * (current.bit_length() + 4 * control_bits + 32))
                if d8_table is None:
                    d8_table = D8TemporalTable.for_ledger(ledger)
                if not include_joint_cocycle and (
                    current.bit_length() <= _MIN_CYLINDER_SOURCE_BITS or remaining < 32
                ):
                    # Ordinary small exact states retain the cheaper direct
                    # finite row. A joint demand uses the framed batch path so
                    # completed D8 rows can be composed and admitted together.
                    d8_frame = (
                        D8CylinderFrame(current)
                        if include_joint_cocycle
                        or (include_width_spine and width_spine.complete)
                        else None
                    )
                    d8_action = None
                    d8_width_summary = None
                    if include_joint_cocycle:
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
                            if include_width_spine and width_spine.complete:
                                d8_endpoint = advanced.materialize()
                                ledger.bump(
                                    "collatz_physical_temporal_d8_frame_materializations"
                                )
                            else:
                                d8_endpoint = target_origin + 3**ones * (current >> 8)
                            ledger.bump(
                                "collatz_physical_temporal_d8_endpoint_evaluations"
                            )
                            survives = d8_endpoint > 2
                        ledger.bump(
                            "collatz_physical_temporal_run_operand_bits",
                            current.bit_length()
                            + (
                                d8_endpoint.bit_length()
                                if d8_endpoint is not None
                                else 0
                            )
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
                                    raise AssertionError(
                                        "joint D8 action was not selected"
                                    )
                                joint_builder.begin_d8_batch(current)
                                joint_builder.append_d8_transition(
                                    d8_action, ones, current & 255
                                )
                                current = joint_builder.finish_d8_batch(
                                    macros, advanced
                                )
                            else:
                                if d8_endpoint is None:
                                    raise AssertionError(
                                        "D8 endpoint was not evaluated"
                                    )
                                current = d8_endpoint
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
                    # This bounded cursor consumes source windows, not a sequence
                    # of full intermediate integer endpoints. After the source
                    # tail is exhausted, the ordinary exact run owner resumes.
                    while (
                        remaining >= 8
                        and frame.consumed < _MAX_CYLINDER_BATCH_SYMBOLS
                        and frame.consumed < frame.source.bit_length()
                    ):
                        block_frame = frame
                        block_normalized_offset = normalized
                        block_odd_offset = one_symbols
                        frame_bits = max(
                            frame.origin.bit_length(), frame.gain.bit_length()
                        )
                        scratch.require_bits(
                            8
                            * (
                                current.bit_length()
                                + frame_bits
                                + 4 * control_bits
                                + 48
                            )
                        )
                        local = frame.local_word()
                        residue = local & 255
                        ledger.bump(
                            "collatz_physical_temporal_d8_frame_operand_bits",
                            local.bit_length() + frame.gain.bit_length(),
                        )
                        capped = _bounded_run_length(residue)
                        homogeneous = min(
                            capped, remaining // 2 if residue & 1 else remaining
                        )
                        if homogeneous >= 8:
                            break
                        d8_width_summary = None
                        d8_action = None
                        if include_joint_cocycle:
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
                            advanced, ones, residue, target_origin = (
                                d8_table.transition(frame)
                            )
                        if remaining < 8 + ones:
                            break
                        # Normalized dynamics remain in {1, 2} after first hitting
                        # 1. Preserve the earliest physical cycle entry for the
                        # scheduler's bounded support/audit prefix by letting the
                        # existing runs reach that boundary.
                        if advanced.source.bit_length() <= advanced.consumed + 2:
                            ledger.bump(
                                "collatz_physical_temporal_d8_endpoint_evaluations"
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
                            # These materializations occur only at O(log horizon)
                            # root checkpoints, not at every D8 source section.
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
                        if not include_joint_cocycle:
                            ledger.bump(
                                "collatz_physical_temporal_d8_frame_materializations"
                            )
                            ledger.bump(
                                "collatz_physical_temporal_d8_endpoint_evaluations"
                            )
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

            if low in (0, 255):
                available = v2_positive(current + 1 if current & 1 else current)

            if current & 1 == 0:
                length = min(available, remaining)
                run_source = current
                run_offset = normalized
                run_odd_offset = one_symbols
                before_bits = current.bit_length()
                joint_source = current
                if include_joint_cocycle:
                    joint_builder.append_run(joint_source, length, odd=False)
                current >>= length
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
                power3 = 3**complete
                current = power3 * ((current + 1) >> complete) - 1
                if width_spine.complete:
                    displacement = current.bit_length() - before_bits
                    # Every normalized odd boundary grows monotonically; the
                    # raw 3*x+1 cell is at most one bit above the final
                    # normalized boundary of this maximal odd run.
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

        if macros is not None:
            if phase == 0 and previous_width < normalized <= share_width:
                macros.observe(
                    previous_source,
                    normalized - previous_width,
                    one_symbols - previous_ones,
                    current,
                    anchor=seed,
                    tape_width_summary=width_spine.segment_summary(
                        previous_source.bit_length(),
                        current.bit_length(),
                        normalized - previous_width,
                        one_symbols - previous_ones,
                    ),
                )
            macros._bump(
                "primitive_steps",
                ledger.counters.get("collatz_physical_temporal_d8_discovery_symbols", 0)
                - discovery_before,
            )
        certificate = None
        ledger.bump("collatz_physical_temporal_run_actions", run_actions)
        ledger.bump("collatz_physical_temporal_normalized_symbols", normalized)
        ledger.bump("collatz_physical_temporal_odd_ticks", odd_ticks)
        ledger.bump("collatz_physical_temporal_division_ticks", division_ticks)
        ledger.bump(
            "collatz_physical_temporal_endpoint_operand_bits", current.bit_length()
        )

        tape_width_summary = width_spine.finish(
            seed.bit_length(),
            current.bit_length(),
            physical_ticks,
            division_ticks,
            odd_ticks,
        )
        joint_action = None
        if include_joint_cocycle:
            normalized_endpoint = current if phase == 0 else (current - 1) // 3
            joint_action = joint_builder.finish(
                seed,
                current,
                normalized_endpoint,
                physical_ticks,
                division_ticks,
                one_symbols,
                phase,
            )

        return CollatzTemporalRunQuotient(
            seed,
            physical_ticks,
            current,
            odd_ticks,
            division_ticks,
            normalized,
            phase,
            run_actions,
            zero_symbols,
            one_symbols,
            cycle_repetitions,
            normalized_f5,
            physical_f5,
            certificate,
            tape_width_summary,
            joint_action,
            first_boundary,
            first_boundary_macro,
        )


__all__ = [
    "F5_AFFINE_ALPHABET",
    "HENSEL_ONE_F5",
    "HENSEL_ZERO_F5",
    "ODD_HALF_F5",
    "CollatzAnonymousF5Fiber",
    "CollatzF5AffineAction",
    "CollatzPoweredRootVietaProgram",
    "CollatzRootFiberCertificate",
    "CollatzTemporalRunQuotient",
    "compile_collatz_temporal_run_quotient",
    "root_fiber_certificate",
]
