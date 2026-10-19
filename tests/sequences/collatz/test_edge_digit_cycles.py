"""Exact production guards for the NC11 physical digit-cycle macros."""

from __future__ import annotations

from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicReturnSourceRecord,
)
from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.border_identity import (
    ENTRY_0563,
    ENTRY_26847_PHASES,
    BoundaryActionIdentity,
)
from number_compiler.sequences.collatz.boundary_macro_prefixes import (
    _publish_boundary_macro_prefixes,
    _slice_action,
)
from number_compiler.sequences.collatz.boundary_macros import (
    admit_routed_boundary_macro_plan,
    boundary_macro_26847_phase,
    select_admitted_boundary_macro,
    select_boundary_macro,
    validate_boundary_macro,
)
from number_compiler.sequences.collatz.physical_boundary_route import (
    has_admitted_boundary_macro,
)
from number_compiler.sequences.collatz.source_cylinder_cache import (
    CollatzDyadicMacros,
)
from number_compiler.sequences.collatz.temporal_run_quotient import (
    compile_collatz_temporal_run_quotient,
)


def _physical_trace(source: int, ticks: int) -> tuple[int, ...]:
    values = [source]
    for _ in range(ticks):
        source = 3 * source + 1 if source & 1 else source // 2
        values.append(source)
    return tuple(values)


def _source_node(source: int) -> DyadicReturnSourceRecord:
    return DyadicReturnSourceRecord(source, 0, 0, None, None, None, 0, True)


def _normalized_trace(source: int, steps: int) -> tuple[int, ...]:
    values = [source]
    for _ in range(steps):
        source = (3 * source + 1) // 2 if source & 1 else source // 2
        values.append(source)
    return tuple(values)


def _assert_cached_prefix(cache: CollatzDyadicMacros, source: int, width: int) -> None:
    cell = cache.lookup(source, width)
    assert cell is not None
    trace = _normalized_trace(source, width)
    assert cell.apply(source) == trace[-1]
    assert cell.odd_symbols == sum(value & 1 for value in trace[:-1])


def _high_fiber_source(identity: BoundaryActionIdentity, repetitions: int) -> int:
    if identity == ENTRY_0563:
        precision = 2 * repetitions + 2
        modulus = 1 << precision
        residue = (-2 + (1 << (2 * repetitions + 1))) % modulus
        source = residue + modulus * (-residue * pow(modulus, -1, 5) % 5)
    else:
        precision = 4 * repetitions + 2
        modulus = 1 << precision
        residue = ((16 + (1 << (4 * repetitions + 1))) * pow(13, -1, modulus)) % modulus
        source = residue + modulus * ((2 - residue) * pow(modulus, -1, 5) % 5)
    return source + (5 << (precision + 80))


def test_phase_zero_edge_actions_preserve_both_clocks_and_width_extrema() -> None:
    cases = (
        (30, 5, ENTRY_0563, 1, 35),
        (30, 9, ENTRY_0563, 2, 80),
        (70, 5, ENTRY_0563, 1, 80),
        (112, 6, ENTRY_26847_PHASES[0], 1, 11),
        (592, 11, ENTRY_26847_PHASES[0], 2, 11),
    )
    for source, ticks, identity, repetitions, endpoint in cases:
        plan = admit_routed_boundary_macro_plan(source, ticks)
        assert plan is not None
        assert (plan.identity, plan.repetitions, plan.physical_ticks) == (
            identity,
            repetitions,
            ticks,
        )
        macro = select_admitted_boundary_macro(plan)
        validate_boundary_macro(macro)
        trace = _physical_trace(source, ticks)
        assert trace[-1] == endpoint == macro.endpoint
        assert macro.normalized_symbols + macro.odd_symbols == ticks
        widths = tuple(value.bit_length() for value in trace)
        assert source.bit_length() + macro.width_blank.minimum == min(widths)
        assert source.bit_length() + macro.width_blank.maximum == max(widths)


def test_one_tick_short_requests_remain_on_exact_fallback() -> None:
    assert admit_routed_boundary_macro_plan(30, 4) is None
    assert admit_routed_boundary_macro_plan(112, 5) is None


def test_single_rotated_return_does_not_preempt_longer_powered_routes() -> None:
    assert admit_routed_boundary_macro_plan(7, 32) is None
    plan = admit_routed_boundary_macro_plan(7, 2)
    assert plan is not None
    assert (plan.identity, plan.repetitions, plan.physical_ticks) == (
        ENTRY_26847_PHASES[4],
        1,
        2,
    )


def test_macro_source_routing_covers_all_twenty_last_digit_classes() -> None:
    for residue in range(20):
        source = 160 * 8 + residue
        plan = admit_routed_boundary_macro_plan(source, 32)
        if plan is None:
            continue
        macro = select_admitted_boundary_macro(plan)
        validate_boundary_macro(macro)
        assert macro.endpoint == _physical_trace(source, macro.physical_ticks)[-1]
        if macro.identity == ENTRY_0563:
            assert source % 40 == 30
        elif (phase := boundary_macro_26847_phase(macro.identity)) is not None:
            assert source % (160 >> phase) == 112 >> phase


def test_scheduler_completes_exact_prefixes_from_all_last_digit_classes() -> None:
    for residue in range(20):
        source = (1 << 80) + (residue - (1 << 80)) % 160
        for ticks in (1, 7, 32):
            result = compile_collatz_temporal_run_quotient(
                source,
                ticks,
                ledger=ResourceLedger(),
                shared_cache=False,
            )
            assert result.endpoint == _physical_trace(source, ticks)[-1]
            assert result.physical_ticks == ticks


def test_scheduler_powers_rotated_26847_entries_and_partial_horizons() -> None:
    phases = (
        (0, 592, 11, ENTRY_26847_PHASES[0]),
        (1, 296, 10, ENTRY_26847_PHASES[1]),
        (2, 148, 9, ENTRY_26847_PHASES[2]),
        (3, 74, 8, ENTRY_26847_PHASES[3]),
        (4, 37, 7, ENTRY_26847_PHASES[4]),
    )
    for _, rotated, complete_ticks, identity in phases:
        full = compile_collatz_temporal_run_quotient(
            rotated,
            complete_ticks,
            ledger=ResourceLedger(),
            include_innovation_tape=True,
            shared_cache=False,
        )
        assert full.endpoint == _physical_trace(rotated, complete_ticks)[-1]
        assert full.first_boundary_macro is not None
        assert full.first_boundary_macro.identity == identity
        partial_ticks = complete_ticks - 1
        partial = compile_collatz_temporal_run_quotient(
            rotated,
            partial_ticks,
            ledger=ResourceLedger(),
            shared_cache=False,
        )
        assert partial.endpoint == _physical_trace(rotated, partial_ticks)[-1]


def test_large_rotated_guard_fibers_publish_exact_prefix_grammars() -> None:
    root = _high_fiber_source(ENTRY_26847_PHASES[0], 12)
    for phase in range(5):
        source = root >> phase
        plan = admit_routed_boundary_macro_plan(source, 128)
        assert plan is not None
        macro = select_admitted_boundary_macro(plan)
        validate_boundary_macro(macro)
        assert macro.endpoint == _physical_trace(source, macro.physical_ticks)[-1]
        ledger = ResourceLedger()
        scratch = RunArithmeticWorkspace.for_ledger(ledger, "collatz_physical")
        with CollatzDyadicMacros(ledger, shared_cache=False) as cache:
            with scratch.scope():
                count = _publish_boundary_macro_prefixes(
                    macro,
                    cache,
                    scratch,
                    anchor=source,
                    normalized_offset=0,
                    odd_offset=0,
                )
            assert count > 0
            for width in (8, 16, 32):
                if width > macro.normalized_symbols:
                    continue
                _assert_cached_prefix(cache, source, width)


def test_rotated_26847_phases_do_not_inherit_the_phase_zero_guard() -> None:
    # One complete physical return from 112 traverses these rotated sources.
    rotated_sources = (56, 28, 14, 7, 22)
    for source in rotated_sources:
        plan = admit_routed_boundary_macro_plan(source, 32)
        assert plan is None or plan.identity != ENTRY_26847_PHASES[0]
        if plan is not None:
            macro = select_admitted_boundary_macro(plan)
            validate_boundary_macro(macro)
            assert macro.endpoint == _physical_trace(source, macro.physical_ticks)[-1]


def test_every_rotated_grammar_slice_matches_the_literal_normalized_trace() -> None:
    root = _high_fiber_source(ENTRY_26847_PHASES[0], 3)
    for phase in range(5):
        source = root >> phase
        plan = admit_routed_boundary_macro_plan(source, 16 - phase)
        assert plan is not None and plan.repetitions == 3
        macro = select_admitted_boundary_macro(plan)
        trace = _normalized_trace(source, macro.normalized_symbols)
        for start in range(len(trace)):
            for stop in range(start, len(trace)):
                action, ones = _slice_action(macro, start, stop - start)
                assert action.endpoint(trace[start]) == trace[stop]
                assert ones == sum(value & 1 for value in trace[start:stop])


def test_scheduler_routes_exact_cylinder_guards_for_new_cycles() -> None:
    for identity in (ENTRY_0563, ENTRY_26847_PHASES[0]):
        source = _high_fiber_source(identity, 30)
        plan = admit_routed_boundary_macro_plan(source, 128)
        assert plan is not None and plan.identity == identity
        macro = select_admitted_boundary_macro(plan)
        validate_boundary_macro(macro)
        assert macro.endpoint == _physical_trace(source, macro.physical_ticks)[-1]
        admitted = has_admitted_boundary_macro(
            _source_node(source),
            128,
            include_innovation_tape=True,
            include_joint_cocycle=True,
            allow_border_return=False,
        )
        assert admitted


def test_unproductive_border_guard_preserves_high_entropy_cylinder_route() -> None:
    source = (1 << 4095) + (113 - (1 << 4095)) % 160
    assert source.bit_length() == 4096
    assert source % 160 == 113
    ledger = ResourceLedger()
    scratch = RunArithmeticWorkspace.for_ledger(ledger, "collatz_physical")
    with scratch.scope():
        assert not has_admitted_boundary_macro(
            _source_node(source),
            4096,
            include_innovation_tape=False,
            include_joint_cocycle=False,
            ledger=ledger,
            scratch=scratch,
        )
    assert ledger.counters["collatz_physical_boundary_macro_plan_checks"] == 1


def test_prefix_cache_publishes_powered_edge_grammars() -> None:
    for identity, repetitions in ((ENTRY_0563, 30), (ENTRY_26847_PHASES[0], 12)):
        source = _high_fiber_source(identity, repetitions)
        ticks = 4 * repetitions + 1 if identity == ENTRY_0563 else 5 * repetitions + 1
        macro = select_boundary_macro(source, ticks, minimum_repetitions=1)
        assert macro is not None and macro.identity == identity
        assert macro.repetitions == repetitions
        ledger = ResourceLedger()
        scratch = RunArithmeticWorkspace.for_ledger(ledger, "collatz_physical")
        with CollatzDyadicMacros(ledger, shared_cache=False) as cache:
            with scratch.scope():
                count = _publish_boundary_macro_prefixes(
                    macro,
                    cache,
                    scratch,
                    anchor=source,
                    normalized_offset=0,
                    odd_offset=0,
                )
            assert count >= 3
            for width in (8, 16, 32):
                _assert_cached_prefix(cache, source, width)


def test_run_executor_consumes_edge_macro_with_demanded_observers() -> None:
    cases = ((30, 9, ENTRY_0563, 80), (592, 11, ENTRY_26847_PHASES[0], 11))
    for source, ticks, identity, endpoint in cases:
        result = compile_collatz_temporal_run_quotient(
            source,
            ticks,
            ledger=ResourceLedger(),
            include_joint_cocycle=True,
            include_f5=True,
            include_width_spine=True,
            include_innovation_tape=True,
            innovation_modulus=49,
            shared_cache=False,
        )
        assert result.endpoint == endpoint
        assert result.run_actions == 1
        assert result.first_boundary_macro is not None
        assert result.first_boundary_macro.identity == identity
        assert result.normalized_symbols + result.phase == result.division_ticks
        assert result.joint_action is not None
        assert result.joint_action.endpoint == endpoint
        assert result.innovation_observation is not None
        assert result.innovation_observation.physical_ticks == ticks
