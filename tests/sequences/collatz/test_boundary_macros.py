"""Exact guarded boundary actions stay source-bound and demand-aware."""

from copy import copy
from dataclasses import fields, replace

import pytest

from number_compiler.hashlife.execution.source_bound_images import (
    SourceImageCandidate,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.sequences.collatz import boundary_macros
from number_compiler.sequences.collatz.border_identity import (
    CYCLE_89,
    ENTRY_0563,
    ENTRY_89_AT_NINE,
    ENTRY_421,
    ENTRY_4721,
    ENTRY_26847_PHASES,
    PATH_305,
    PATH_630,
    BoundaryOccurrenceProducerStamp,
    BoundaryPathKind,
    ClosedBorderCycle,
    CycleEntryPhase,
    GuardedBorderPath,
    border_return_path,
)
from number_compiler.sequences.collatz.boundary_macros import (
    BoundaryActionTemplateMemo,
    CollatzBoundaryMacro,
    admit_boundary_macro_plan,
    boundary_metric_suffix,
    select_boundary_macro,
    validate_boundary_macro,
)
from number_compiler.sequences.collatz.physical_images import (
    CollatzPhysicalImageWorkspace,
)
from number_compiler.sequences.collatz.source_cylinder_cache import (
    CollatzDyadicMacros,
)
from number_compiler.sequences.collatz.temporal_dyadic import D8TemporalTable
from number_compiler.sequences.collatz.temporal_run_quotient import (
    compile_collatz_temporal_run_quotient,
)


def _physical(source: int, ticks: int) -> int:
    for _ in range(ticks):
        source = 3 * source + 1 if source & 1 else source // 2
    return source


def test_guarded_macro_is_exact_and_issued_only_by_the_selector() -> None:
    macro = select_boundary_macro(2174, 13)
    assert macro is not None
    validate_boundary_macro(macro)
    assert not hasattr(CollatzBoundaryMacro, "from_structural_payload")
    assert (macro.identity, macro.repetitions, macro.physical_ticks) == (
        ENTRY_4721,
        3,
        13,
    )
    assert macro.endpoint == _physical(2174, 13)
    with pytest.raises(TypeError):
        CollatzBoundaryMacro()
    uninitialized = object.__new__(CollatzBoundaryMacro)
    with pytest.raises(ValueError, match="no producer authority"):
        validate_boundary_macro(uninitialized)

    forged = object.__new__(CollatzBoundaryMacro)
    for item in fields(macro):
        object.__setattr__(forged, item.name, getattr(macro, item.name))
    object.__setattr__(forged, "endpoint", macro.endpoint + 1)
    with pytest.raises(ValueError, match="not an exact guarded action"):
        validate_boundary_macro(forged)


def test_cycle_display_phase_does_not_create_an_unguarded_entry_action() -> None:
    eight_entry = CycleEntryPhase(CYCLE_89, 0)
    assert eight_entry.display_label == "898"
    assert ENTRY_89_AT_NINE.display_label == "989"
    assert boundary_metric_suffix(ENTRY_89_AT_NINE) == "989"
    assert admit_boundary_macro_plan(18, 100, minimum_repetitions=1) is None
    with (
        BoundaryActionTemplateMemo(ResourceLedger()) as templates,
        pytest.raises(ValueError, match="unknown Collatz boundary action"),
    ):
        templates.get(eight_entry, 2)


def test_cycle_phases_are_unique_and_guarded_path_labels_are_entry_first() -> None:
    with pytest.raises(ValueError, match="identify every phase uniquely"):
        ClosedBorderCycle.from_rotation((1, 2, 1, 2))

    assert PATH_630.display_label == "6→3→0"
    assert PATH_305.display_label == "3→0*→5"
    assert border_return_path(3, 8).display_label == "3→0*→5→6→8"
    assert border_return_path(6, 8).display_label == "6→3→0*→5→6→8"
    assert border_return_path(5, 3).display_label == "5→6→3→0*→5→6→3"
    assert border_return_path(0, 4).display_label == "0*→(3|5→6→3)→0*→5→6→8→4"

    with pytest.raises(ValueError, match="exact entry and exit"):
        GuardedBorderPath(BoundaryPathKind.SIX_THREE_ZERO, 6, 3)


@pytest.mark.parametrize(
    ("source", "ticks", "identity"),
    (
        (164, 7, ENTRY_421),
        (94, 9, ENTRY_4721),
        (26, 5, PATH_630),
        (19, 4, ENTRY_89_AT_NINE),
    ),
)
def test_each_guarded_family_matches_endpoint_f5_joint_and_width(
    source: int, ticks: int, identity: object
) -> None:
    result = compile_collatz_temporal_run_quotient(
        source,
        ticks,
        ledger=ResourceLedger(),
        include_f5=True,
        include_width_spine=True,
        include_joint_cocycle=True,
        include_innovation_tape=True,
    )
    endpoint = _physical(source, ticks)
    assert result.endpoint == endpoint
    assert result.run_actions == 1
    assert result.first_boundary is not None
    assert result.first_boundary[0] == 0
    assert result.first_boundary_macro is not None
    assert result.first_boundary_macro.identity == identity
    assert result.first_boundary_macro.endpoint == endpoint
    assert result.physical_f5 is not None
    assert result.physical_f5.apply(source) == endpoint % 5
    assert result.joint_action is not None
    assert result.joint_action.endpoint == endpoint
    assert result.tape_width_summary is not None
    assert result.tape_width_summary.target_width == endpoint.bit_length()


@pytest.mark.parametrize("source,ticks", ((164, 7), (94, 9), (26, 5), (19, 4)))
def test_partial_boundary_ranges_still_match_literal_physical_steps(
    source: int, ticks: int
) -> None:
    result = compile_collatz_temporal_run_quotient(
        source, ticks - 1, ledger=ResourceLedger(), include_innovation_tape=True
    )
    assert result.endpoint == _physical(source, ticks - 1)
    if result.first_boundary_macro is not None:
        assert result.first_boundary is not None
        assert (
            result.first_boundary[0] + result.first_boundary_macro.physical_ticks
            <= ticks - 1
        )


@pytest.mark.parametrize(
    ("source", "ticks", "identity", "repetitions"),
    (
        (164, 7, ENTRY_421, 2),
        (2174, 13, ENTRY_4721, 3),
        (30, 9, ENTRY_0563, 2),
        (112, 6, ENTRY_26847_PHASES[0], 1),
        (296, 10, ENTRY_26847_PHASES[1], 2),
        (148, 9, ENTRY_26847_PHASES[2], 2),
        (74, 8, ENTRY_26847_PHASES[3], 2),
        (37, 7, ENTRY_26847_PHASES[4], 2),
        (26, 5, PATH_630, 2),
        (13, 4, PATH_305, 2),
        (19, 4, ENTRY_89_AT_NINE, 2),
    ),
)
def test_admitted_plan_binds_a_repetition_limit_for_each_identity(
    source: int, ticks: int, identity: object, repetitions: int
) -> None:
    plan = admit_boundary_macro_plan(source, ticks, minimum_repetitions=1)

    assert plan is not None
    assert plan.identity == identity
    assert plan.repetitions == repetitions
    assert plan.maximum_repetitions >= plan.repetitions
    assert plan.physical_ticks == ticks


def test_midrun_boundary_occurrence_cannot_be_rebound() -> None:
    result = compile_collatz_temporal_run_quotient(
        109,
        9,
        ledger=ResourceLedger(),
        include_f5=True,
        include_width_spine=True,
        include_joint_cocycle=True,
        include_innovation_tape=True,
    )
    assert result.first_boundary is not None
    assert result.first_boundary[0] == 2
    assert result.first_boundary_macro is not None
    assert result.first_boundary[1] == 164
    assert result.first_boundary_stamp is not None
    with pytest.raises(ValueError, match="lost producer authority"):
        replace(result, first_boundary_stamp=copy(result.first_boundary_stamp))
    with pytest.raises(ValueError, match="lost producer authority"):
        replace(
            result,
            first_boundary=(
                0,
                result.first_boundary[1],
                result.first_boundary[2],
                result.first_boundary[3],
            ),
        )
    assert not result.first_boundary_stamp.certifies(
        True,
        result.physical_ticks,
        result.first_boundary,
        result.first_boundary_macro,
    )
    replacement_macro = select_boundary_macro(164, 7)
    assert replacement_macro is not None
    assert replacement_macro is not result.first_boundary_macro
    object.__setattr__(result.first_boundary_stamp, "macro", replacement_macro)
    with pytest.raises(ValueError, match="lost producer authority"):
        result.validate_boundary_producer_stamp()


def test_long_quiet_boundary_is_one_pumped_action_without_d8_discovery() -> None:
    source = 4 + 40 * (1 << 256)
    ticks = 388
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(
        source,
        ticks,
        ledger=ledger,
        include_f5=True,
        include_width_spine=True,
        include_joint_cocycle=True,
    )
    endpoint = _physical(source, ticks)
    assert result.endpoint == endpoint
    assert result.run_actions == 1
    assert result.physical_f5 is not None
    assert result.physical_f5.apply(source) == endpoint % 5
    assert result.joint_action is not None
    assert result.joint_action.endpoint == endpoint
    assert result.tape_width_summary is not None
    assert result.tape_width_summary.target_width == endpoint.bit_length()
    assert ledger.counters.get("collatz_physical_temporal_d8_discovery_symbols", 0) == 0
    assert ledger.counters["collatz_physical_boundary_421_macro_actions"] == 1


def test_template_memo_warm_hit_bypasses_exact_cold_constructor(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    with BoundaryActionTemplateMemo(ledger) as memo:
        cold = memo.get(ENTRY_4721, 2)

        def forbidden(*_args: object, **_kwargs: object) -> object:
            raise AssertionError("warm boundary template lookup rebuilt its action")

        monkeypatch.setattr(
            boundary_macros, "_build_boundary_action_template", forbidden
        )
        assert memo.get(ENTRY_4721, 2) is cold
    assert ledger.counters["collatz_boundary_template_publications"] == 1
    assert ledger.counters["collatz_boundary_template_hits"] == 1


def test_template_memo_cleanup_failure_blocks_use_and_can_be_retried(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    memo = BoundaryActionTemplateMemo(ledger)
    memo.get(ENTRY_4721, 2)
    templates = memo._templates
    assert templates is not None
    owner = templates.owner
    original_dispose = templates.dispose
    failed = False

    def fail_once(instance: object) -> None:
        nonlocal failed
        if instance is not templates:
            raise AssertionError("unexpected template memo cleanup")
        if not failed:
            failed = True
            raise RuntimeError("injected template cleanup failure")
        original_dispose()

    monkeypatch.setattr(type(templates), "dispose", fail_once)
    with pytest.raises(RuntimeError, match="injected template cleanup failure"):
        memo.dispose()

    assert memo._closing and not memo._closed
    assert ledger.inventory_owner(owner).entries > 0
    with pytest.raises(RuntimeError, match="closed"):
        memo.get(ENTRY_4721, 2)

    memo.dispose()
    assert memo._closed and not memo._closing
    disposed = ledger.inventory_owner(owner)
    assert disposed.disposed and disposed.entries == disposed.nodes == 0


def test_foreign_macro_cannot_publish_at_another_root_origin() -> None:
    source_macro = select_boundary_macro(164, 7)
    assert source_macro is not None
    workspace = CollatzPhysicalImageWorkspace(
        ResourceLedger(), 165, 7, include_innovation_tape=True
    )
    candidate = SourceImageCandidate(workspace.root_payload, workspace.steps)
    occurrence = (0, 164, source_macro.physical_ticks, source_macro.identity)
    stamp = BoundaryOccurrenceProducerStamp._issue(165, 7, occurrence, source_macro)
    with pytest.raises(ValueError, match="outside its demanded root"):
        workspace._attach_boundary_macro(candidate, occurrence, stamp, source_macro)


def test_macro_occurrence_retention_is_ledger_owned_and_disposed() -> None:
    ledger = ResourceLedger()
    workspace = CollatzPhysicalImageWorkspace(
        ledger,
        2174,
        13,
        retain_chronology=False,
        include_innovation_tape=True,
    )
    assert workspace.first_boundary_macro is not None
    memo = workspace._boundary_macro_memo
    assert memo is not None and len(memo) == 1
    owner = memo.owner
    before = ledger.inventory_owner(owner)
    assert before.entries == 1 and before.nodes > 0

    workspace.dispose()

    after = ledger.inventory_owner(owner)
    assert after.disposed
    assert after.entries == 0 and after.nodes == 0
    assert workspace._boundary_macro_memo is None
    assert workspace._first_boundary_macro_snapshot is None
    assert workspace._boundary_route_snapshot is None


def test_run_constructor_publishes_only_a_demanded_executed_macro() -> None:
    ordinary_ledger = ResourceLedger()
    ordinary = compile_collatz_temporal_run_quotient(2174, 13, ledger=ordinary_ledger)
    assert ordinary.endpoint == _physical(2174, 13)
    assert ordinary.first_boundary is None
    assert ordinary.first_boundary_macro is None
    assert ordinary_ledger.counters["collatz_physical_boundary_4721_macro_actions"] == 1
    assert ordinary_ledger.counters.get("collatz_boundary_template_publications") == 1

    observed_ledger = ResourceLedger()
    observed = compile_collatz_temporal_run_quotient(
        2174, 13, ledger=observed_ledger, include_innovation_tape=True
    )
    assert observed.endpoint == ordinary.endpoint
    assert observed.first_boundary is not None
    assert observed.first_boundary[0] == 0
    assert observed.first_boundary_macro is not None
    assert observed.first_boundary_macro.source == 2174


def test_reentered_chain_keeps_the_first_boundary_source_authoritative() -> None:
    # The root reaches a later reentry point before applying a joined action.
    # The final result need not retain that non-root chain, so assert its actual
    # application through the production counter and its published boundary.
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(
        4348,
        300,
        ledger=ledger,
        include_f5=True,
        include_width_spine=True,
        include_joint_cocycle=True,
        include_innovation_tape=True,
        innovation_modulus=49,
    )

    assert (
        ledger.counters[_collatz_keys.COLLATZ_PHYSICAL_UNIFIED_SKEW_APPLIED_ACTIONS] > 0
    )
    assert result.first_boundary is not None
    assert result.first_boundary[0] > 0
    assert result.first_boundary[1] != result.source
    assert result.first_boundary_macro is not None
    assert result.first_boundary[1] == result.first_boundary_macro.source
    assert result.first_boundary_stamp is not None
    assert result.first_boundary_stamp.certifies(
        result.source,
        result.physical_ticks,
        result.first_boundary,
        result.first_boundary_macro,
    )


def test_selected_macro_stamp_uses_witness_source_after_outer_rebase() -> None:
    macro = select_boundary_macro(164, 7)
    assert macro is not None
    stamp = BoundaryOccurrenceProducerStamp._issue_selected_macro(
        4348, 128, 111, macro, boundary_offset=17
    )

    assert stamp.occurrence == (17, 164, 7, ENTRY_421)
    assert stamp.certifies(4348, 128, stamp.occurrence, macro)


def test_ordinary_odd_run_does_not_build_observer_specific_989_macro() -> None:
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(19, 4, ledger=ledger)
    assert result.endpoint == _physical(19, 4)
    assert result.first_boundary_macro is None
    assert ledger.counters.get("collatz_physical_boundary_989_macro_actions", 0) == 0
    assert ledger.counters.get("collatz_boundary_template_lookups") is None


@pytest.mark.usefixtures("isolated_process_cache")
def test_warm_guarded_parent_is_used_before_cold_macro_or_d8(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.resources.process_cache import clear_process_cache

    clear_process_cache()
    source = 4 + 40 * (1 << 256)
    compile_collatz_temporal_run_quotient(
        source, 388, ledger=ResourceLedger(), shared_cache=True
    )
    with CollatzDyadicMacros(ResourceLedger(), shared_cache=True) as macros:
        cell = macros.lookup(source, 256)
        assert cell is not None and cell.width == 256
        physical_ticks = cell.width + cell.odd_symbols

    def forbidden_template(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("warm parent reconstructed the guarded action")

    def forbidden_d8(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("warm parent fell back to D8 discovery")

    monkeypatch.setattr(
        boundary_macros, "_build_boundary_action_template", forbidden_template
    )
    monkeypatch.setattr(D8TemporalTable, "select", forbidden_d8)
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(
        source, physical_ticks, ledger=ledger, shared_cache=True
    )
    assert result.endpoint == cell.apply(source)
    assert result.normalized_symbols == 256
    assert ledger.counters["collatz_hashlife_occurrence_applied_hits"] == 1
    assert ledger.counters.get("collatz_physical_boundary_plan_checks", 0) == 0
    assert ledger.counters.get("collatz_physical_temporal_d8_discovery_symbols", 0) == 0
    assert ledger.counters.get("collatz_physical_boundary_421_macro_actions", 0) == 0
    clear_process_cache()


def test_eight_bit_parity_prefix_does_not_authorize_a_longer_action() -> None:
    from number_compiler.sequences.collatz.hensel_cylinders import HenselCylinder
    from number_compiler.sequences.collatz.parity import normalized_collatz

    cylinder = HenselCylinder(8, 1)
    assert cylinder.contains(1) and cylinder.contains(257)
    assert not HenselCylinder(9, 1).contains(257)

    endpoints = []
    for source in (1, 257):
        value = source
        odd_symbols = 0
        for _ in range(8):
            odd_symbols += value & 1
            value = normalized_collatz(value)
        result = compile_collatz_temporal_run_quotient(
            source,
            8 + odd_symbols,
            ledger=ResourceLedger(),
        )
        assert result.normalized_symbols == 8
        assert result.endpoint == value
        endpoints.append(value)
    assert endpoints == [1, 82]


def test_demanded_989_macro_keeps_the_exact_completed_endpoint() -> None:
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(
        19, 4, ledger=ledger, include_innovation_tape=True
    )
    assert result.endpoint == _physical(19, 4)
    assert result.first_boundary_macro is not None
    assert result.first_boundary_macro.identity == ENTRY_89_AT_NINE
