"""Exact guarded boundary actions stay source-bound and demand-aware."""

from dataclasses import fields

import pytest

from number_compiler.hashlife.execution.source_bound_images import (
    SourceImageCandidate,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz import boundary_macros
from number_compiler.sequences.collatz.boundary_macros import (
    BoundaryActionTemplateMemo,
    CollatzBoundaryMacro,
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
    assert (macro.family, macro.repetitions, macro.physical_ticks) == ("4721", 3, 13)
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


@pytest.mark.parametrize(
    ("source", "ticks", "family"),
    ((164, 7, "421"), (94, 9, "4721"), (26, 5, "630"), (19, 4, "989")),
)
def test_each_guarded_family_matches_endpoint_f5_joint_and_width(
    source: int, ticks: int, family: str
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
    assert result.first_boundary_macro.family == family
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
        cold = memo.get("4721", 2)

        def forbidden(*_args: object, **_kwargs: object) -> object:
            raise AssertionError("warm boundary template lookup rebuilt its action")

        monkeypatch.setattr(
            boundary_macros, "_build_boundary_action_template", forbidden
        )
        assert memo.get("4721", 2) is cold
    assert ledger.counters["collatz_boundary_template_publications"] == 1
    assert ledger.counters["collatz_boundary_template_hits"] == 1


def test_template_memo_cleanup_failure_blocks_use_and_can_be_retried(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    memo = BoundaryActionTemplateMemo(ledger)
    memo.get("4721", 2)
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
        memo.get("4721", 2)

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
    occurrence = (0, 164, source_macro.physical_ticks, source_macro.family)
    with pytest.raises(ValueError, match="differs from its run witness"):
        workspace._attach_boundary_macro(candidate, occurrence, source_macro)


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
    assert result.first_boundary_macro.family == "989"
