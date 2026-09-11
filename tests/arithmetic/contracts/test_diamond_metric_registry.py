"""Node categories are observed independently of reservations and cache slots."""

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.metric_registry import observed_node_partition
from number_compiler.resources.stores import LedgerDict, LedgerList


def test_diamond_nodes_have_disjoint_roles_and_interner_slots_are_not_nodes() -> None:
    ledger = ResourceLedger()
    for role, count in (
        ("exact_source", 1),
        ("temporal_action", 2),
        ("image_action", 3),
        ("diamond_cell", 4),
        ("spatial_binding", 5),
        ("unrecognized_helper", 6),
    ):
        owner = ledger.register(role, role)
        records: LedgerList[object]
        records = ledger.make_list(owner)
        ledger.reserve(owner, entries=count, nodes=count)
        records.extend(ArenaToken(role) for _ in range(count))
    owner = ledger.register("image interner", "image_action")
    interner: LedgerDict[object, object]
    interner = ledger.make_dict(owner, nodes_per_entry=0)
    ledger.reserve(owner, entries=3)
    interner.update({0: 0, 1: 1, 2: 2})
    actual = observed_node_partition(ledger.inventory())
    assert actual["image_action_nodes"] == 3
    assert actual["diamond_cell_nodes"] == 4
    assert actual["temporal_program_nodes"] == 2
    assert actual["spatial_binding_nodes"] == 5
    assert actual["other_retained_nodes"] == 6
    assert sum(actual.values()) == 21
    observed = tuple(item.observed_entries for item in ledger.inventory())
    assert all(value is not None for value in observed)
    assert sum(value for value in observed if value is not None) == 24


def test_unpublished_reservation_does_not_create_a_reported_diamond_node() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("diamonds", "diamond_cell")
    ledger.make_list(owner)
    ledger.reserve(owner, entries=10, nodes=10)
    assert observed_node_partition(ledger.inventory())["diamond_cell_nodes"] == 0
    assert ledger.snapshot().nodes == 10


def test_mixed_cell_arena_reports_actual_image_records_without_double_counting() -> (
    None
):
    from number_compiler.hashlife.actions.diamond_actions import CellNode

    ledger = ResourceLedger()
    owner = ledger.register("mixed cells", "diamond_cell")
    records: LedgerList[object]
    records = ledger.make_list(owner)
    ledger.reserve(owner, entries=2, nodes=2)
    records.extend(
        (CellNode("source", 0, source_tile=0), CellNode("image", 0, left=0, action=0))
    )
    counts = observed_node_partition(ledger.inventory(), dict(ledger.iter_containers()))
    assert counts["image_action_nodes"] == counts["diamond_cell_nodes"] == 1
    assert sum(counts.values()) == 2


def test_diamond_roles_cannot_reclassify_a_packed_history_as_an_action() -> None:
    for role in ("temporal_action", "image_action", "diamond_cell"):
        ledger = ResourceLedger()
        owner = ledger.register(role, role)
        records: LedgerList[object]
        records = ledger.make_list(owner)
        ledger.reserve(owner, entries=1, nodes=1)
        records.append(0b101101)
        report = collect_ledger_metrics(ledger)
        assert report.forbidden_future_payloads > 0
        assert report.representation_boundary_complete == 0


def test_uninstrumented_runtime_does_not_report_a_measured_diamond_zero() -> None:
    from number_compiler.resources.metric_registry import DIAMOND_WORK_COUNTERS

    ledger = ResourceLedger()
    assert collect_ledger_metrics(ledger).diamond_instrumentation_complete == 0
    for name in DIAMOND_WORK_COUNTERS:
        ledger.bump(name, 0)
    ledger.bump("diamond_requests", 3)
    ledger.bump("diamond_cache_hits", 2)
    ledger.bump("diamond_evaluations")
    report = collect_ledger_metrics(ledger)
    assert report.diamond_instrumentation_complete == 1
    assert (
        report.diamond_requests
        == report.diamond_cache_hits + report.diamond_evaluations
        == 3
    )
    # Counters cannot confer an execution certificate.
    assert report.bimachine_composition_certified == 0


def test_original_source_record_is_charged_before_any_geometry_node() -> None:
    from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
    from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry

    ledger = ResourceLedger()
    source = ExactSource((0, 1), 2)
    geometry = SourceGeometry(ledger, source)
    report = collect_ledger_metrics(ledger)
    assert report.exact_source_occurrences == 1
    assert report.source_payload_nodes == report.cache_slots == 1
    assert geometry._sources[0] is geometry._construction.source is source
    assert not geometry.nodes


def test_source_budget_rejection_does_not_publish_an_uncharged_record() -> None:
    import pytest

    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )
    from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
    from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry

    ledger = ResourceLedger(max_nodes=0, max_cache_entries=0)
    with pytest.raises(BlockContextBudgetExceeded):
        SourceGeometry(ledger, ExactSource((1,), 2))
    assert ledger.snapshot().entries == ledger.snapshot().nodes == 0
    assert all(item.accounting_delta == 0 for item in ledger.inventory())


def test_equal_but_distinct_original_source_records_are_not_identity_deduplicated() -> (
    None
):
    from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
    from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry

    ledger = ResourceLedger()
    first = SourceGeometry(ledger, ExactSource((1,), 2))
    second = SourceGeometry(ledger, ExactSource((1,), 2))
    assert first._sources[0] == second._sources[0]
    assert first._sources[0] is not second._sources[0]
    report = collect_ledger_metrics(ledger)
    assert report.exact_source_occurrences == report.source_payload_nodes == 2
