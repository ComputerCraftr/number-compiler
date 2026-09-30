"""Powered views must forward the same captured engine observations by name."""

from dataclasses import fields

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_unindexed_metrics
from number_compiler.resources.metric_replace import replace_metric
from number_compiler.resources.powered_metrics import project_powered_metrics
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockMetrics
from number_compiler.sequences.reverse_add.power import ReverseAddPowerMetrics


@pytest.mark.parametrize("kind", (ReverseAddPowerMetrics, CollatzPhysicalBlockMetrics))
def test_every_shared_metric_is_forwarded_without_positional_zeros(
    kind: type[ReverseAddPowerMetrics] | type[CollatzPhysicalBlockMetrics],
) -> None:
    point = collect_unindexed_metrics(ResourceLedger())
    observations = {
        field.name: index + 101
        for index, field in enumerate(fields(point))
        if type(getattr(point, field.name)) is int
    }
    point = replace_metric(
        point,
        {
            **observations,
            "resource_work_counters": {
                "spacetime_primitive_field_steps": 17,
                "spacetime_forcing_classes": 23,
                "run_action_cache_entries": 29,
            },
        },
    )
    metadata: dict[str, object] = {
        "seed": 196,
        "operator_nodes": 7,
        "compose_operations": 4,
        "syntax_depth_bound": 3,
        "descriptor_bits": 19,
    }
    if kind is ReverseAddPowerMetrics:
        metadata.update(base=10, generation=16, spacetime_carry_direction="lsd-to-msd")
    else:
        metadata.update(steps=16)
    report = project_powered_metrics(kind, point, **metadata)
    assert type(report) is kind
    for name in observations.keys() - metadata.keys():
        if hasattr(report, name):
            assert getattr(report, name) == getattr(point, name), name
    assert report.resource_work_counters is point.resource_work_counters
    if kind is ReverseAddPowerMetrics:
        assert isinstance(report, ReverseAddPowerMetrics)
        assert report.hashlife_tile_roots == point.canonical_tile_roots
        assert report.hashlife_leaf_cache_entries == point.leaf_word_cache_entries
        assert report.hashlife_section_cache_hits == point.section_cache_hits
        assert report.spacetime_primitive_field_steps == 17
        assert report.spacetime_forcing_classes == 23
        assert report.run_action_cache_entries == 29


def test_unknown_powered_metadata_is_not_silently_dropped() -> None:
    point = collect_unindexed_metrics(ResourceLedger())
    with pytest.raises(ValueError, match="unknown powered metric"):
        project_powered_metrics(CollatzPhysicalBlockMetrics, point, unknown=1)


def test_unindexed_metrics_preserve_actual_point_work_without_new_queries() -> None:
    ledger = ResourceLedger()
    ledger.bump("direct_powered_point_queries", 7)
    ledger.bump("temporal_point_requests", 11)
    before = dict(ledger.counters)
    report = collect_unindexed_metrics(ledger)
    assert report.direct_powered_point_queries == 7
    assert report.point_queries == 11
    assert report.resource_work_counters["direct_powered_point_queries"] == 7
    assert dict(ledger.counters) == before
    ledger.bump("direct_powered_point_queries", 2)
    ledger.bump("temporal_point_requests", 3)
    assert report.direct_powered_point_queries == 7
    assert report.point_queries == 11
    after = collect_unindexed_metrics(ledger)
    assert after.direct_powered_point_queries == 9
    assert after.point_queries == 14
