"""Focused checks for the bounded Compact B1 scope-graph audit."""

import pytest

from devtools.verification.comma_b1_quotient import offset_representatives
from devtools.verification.comma_b1_scope_audit import (
    _terminal_label,
    audit_root,
    audit_scope_graph,
)
from number_compiler.sequences.comma.boundary_chart import BoundaryChart


def test_root_zero_reproduces_compact_scope_graph_counts() -> None:
    result = audit_scope_graph()
    graph = result["source_graph"]
    assert isinstance(graph, dict)
    assert graph["recursive_calls"] == 881
    assert graph["unique_source_scope_pairs"] == 881
    assert graph["reused_source_scope_visits"] == 0
    assert graph["unique_source_states"] == 269
    assert graph["terminal_leaves"] == 495
    assert graph["output_labels"] == 46
    assert graph["distinct_scopes"] == 537
    assert graph["singleton_scopes"] == 448
    assert graph["terminal_phase_count"] == 924
    assert graph["outcome_coverage"] == {
        "fork": 20,
        "landmine": 90,
        "live": 385,
    }


@pytest.mark.parametrize("root_index", [True, -1, 46])
def test_scope_audit_rejects_invalid_root_selectors(root_index: int) -> None:
    with pytest.raises(ValueError, match="root index"):
        audit_scope_graph(root_index=root_index)


def test_scope_audit_requires_the_canonical_root_offset() -> None:
    representatives = offset_representatives()
    with pytest.raises(ValueError, match="canonical representative"):
        audit_root(0, representatives[1])


@pytest.mark.parametrize("coordinate", [91, 10])
def test_scope_audit_rejects_malformed_live_crossing(coordinate: int) -> None:
    crossing = BoundaryChart("entry", 1 if coordinate == 91 else 2, 1, coordinate)
    with pytest.raises(AssertionError, match="canonical root domain"):
        _terminal_label(crossing, None)


def test_live_crossing_is_projected_to_its_orbit_not_raw_offset() -> None:
    assert _terminal_label(BoundaryChart("entry", 1, 1, 10), None) == ("live", 1)
    assert _terminal_label(BoundaryChart("entry", 1, 1, 0), None) == ("live", 0)
