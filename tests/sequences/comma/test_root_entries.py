"""Independent finite controls for the proposed global-root proof boundary."""

from __future__ import annotations

import pytest

from devtools.verification.comma_root_entries import audit_root_entries
from devtools.verification.comma_semantic_quotients import build_future_graph
from tests.support.comma_oracles import literal_children


@pytest.mark.validation
def test_all_91_first_crossing_entries_preserve_both_child_ranks() -> None:
    rows = audit_root_entries(build_future_graph())
    assert tuple(row.offset for row in rows) == tuple(range(91))
    open_rows = [row for row in rows if row.future_open]
    assert [row.offset for row in open_rows] == [3, 34, 75]
    for row in open_rows:
        assert row.exponent_gain == 5
        assert row.fork_a == 2
        assert row.child_ranks == (None, 7)
    assert all(row.chart_visits > 0 for row in rows)


def test_surviving_entries_are_on_the_unbranched_literal_source20_prefix() -> None:
    value = 20
    entries: list[int] = []
    for _ in range(10_000):
        children = literal_children(value)
        assert len(children) == 1
        value = children[0]
        if value >= 100_000:
            entries.append(value)
        if value == 100_075:
            break
    else:
        pytest.fail("literal source-20 control did not reach the entry boundary")
    assert entries == [100_003, 100_034, 100_075]


def test_first_crossing_upper_bound_uses_the_receiving_leading_digit() -> None:
    crossings = {
        child
        for parent in range(99_901, 100_000)
        for child in literal_children(parent)
        if child >= 100_000
    }
    assert crossings
    assert all(0 <= child - 100_000 <= 90 for child in crossings)
