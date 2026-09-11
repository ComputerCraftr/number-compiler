"""Dyadic carry actions skip known parents without storing emitted words."""

from collections import OrderedDict
from typing import Never

import pytest

from devtools.proofs.carry_interval_effects import CarryActionQuotientArena
from devtools.proofs.lazy_reverse import LazyReverseApplication, ReverseRangeRequest
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.resources.ledger import ResourceLedger


def forbidden(*args: object, **kwargs: object) -> Never:
    raise AssertionError("known parent descended into source or children")


def test_parent_action_hit_skips_source_and_child_composition(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = (9, 10, 10, 9) * 16
    application = LazyReverseApplication(10, -1, 0, source)
    request = ReverseRangeRequest(0, 64, 6)
    result = application._evaluate(request, OrderedDict())
    assert application.ledger.counters["reverse_range_parent_compositions"] > 0
    assert any(key.level == 6 for key in application._ranges)
    before = dict(application.ledger.counters)
    monkeypatch.setattr(application, "_coefficient", forbidden)
    monkeypatch.setattr(application.port_actions, "compose_intervals", forbidden)
    assert application._evaluate(request, OrderedDict()) == result
    after = application.ledger.counters
    for counter in (
        "reverse_source_reads",
        "reverse_range_leaf_evaluations",
        "reverse_range_parent_compositions",
        "bounded_limb_operations",
    ):
        assert after.get(counter, 0) == before.get(counter, 0)


def test_different_parent_interiors_share_canonical_effect_id() -> None:
    a, b = (9, 10, 10, 9), (10, 9, 9, 10)
    source = a + b + b[::-1] + a[::-1]
    application = LazyReverseApplication(10, -1, 0, source)
    first = application._evaluate(ReverseRangeRequest(0, 4, 2), OrderedDict())
    second = application._evaluate(ReverseRangeRequest(0, 8, 2), OrderedDict())
    assert first == second
    # The first carry differs with incoming zero, so the action cannot invert
    # the original emitted carry word despite having a reusable parent ID.
    assert int(a[0] >= 10) != int(b[0] >= 10)


@pytest.mark.parametrize("width", (16, 1024, 65536))
def test_terminal_reset_does_not_eagerly_scan_source_width(width: int) -> None:
    application = LazyReverseApplication(10, -1, 0, (10,) * width)
    assert application._scan(0, OrderedDict()) == 1
    assert application.ledger.counters["reverse_source_reads"] == 2
    assert application.ledger.counters["reverse_range_leaf_evaluations"] == 1


def test_canonical_carry_classification_rejects_other_port_and_foreign_owner() -> None:
    first, second = CarryActionQuotientArena(), CarryActionQuotientArena()
    port = PortVariable(0, 0, "carry", 0)
    other_port = PortVariable(0, 1, "carry", 0)
    identity = first.variable(port)
    assert first.carry_code(identity, port) == 1
    with pytest.raises(ValueError):
        first.carry_code(identity, other_port)
    with pytest.raises(ValueError):
        second.carry_code(identity, port)


def test_original_source_parent_uses_canonical_tile_before_any_coefficient(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = (9, 10, 10, 9) * 1024
    ledger = ResourceLedger()
    # The admitted pair alphabet is 0..18 with the separate blank symbol 19.
    exact = ExactSource(source, 10, "reverse-pair", alphabet_size=19, blank=19)
    geometry = SourceGeometry(ledger, exact)
    geometry.span(source, 19, len(source))
    application = LazyReverseApplication(
        10, 19, 0, source, ledger, source_geometry=geometry
    )
    monkeypatch.setattr(application, "_coefficient", forbidden)
    request = ReverseRangeRequest(0, len(source), 12)
    action = application._evaluate(request, OrderedDict())
    assert application.port_actions.interval_effect(action).reset_count == 2
    assert ledger.counters["reverse_source_reads"] == 2  # Two original symbol classes.
    assert ledger.counters["reverse_source_tile_action_visits"] < 30
    before = dict(ledger.counters)
    assert application._evaluate(request, OrderedDict()) == action
    assert (
        ledger.counters["reverse_source_tile_action_visits"]
        == before["reverse_source_tile_action_visits"]
    )


def test_foreign_original_geometry_rejects_before_allocating_application() -> None:
    ledger = ResourceLedger()
    geometry = SourceGeometry(ledger, ExactSource((2, 2), 10, alphabet_size=19))
    geometry.span((2, 2), 0, 2)
    before = ledger.snapshot()
    with pytest.raises(ValueError):
        LazyReverseApplication(10, 0, 4, (4, 4), ledger, source_geometry=geometry)
    assert ledger.snapshot() == before


def test_known_siblings_do_not_publish_unrequested_ancestors() -> None:
    application = LazyReverseApplication(10, -1, 0, (9, 10, 10, 9) * 4)
    workspace: OrderedDict[tuple[int, int], tuple[int, int]] = OrderedDict()
    application._evaluate(ReverseRangeRequest(0, 2), workspace)
    application._evaluate(ReverseRangeRequest(0, 4), workspace)
    assert len(application._ranges) == 2
    assert all(key.level == 1 for key in application._ranges)
    parent = application._evaluate(ReverseRangeRequest(0, 4, 2), workspace)
    assert len(application._ranges) == 3
    assert sum(key.level > 1 for key in application._ranges) == 1
    before = application.ledger.snapshot()
    assert application._evaluate(ReverseRangeRequest(0, 4, 2), workspace) == parent
    after = application.ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)


def test_demanded_parent_bindings_evict_without_invalidating_canonical_actions() -> (
    None
):
    application = LazyReverseApplication(10, -1, 0, (9, 10, 10, 9) * 4)
    request = ReverseRangeRequest(0, 16, 4)
    parent = application._evaluate(request, OrderedDict())
    before = application.ledger.snapshot()
    assert application._ranges
    application.ledger.evict_query_memos()
    assert not application._ranges
    after = application.ledger.snapshot()
    assert after.entries < before.entries
    assert after.nodes < before.nodes
    assert application._evaluate(request, OrderedDict()) == parent
