"""Exact endpoint closure does not hide cold primitive evaluation."""

import pytest

from devtools.verification.decimal_endpoint_seam import decimal_step, reachable_pairs
from devtools.verification.endpoint_seam_audit import (
    BoundedEndpointPowerArena,
    audit_endpoint_frontier,
)

pytestmark = pytest.mark.validation


def test_reachable_pair_domain_and_endpoint_fibers() -> None:
    report = audit_endpoint_frontier(reachable_pairs(4), decimal_step, horizons=(1, 2))
    assert report["distinct_sources"] == 342
    rows = report["rows"]
    assert isinstance(rows, list)
    assert rows[0]["endpoint_classes"] == 261
    assert rows[0]["aliases"] == 81
    assert rows[0]["primitive_successors"] == 342
    assert rows[0]["endpoint_intern_hits"] == 81


def test_closed_primitive_table_powers_without_primitive_execution() -> None:
    arena = BoundedEndpointPowerArena(lambda n: (n * n) % 17)
    for source in range(17):
        arena.power(source, 0)
    assert arena.primitive_successors == 17

    def forbidden(n: int) -> int:
        raise AssertionError("primitive called after complete A1 table")

    arena.step = forbidden
    for level in range(1, 11):
        for source in range(17):
            assert arena.power(source, level) == pow(source, 1 << (1 << level), 17)
    assert arena.primitive_successors == 17


def test_cold_nonrepeating_orbit_is_charged_and_warm_result_reused() -> None:
    arena = BoundedEndpointPowerArena(lambda n: n + 1)
    for level in range(11):
        assert arena.power(0, level) == 1 << level
        assert arena.primitive_successors == 1 << level
    cold = arena.primitive_successors
    assert arena.power(0, 10) == 1024
    assert arena.primitive_successors == cold
    assert arena.retained_endpoints == 1024


def test_endpoint_aliases_share_future_cache_but_do_not_close_source_domain() -> None:
    arena = BoundedEndpointPowerArena(decimal_step)
    sources = tuple(reachable_pairs(4))
    targets = {arena.power(source, 0) for source in sources}
    assert len(targets) == 261
    assert len(targets - set(sources)) > 0  # Growth exits this bounded source domain.
    for source in sources:
        assert arena.power(source, 1) == decimal_step(decimal_step(source))
    assert arena.retained_endpoints < arena.retained_results


def test_primitive_budget_does_not_claim_a_cold_jump() -> None:
    arena = BoundedEndpointPowerArena(lambda n: n + 1, max_primitives=1)
    with pytest.raises(ValueError, match="primitive budget"):
        arena.power(0, 4)
    assert arena.primitive_successors == 1
