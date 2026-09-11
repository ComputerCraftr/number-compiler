"""Outer scalar caches must not bypass the live tile execution contract."""

import pytest

from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


@pytest.mark.parametrize("family", ("reverse", "collatz"))
@pytest.mark.parametrize("cache", ("cold", "response", "microblock"))
def test_direct_scalar_query_admits_context_before_any_cache_hit(
    monkeypatch: pytest.MonkeyPatch, family: str, cache: str
) -> None:
    term = (
        ReverseAddPoweredTerm(196, 2)
        if family == "reverse"
        else PoweredCollatzTerm(27, 2)
    )
    index = term._point_index()
    projection = index._lazy_application
    try:
        expected = None
        if cache != "cold":
            expected = index.direct_powered_point(0)
        if cache == "microblock":
            index._point_response.clear()
        ledger = projection.ledger
        before = ledger.snapshot()
        queries = index._point_queries, index._direct_powered_point_queries

        def revoked(*_args: object) -> None:
            raise ValueError("scalar execution wiring revoked")

        with monkeypatch.context() as patch:
            patch.setattr(projection.scheduler.adapter, "validate_wiring", revoked)
            with pytest.raises(ValueError, match="scalar execution wiring revoked"):
                index.direct_powered_point(0)

        assert (index._point_queries, index._direct_powered_point_queries) == queries
        after = ledger.snapshot()
        assert (after.entries, after.nodes) == (before.entries, before.nodes)
        for counter in (
            "point_response_requests",
            "point_response_cache_hits",
            "point_response_evaluations",
        ):
            assert after.counters.get(counter, 0) == before.counters.get(counter, 0)
        if expected is not None:
            assert index.direct_powered_point(0) == expected
    finally:
        projection.close()
