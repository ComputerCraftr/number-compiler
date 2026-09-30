"""All result pin routes authenticate the live application before lookup."""

from tests.support.assertions import assert_rejected_atomically


from typing import cast

import pytest

from tests.hashlife.tiles.test_tile_dependency_leases import _request


@pytest.mark.parametrize("alias", (True, False, 0.0, -1, 999))
@pytest.mark.parametrize("warm", (False, True))
def test_result_pin_rejects_application_alias_before_mutation(
    alias: object, warm: bool
) -> None:
    ledger, _tiles, scheduler, source, dependency, boundary, app, key, result = (
        _request()
    )
    try:
        if warm:
            scheduler._pin(app.identity, key, result)
            fresh = scheduler.results.lookup(key)
            assert fresh is not None
            result = fresh
        assert_rejected_atomically(
            ledger, lambda: scheduler._pin(cast(int, alias), key, result), ValueError
        )
        assert result.result.output is not None
    finally:
        result.close()
        app.close()
        boundary.close()
        dependency.close()
        source.close()


def test_result_pin_rejects_retired_application_and_preserves_borrowed_lease() -> None:
    ledger, _tiles, scheduler, source, dependency, boundary, app, key, result = (
        _request()
    )
    app.close()
    before = ledger.snapshot()
    try:
        with pytest.raises(ValueError):
            scheduler._pin(app.identity, key, result)
        assert ledger.snapshot() == before
        assert result.result.output is not None
    finally:
        result.close()
        boundary.close()
        dependency.close()
        source.close()


def test_warm_causal_pin_does_not_enumerate_the_dependency_store(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from collections.abc import Iterator
    from typing import TypeVar

    from number_compiler.resources.stores import LedgerDict

    key_type = TypeVar("key_type")
    value_type = TypeVar("value_type")
    _ledger, _tiles, scheduler, source, dependency, boundary, app, key, result = (
        _request()
    )
    scheduler._pin_causal(app.identity, key, result)
    fresh = scheduler.results.lookup(key)
    assert fresh is not None
    original = LedgerDict.__iter__

    def bounded_iteration(
        store: LedgerDict[key_type, value_type],
    ) -> Iterator[key_type]:
        if store is scheduler._causal_dependencies.records:
            raise AssertionError("warm pin enumerated all retained dependencies")
        return original(store)

    try:
        with monkeypatch.context() as patch:
            patch.setattr(LedgerDict, "__iter__", bounded_iteration)
            scheduler._pin_causal(app.identity, key, fresh)
    finally:
        fresh.close()
        app.close()
        boundary.close()
        dependency.close()
        source.close()


def test_repinning_the_owned_causal_lease_does_not_close_it() -> None:
    _ledger, _tiles, scheduler, source, dependency, boundary, app, key, result = (
        _request()
    )
    try:
        scheduler._pin_causal(app.identity, key, result)
        scheduler._pin_causal(app.identity, key, result)
        assert result.result.output is not None
    finally:
        app.close()
        boundary.close()
        dependency.close()
        source.close()
