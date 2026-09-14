"""Causal result pins retain every exact request dependency per application."""

from __future__ import annotations

import gc
import subprocess
import sys
import weakref
from collections.abc import Hashable
from pathlib import Path
from typing import TYPE_CHECKING, Never, TypeVar, cast

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.execution.tile_application_authority import (
    audit_tile_application_registry,
)
from number_compiler.hashlife.tiles.tile_boundaries import (
    BoundaryTileOperands,
    BoundaryTileView,
)
from number_compiler.hashlife.tiles.tile_boundary_concat_memo import (
    concat_cached_boundary_views,
)
from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.resources.stores import LedgerDict
from number_compiler.resources.tile_dependency_leases import (
    audit_tile_dependency_leases,
)
from tests.arithmetic.contracts.test_tile_kernel import _runtime, _tile

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_scheduler import (
        TileApplication,
        TileScheduler,
    )
    from number_compiler.hashlife.tiles.tile_results import ResultLease
    from number_compiler.hashlife.tiles.tiles import TileArena, TileLease
    from number_compiler.resources.ledger import ResourceLedger


def _request() -> tuple[
    ResourceLedger,
    TileArena,
    TileScheduler,
    TileLease,
    TileLease,
    TileLease,
    TileApplication,
    PoweredResultKey,
    ResultLease,
]:
    ledger, tiles, adapter, action, scheduler = _runtime(BaseBlockEffect(3))
    source = _tile(tiles, adapter, action, (0, 0, 0, 1))
    dependency = _tile(tiles, adapter, action, (1, 2))
    boundary = _tile(tiles, adapter, action, (2, 1))
    wiring = adapter.wiring(action)
    operands = BoundaryTileOperands(
        BoundaryTileView(boundary.tile, -2, 2),
        None,
    )
    key = PoweredResultKey(
        action,
        dependency.tile,
        adapter.initial_ports(action),
        wiring,
        operands,
    )
    result = scheduler.complete(
        action,
        dependency.tile,
        key.ports,
        wiring,
        boundaries=operands,
    )
    application = scheduler.application(
        action,
        source.tile,
        adapter.initial_ports(action),
        wiring,
    )
    return (
        ledger,
        tiles,
        scheduler,
        source,
        dependency,
        boundary,
        application,
        key,
        result,
    )


def test_causal_pin_retains_inputs_and_boundaries_until_application_close() -> None:
    (
        ledger,
        tiles,
        scheduler,
        source,
        dependency,
        boundary,
        application,
        key,
        result,
    ) = _request()
    scheduler._pin_causal(application.identity, key, result)
    dependency_id, boundary_id = dependency.tile, boundary.tile
    dependency.close()
    boundary.close()
    assert tiles.resolve(dependency_id).width == 2
    assert tiles.resolve(boundary_id).width == 2
    assert set(scheduler._causal_dependencies.records) == {
        (application.identity, dependency_id),
        (application.identity, boundary_id),
    }
    approved, invalid = audit_tile_dependency_leases(
        scheduler._causal_dependencies,
        dict(ledger.iter_containers()),
    )
    assert not invalid and id(scheduler._causal_dependencies.records) in approved
    payloads = audit_registered_payloads(ledger)
    assert not payloads.unknown_payloads and not payloads.forbidden_future_payloads
    warm = scheduler.results.lookup(key)
    assert warm is not None
    warm.close()
    application.close()
    assert not scheduler._causal_dependencies.records
    with pytest.raises(ValueError, match="stale or unpublished"):
        tiles.resolve(dependency_id)
    source.close()


def test_causal_pin_deduplicates_application_source_and_rolls_back(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    (
        ledger,
        _tiles,
        scheduler,
        source,
        dependency,
        boundary,
        application,
        key,
        result,
    ) = _request()
    from number_compiler.resources.stores import LedgerDict

    original = LedgerDict.__setitem__

    def fail_dependency(
        store: LedgerDict[KeyT, ValueT], binding: KeyT, value: ValueT
    ) -> None:
        original(store, binding, value)
        if store is scheduler._causal_dependencies.records:
            raise RuntimeError("injected causal dependency publication failure")

    with monkeypatch.context() as poison:
        poison.setattr(LedgerDict, "__setitem__", fail_dependency)
        with pytest.raises(RuntimeError, match="causal dependency"):
            scheduler._pin_causal(application.identity, key, result)
    assert not scheduler._pins and not scheduler._causal_dependencies.records
    assert result._closed is True
    for owner in (scheduler._pin_owner, scheduler._causal_dependencies.owner):
        account = ledger.inventory()[owner]
        assert (account.entries, account.nodes, account.accounting_delta) == (0, 0, 0)

    # A causal root result needs no second lease/slot for the application's
    # already retained immutable source tile.
    root = scheduler.complete(
        key.action,
        application.source,
        key.ports,
        key.wiring,
    )
    root_key = PoweredResultKey(key.action, application.source, key.ports, key.wiring)
    scheduler._pin_causal(application.identity, root_key, root)
    assert not scheduler._causal_dependencies.records
    application.close()
    boundary.close()
    dependency.close()
    source.close()


def test_dependency_inventory_rejects_integer_alias() -> None:
    (
        ledger,
        _tiles,
        scheduler,
        source,
        dependency,
        boundary,
        application,
        key,
        result,
    ) = _request()
    scheduler._pin_causal(application.identity, key, result)
    binding = next(iter(scheduler._causal_dependencies.records))
    lease = scheduler._causal_dependencies.records.pop(binding)
    scheduler._causal_dependencies.records[(True, binding[1])] = lease
    _, invalid = audit_tile_dependency_leases(
        scheduler._causal_dependencies,
        dict(ledger.iter_containers()),
    )
    assert invalid
    scheduler._causal_dependencies.records.pop((True, binding[1]))
    scheduler._causal_dependencies.records[binding] = lease
    application.close()
    boundary.close()
    dependency.close()
    source.close()


def test_causal_pin_reservation_failure_closes_unpublished_result(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    (
        ledger,
        _tiles,
        scheduler,
        source,
        dependency,
        boundary,
        application,
        key,
        result,
    ) = _request()
    original = ledger.reserve

    def reject_pin(owner: int, *, entries: int = 0, nodes: int = 0) -> None:
        if owner == scheduler._pin_owner:
            raise RuntimeError("injected causal pin reservation failure")
        original(owner, entries=entries, nodes=nodes)

    monkeypatch.setattr(ledger, "reserve", reject_pin)
    with pytest.raises(RuntimeError, match="causal pin reservation"):
        scheduler._pin_causal(application.identity, key, result)
    assert result._closed is True
    assert not scheduler._pins and not scheduler._causal_dependencies.records
    application.close()
    boundary.close()
    dependency.close()
    source.close()


def test_application_registry_avoids_execution_root_scans_for_causal_pins(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    (
        _ledger,
        _tiles,
        scheduler,
        source,
        dependency,
        boundary,
        application,
        key,
        result,
    ) = _request()

    def forbidden() -> Never:
        raise AssertionError("causal pin scanned every execution root")

    monkeypatch.setattr(scheduler.ledger, "iter_execution_roots", forbidden)
    scheduler._pin_causal(application.identity, key, result)
    assert (
        application.identity,
        dependency.tile,
    ) in scheduler._causal_dependencies.records
    alphabet = scheduler.tiles.resolve(dependency.tile).alphabet
    _view, concat_lease = concat_cached_boundary_views(
        scheduler.results,
        alphabet,
        BoundaryTileView(dependency.tile, 0, 2),
        BoundaryTileView(boundary.tile, 0, 2),
        dependencies=scheduler._causal_dependencies,
        application=application.identity,
    )
    concat_lease.close()
    application.close()
    boundary.close()
    dependency.close()
    source.close()


def test_application_registry_rejects_numeric_aliases_without_lookup() -> None:
    (
        _ledger,
        _tiles,
        scheduler,
        source,
        dependency,
        boundary,
        application,
        _key,
        result,
    ) = _request()
    result.close()
    for alias in (True, False, 0.0, -1):
        with pytest.raises(ValueError, match="invalid scoped identity"):
            scheduler._applications.application(cast(int, alias))
    application.close()
    boundary.close()
    dependency.close()
    source.close()


def test_application_registry_weak_binding_expires_and_reconciles() -> None:
    ledger, tiles, adapter, action, scheduler = _runtime(BaseBlockEffect(3))
    with _tile(tiles, adapter, action, (0, 0, 0, 1)) as source:
        lease_entries = ledger.inventory()[tiles._lease_owner].entries
        application = scheduler.application(
            action,
            source.tile,
            adapter.initial_ports(action),
            adapter.wiring(action),
        )
        application.complete()
        root = application._root
        assert root is not None
        identity = application.identity
        saved = weakref.ref(application)
        assert identity in scheduler._applications.records
        del application
        gc.collect()
        assert saved() is None
        assert root._closed is True
        assert identity not in scheduler._applications.records
        account = ledger.inventory()[scheduler._applications.owner]
        assert (account.entries, account.nodes) == (0, 0)
        assert (account.observed_entries, account.observed_nodes) == (0, 0)
        assert ledger.inventory()[tiles._lease_owner].entries == lease_entries


def test_abandoned_application_releases_causal_pins_and_dependencies() -> None:
    (
        ledger,
        _tiles,
        scheduler,
        source,
        dependency,
        boundary,
        application,
        key,
        result,
    ) = _request()
    scheduler._pin_causal(application.identity, key, result)
    identity = application.identity
    saved = weakref.ref(application)
    del application
    gc.collect()
    assert saved() is None
    assert result._closed is True
    assert not scheduler._pins
    assert not scheduler._causal_dependencies.records
    assert identity not in scheduler._applications.records
    account = ledger.inventory()[scheduler._applications.owner]
    assert (account.entries, account.nodes) == (0, 0)
    boundary.close()
    dependency.close()
    source.close()


def test_application_registry_failed_publication_rolls_back(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, tiles, adapter, action, scheduler = _runtime(BaseBlockEffect(3))
    with _tile(tiles, adapter, action, (0, 0, 0, 1)) as source:
        ports = adapter.initial_ports(action)
        wiring = adapter.wiring(action)
        key = PoweredResultKey(action, source.tile, ports, wiring)
        prepared = scheduler.results.lookup(key)
        if prepared is not None:
            prepared.close()
        inventory_before = {
            item.owner: (item.role, item.entries, item.nodes)
            for item in ledger.inventory()
        }
        entries_before = ledger.entries
        original = LedgerDict.__setitem__

        def fail_registry(
            store: LedgerDict[KeyT, ValueT], binding: KeyT, value: ValueT
        ) -> None:
            original(store, binding, value)
            if store is scheduler._applications.records:
                raise RuntimeError("injected application registry failure")

        monkeypatch.setattr(LedgerDict, "__setitem__", fail_registry)
        with pytest.raises(RuntimeError, match="application registry"):
            scheduler.application(
                action,
                source.tile,
                ports,
                wiring,
            )
        assert not scheduler._applications.records
        account = ledger.inventory()[scheduler._applications.owner]
        assert (account.entries, account.nodes) == (0, 0)
        assert (account.observed_entries, account.observed_nodes) == (0, 0)
        inventory_after = {
            item.owner: (item.role, item.entries, item.nodes)
            for item in ledger.inventory()
        }
        changed = {
            owner: (inventory_before.get(owner), value)
            for owner, value in inventory_after.items()
            if inventory_before.get(owner) != value
        }
        assert ledger.entries == entries_before, changed


def test_application_registry_inventory_rejects_alias_and_stale_reference() -> None:
    ledger, tiles, adapter, action, scheduler = _runtime(BaseBlockEffect(3))
    with (
        _tile(tiles, adapter, action, (0, 0, 0, 1)) as source,
        scheduler.application(
            action,
            source.tile,
            adapter.initial_ports(action),
            adapter.wiring(action),
        ) as application,
    ):
        approved, invalid = audit_tile_application_registry(
            scheduler._applications,
            dict(ledger.iter_containers()),
        )
        assert not invalid
        assert id(scheduler._applications.records) in approved
        reference = scheduler._applications.records.pop(application.identity)
        scheduler._applications.records[True] = reference
        _, invalid = audit_tile_application_registry(
            scheduler._applications,
            dict(ledger.iter_containers()),
        )
        assert invalid
        scheduler._applications.records.pop(True)
        scheduler._applications.records[application.identity] = reference


def test_application_cleanup_delete_failure_is_retryable(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, tiles, adapter, action, scheduler = _runtime(BaseBlockEffect(3))
    with _tile(tiles, adapter, action, (0, 0, 0, 1)) as source:
        application = scheduler.application(
            action,
            source.tile,
            adapter.initial_ports(action),
            adapter.wiring(action),
        )
        identity = application.identity
        original = LedgerDict.__delitem__
        failed = False

        def fail_once(store: LedgerDict[KeyT, ValueT], key: KeyT) -> None:
            nonlocal failed
            original(store, key)
            if store is scheduler._applications.records and not failed:
                failed = True
                raise RuntimeError("injected cleanup deletion failure")

        with monkeypatch.context() as poison:
            poison.setattr(LedgerDict, "__delitem__", fail_once)
            with pytest.raises(RuntimeError, match="cleanup deletion"):
                application.close()
        assert application._closed is False
        assert identity in scheduler._applications.records
        assert application.source == source.tile
        application.close()
        assert identity not in scheduler._applications.records
        account = ledger.inventory()[scheduler._applications.owner]
        assert (account.entries, account.nodes) == (0, 0)


def test_application_pin_delete_failure_restores_binding_for_retry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    (
        _ledger,
        _tiles,
        scheduler,
        source,
        dependency,
        boundary,
        application,
        key,
        result,
    ) = _request()
    scheduler._pin_causal(application.identity, key, result)
    binding = next(iter(scheduler._pins))
    original = LedgerDict.__delitem__
    failed = False

    def fail_once(store: LedgerDict[KeyT, ValueT], key_value: KeyT) -> None:
        nonlocal failed
        original(store, key_value)
        if store is scheduler._pins and not failed:
            failed = True
            raise RuntimeError("injected pin deletion failure")

    with monkeypatch.context() as poison:
        poison.setattr(LedgerDict, "__delitem__", fail_once)
        with pytest.raises(RuntimeError, match="pin deletion"):
            application.close()
    assert binding in scheduler._pins
    assert result._closed is False
    assert application.source == source.tile
    application.close()
    assert not scheduler._pins and not scheduler._causal_dependencies.records
    boundary.close()
    dependency.close()
    source.close()


def test_unclosed_application_shutdown_emits_no_weakref_cleanup_error() -> None:
    script = """
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from tests.arithmetic.contracts.test_tile_kernel import _runtime, _tile

_ledger, tiles, adapter, action, scheduler = _runtime(BaseBlockEffect(3))
source = _tile(tiles, adapter, action, (0, 0, 0, 1))
application = scheduler.application(
    action,
    source.tile,
    adapter.initial_ports(action),
    adapter.wiring(action),
)
"""
    observed = subprocess.run(
        [sys.executable, "-c", script],
        cwd=Path(__file__).parents[3],
        check=False,
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert observed.returncode == 0, observed.stderr
    assert "Exception ignored in:" not in observed.stderr
    assert "ImportError" not in observed.stderr


KeyT = TypeVar("KeyT", bound=Hashable)
ValueT = TypeVar("ValueT")
