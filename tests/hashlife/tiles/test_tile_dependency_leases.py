"""Causal result pins retain every exact request dependency per application."""

from __future__ import annotations

import gc
import subprocess
import sys
import weakref
from collections.abc import Callable
from pathlib import Path
from typing import TYPE_CHECKING, Never

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.execution.tile_application_authority import (
    TileApplicationRegistry,
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
from tests.support.tile_dependency_assertions import (
    assert_tile_dependency_state,
    capture_tile_dependency_state,
)
from tests.support.tile_kernel import (
    make_tile_from_symbols,
    make_tile_runtime,
    make_tile_runtime_source,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_application import TileApplication
    from number_compiler.hashlife.execution.tile_scheduler import (
        TileScheduler,
    )
    from number_compiler.hashlife.tiles.tile_results import ResultLease
    from number_compiler.hashlife.tiles.tiles import TileArena, TileLease
    from number_compiler.resources.ledger import ResourceLedger


def tile_dependency_request() -> tuple[
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
    ledger, tiles, adapter, action, scheduler, source = make_tile_runtime_source(
        BaseBlockEffect(3), (0, 0, 0, 1)
    )
    dependency = make_tile_from_symbols(tiles, adapter, action, (1, 2))
    boundary = make_tile_from_symbols(tiles, adapter, action, (2, 1))
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


def _application_registry(scheduler: TileScheduler) -> TileApplicationRegistry:
    registry: object = object.__getattribute__(scheduler, "_applications")
    if type(registry) is not TileApplicationRegistry:
        raise TypeError("tile scheduler omitted its application registry")
    return registry


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
    ) = tile_dependency_request()
    scheduler.pin_causal(application.identity, key, result)
    dependency_id, boundary_id = dependency.tile, boundary.tile
    dependency.close()
    boundary.close()
    assert tiles.resolve(dependency_id).width == 2
    assert tiles.resolve(boundary_id).width == 2
    assert set(scheduler.dependency_leases.records) == {
        (application.identity, dependency_id),
        (application.identity, boundary_id),
    }
    approved, invalid = audit_tile_dependency_leases(
        scheduler.dependency_leases,
        dict(ledger.iter_containers()),
    )
    assert not invalid and id(scheduler.dependency_leases.records) in approved
    payloads = audit_registered_payloads(ledger)
    assert not payloads.unknown_payloads and not payloads.forbidden_future_payloads
    warm = scheduler.results.lookup(key)
    assert warm is not None
    warm.close()
    application.close()
    assert not scheduler.dependency_leases.records
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
    ) = tile_dependency_request()
    original: Callable[[LedgerDict[object, object], object, object], None] = LedgerDict[
        object, object
    ].__setitem__
    dependencies = scheduler.dependency_leases

    def fail_dependency(
        store: LedgerDict[object, object], binding: object, value: object
    ) -> None:
        original(store, binding, value)
        if store is dependencies.records:
            raise RuntimeError("injected causal dependency publication failure")

    with monkeypatch.context() as poison:
        poison.setattr(LedgerDict, "__setitem__", fail_dependency)
        with pytest.raises(RuntimeError, match="causal dependency"):
            scheduler.pin_causal(application.identity, key, result)
    assert (
        not scheduler.audit_snapshot().pins and not scheduler.dependency_leases.records
    )
    assert result.audit_snapshot().closed is True
    pin_owner = scheduler.audit_snapshot().pin_owner
    assert type(pin_owner) is int
    for owner in (pin_owner, scheduler.dependency_leases.owner):
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
    scheduler.pin_causal(application.identity, root_key, root)
    assert not scheduler.dependency_leases.records
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
    ) = tile_dependency_request()
    scheduler.pin_causal(application.identity, key, result)
    binding = next(iter(scheduler.dependency_leases.records))
    lease = scheduler.dependency_leases.records.pop(binding)
    scheduler.dependency_leases.records[(True, binding[1])] = lease
    _, invalid = audit_tile_dependency_leases(
        scheduler.dependency_leases,
        dict(ledger.iter_containers()),
    )
    assert invalid
    scheduler.dependency_leases.records.pop((True, binding[1]))
    scheduler.dependency_leases.records[binding] = lease
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
    ) = tile_dependency_request()
    original = ledger.reserve

    def reject_pin(owner: int, *, entries: int = 0, nodes: int = 0) -> None:
        if owner == scheduler.audit_snapshot().pin_owner:
            raise RuntimeError("injected causal pin reservation failure")
        original(owner, entries=entries, nodes=nodes)

    monkeypatch.setattr(ledger, "reserve", reject_pin)
    with pytest.raises(RuntimeError, match="causal pin reservation"):
        scheduler.pin_causal(application.identity, key, result)
    assert result.audit_snapshot().closed is True
    assert (
        not scheduler.audit_snapshot().pins and not scheduler.dependency_leases.records
    )
    application.close()
    boundary.close()
    dependency.close()
    source.close()


def test_dependency_rollback_preflights_all_bindings_before_mutation() -> None:
    (
        ledger,
        tiles,
        scheduler,
        source,
        dependency,
        boundary,
        application,
        _key,
        result,
    ) = tile_dependency_request()
    dependencies = scheduler.dependency_leases
    batch = dependencies.acquire(
        application.identity,
        (dependency.tile, boundary.tile),
    )
    first, second = batch.bindings
    missing = dependencies.records.pop(second)
    snapshot = capture_tile_dependency_state(ledger, tiles, dependencies)

    with pytest.raises(ValueError, match="lost a binding"):
        dependencies.rollback(batch)

    assert_tile_dependency_state(snapshot, ledger, tiles, dependencies)
    assert dependencies.records[first].tile == first[1]

    dependencies.records[second] = missing
    dependencies.rollback(batch)
    assert not dependencies.records
    result.close()
    application.close()
    boundary.close()
    dependency.close()
    source.close()


def test_dependency_rollback_rejects_batch_from_another_owner() -> None:
    from number_compiler.resources.tile_dependency_leases import TileDependencyLeases

    (
        _ledger,
        tiles,
        scheduler,
        source,
        dependency,
        boundary,
        application,
        _key,
        result,
    ) = tile_dependency_request()
    local = scheduler.dependency_leases
    foreign = TileDependencyLeases(
        scheduler.ledger,
        tiles,
        "foreign-causal-inputs",
        _application_registry(scheduler),
    )
    local_batch = local.acquire(application.identity, (dependency.tile,))
    foreign_batch = foreign.acquire(application.identity, (dependency.tile,))

    with pytest.raises(TypeError, match="issued batch"):
        local.rollback(foreign_batch)

    assert len(local.records) == len(foreign.records) == 1
    local.rollback(local_batch)
    foreign.rollback(foreign_batch)
    result.close()
    application.close()
    boundary.close()
    dependency.close()
    source.close()


def test_stale_dependency_batch_cannot_close_reacquired_binding() -> None:
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
    ) = tile_dependency_request()
    dependencies = scheduler.dependency_leases
    first = dependencies.acquire(application.identity, (dependency.tile,))
    dependencies.rollback(first)
    replacement = dependencies.acquire(application.identity, (dependency.tile,))

    with pytest.raises(ValueError, match="lost a binding"):
        dependencies.rollback(first)

    current = dependencies.records[replacement.bindings[0]]
    assert current is replacement.leases[0]
    assert not current.audit_snapshot().closed
    dependencies.rollback(replacement)
    result.close()
    application.close()
    boundary.close()
    dependency.close()
    source.close()


def test_batch_allocation_failure_rolls_back_acquired_leases(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.resources.tile_dependency_leases as dependency_module

    (
        ledger,
        tiles,
        scheduler,
        source,
        dependency,
        boundary,
        application,
        _key,
        result,
    ) = tile_dependency_request()
    dependencies = scheduler.dependency_leases
    snapshot = capture_tile_dependency_state(ledger, tiles, dependencies)

    def fail_batch(*_args: object) -> Never:
        raise MemoryError("injected dependency batch allocation failure")

    monkeypatch.setattr(dependency_module, "DependencyLeaseBatch", fail_batch)
    with pytest.raises(MemoryError, match="batch allocation"):
        dependencies.acquire(application.identity, (dependency.tile, boundary.tile))

    assert_tile_dependency_state(snapshot, ledger, tiles, dependencies)
    result.close()
    application.close()
    boundary.close()
    dependency.close()
    source.close()


def test_tile_lease_allocation_failure_publishes_no_lease(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.hashlife.tiles.tiles as tile_module

    (
        ledger,
        tiles,
        scheduler,
        source,
        dependency,
        boundary,
        application,
        _key,
        result,
    ) = tile_dependency_request()
    dependencies = scheduler.dependency_leases
    snapshot = capture_tile_dependency_state(
        ledger,
        tiles,
        dependencies,
        include_tile_state=True,
        include_counters=True,
    )

    def fail_lease(*_args: object) -> Never:
        raise MemoryError("injected tile lease allocation failure")

    with monkeypatch.context() as allocation_failure:
        allocation_failure.setattr(tile_module, "TileLease", fail_lease)
        with pytest.raises(MemoryError, match="tile lease allocation"):
            dependencies.acquire(
                application.identity,
                (dependency.tile, boundary.tile),
            )

    assert_tile_dependency_state(snapshot, ledger, tiles, dependencies)
    assert not dependencies.records

    original_bump = ledger.bump

    def fail_after_acquisition_bump(counter: str, amount: int = 1) -> None:
        original_bump(counter, amount)
        if counter == "tile_lease_acquisitions":
            raise MemoryError("injected tile acquisition metric failure")

    with monkeypatch.context() as metric_failure:
        metric_failure.setattr(ledger, "bump", fail_after_acquisition_bump)
        with pytest.raises(MemoryError, match="metric failure"):
            dependencies.acquire(
                application.identity,
                (dependency.tile, boundary.tile),
            )

    assert_tile_dependency_state(snapshot, ledger, tiles, dependencies)
    assert not dependencies.records
    result.close()
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
    ) = tile_dependency_request()

    def forbidden() -> Never:
        raise AssertionError("causal pin scanned every execution root")

    monkeypatch.setattr(scheduler.ledger, "iter_execution_roots", forbidden)
    scheduler.pin_causal(application.identity, key, result)
    assert (
        application.identity,
        dependency.tile,
    ) in scheduler.dependency_leases.records
    alphabet = scheduler.tiles.resolve(dependency.tile).alphabet
    _view, concat_lease = concat_cached_boundary_views(
        scheduler.results,
        alphabet,
        BoundaryTileView(dependency.tile, 0, 2),
        BoundaryTileView(boundary.tile, 0, 2),
        dependencies=scheduler.dependency_leases,
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
    ) = tile_dependency_request()
    result.close()
    for alias in (True, False, 0.0, -1):
        with pytest.raises(ValueError, match="invalid scoped identity"):
            scheduler.application_by_id(alias)
    application.close()
    boundary.close()
    dependency.close()
    source.close()


def test_application_registry_weak_binding_expires_and_reconciles() -> None:
    ledger, tiles, adapter, action, scheduler = make_tile_runtime(BaseBlockEffect(3))
    with make_tile_from_symbols(tiles, adapter, action, (0, 0, 0, 1)) as source:
        lease_entries = ledger.inventory()[tiles.lease_owner].entries
        application = scheduler.application(
            action,
            source.tile,
            adapter.initial_ports(action),
            adapter.wiring(action),
        )
        application.complete()
        root = application.audit_snapshot().root_lease
        assert root is not None
        identity = application.identity
        saved = weakref.ref(application)
        assert identity in _application_registry(scheduler).records
        del application
        gc.collect()
        assert saved() is None
        assert root is not None and root.audit_snapshot().closed is True
        _assert_application_retired(ledger, scheduler, identity)
        _assert_application_observation_empty(ledger, scheduler)
        assert ledger.inventory()[tiles.lease_owner].entries == lease_entries


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
    ) = tile_dependency_request()
    scheduler.pin_causal(application.identity, key, result)
    identity = application.identity
    saved = weakref.ref(application)
    del application
    gc.collect()
    assert saved() is None
    assert result.audit_snapshot().closed is True
    assert not scheduler.audit_snapshot().pins
    assert not scheduler.dependency_leases.records
    _assert_application_retired(ledger, scheduler, identity)
    boundary.close()
    dependency.close()
    source.close()


def test_application_registry_failed_publication_rolls_back(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, tiles, adapter, action, scheduler = make_tile_runtime(BaseBlockEffect(3))
    with make_tile_from_symbols(tiles, adapter, action, (0, 0, 0, 1)) as source:
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
        original: Callable[[LedgerDict[object, object], object, object], None] = (
            LedgerDict[object, object].__setitem__
        )
        registry = _application_registry(scheduler)

        def fail_registry(
            store: LedgerDict[object, object], binding: object, value: object
        ) -> None:
            original(store, binding, value)
            if store is registry.records:
                raise RuntimeError("injected application registry failure")

        monkeypatch.setattr(LedgerDict, "__setitem__", fail_registry)
        with pytest.raises(RuntimeError, match="application registry"):
            scheduler.application(
                action,
                source.tile,
                ports,
                wiring,
            )
        assert not _application_registry(scheduler).records
        account = ledger.inventory()[_application_registry(scheduler).owner]
        assert (account.entries, account.nodes) == (0, 0)
        _assert_application_observation_empty(ledger, scheduler)
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
    ledger, tiles, adapter, action, scheduler = make_tile_runtime(BaseBlockEffect(3))
    with (
        make_tile_from_symbols(tiles, adapter, action, (0, 0, 0, 1)) as source,
        scheduler.application(
            action,
            source.tile,
            adapter.initial_ports(action),
            adapter.wiring(action),
        ) as application,
    ):
        registry = _application_registry(scheduler)
        approved, invalid = scheduler.audit_application_registry(
            dict(ledger.iter_containers())
        )
        assert not invalid
        assert id(registry.records) in approved
        reference = registry.records.pop(application.identity)
        registry.records[True] = reference
        _, invalid = scheduler.audit_application_registry(
            dict(ledger.iter_containers())
        )
        assert invalid
        registry.records.pop(True)
        registry.records[application.identity] = reference


def test_application_cleanup_delete_failure_is_retryable(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, tiles, adapter, action, scheduler = make_tile_runtime(BaseBlockEffect(3))
    with make_tile_from_symbols(tiles, adapter, action, (0, 0, 0, 1)) as source:
        application = scheduler.application(
            action,
            source.tile,
            adapter.initial_ports(action),
            adapter.wiring(action),
        )
        identity = application.identity
        original: Callable[[LedgerDict[object, object], object], None] = LedgerDict[
            object, object
        ].__delitem__
        registry = _application_registry(scheduler)
        failed = False

        def fail_once(store: LedgerDict[object, object], key: object) -> None:
            nonlocal failed
            original(store, key)
            if store is registry.records and not failed:
                failed = True
                raise RuntimeError("injected cleanup deletion failure")

        with monkeypatch.context() as poison:
            poison.setattr(LedgerDict, "__delitem__", fail_once)
            with pytest.raises(RuntimeError, match="cleanup deletion"):
                application.close()
        assert application.audit_snapshot().closed is False
        assert identity in _application_registry(scheduler).records
        assert application.source == source.tile
        application.close()
        _assert_application_retired(ledger, scheduler, identity)


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
    ) = tile_dependency_request()
    scheduler.pin_causal(application.identity, key, result)
    binding = next(iter(scheduler.audit_snapshot().pins))
    original: Callable[[LedgerDict[object, object], object], None] = LedgerDict[
        object, object
    ].__delitem__
    failed = False

    def fail_once(store: LedgerDict[object, object], key_value: object) -> None:
        nonlocal failed
        original(store, key_value)
        if store is scheduler.audit_snapshot().pin_store and not failed:
            failed = True
            raise RuntimeError("injected pin deletion failure")

    with monkeypatch.context() as poison:
        poison.setattr(LedgerDict, "__delitem__", fail_once)
        with pytest.raises(RuntimeError, match="pin deletion"):
            application.close()
    assert binding in scheduler.audit_snapshot().pins
    assert result.audit_snapshot().closed is False
    assert application.source == source.tile
    application.close()
    assert (
        not scheduler.audit_snapshot().pins and not scheduler.dependency_leases.records
    )
    boundary.close()
    dependency.close()
    source.close()


def test_unclosed_application_shutdown_emits_no_weakref_cleanup_error() -> None:
    script = """
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from tests.support.tile_kernel import make_tile_runtime, make_tile_from_symbols

_ledger, tiles, adapter, action, scheduler = make_tile_runtime(BaseBlockEffect(3))
source = make_tile_from_symbols(tiles, adapter, action, (0, 0, 0, 1))
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
    )
    assert observed.returncode == 0, observed.stderr
    assert "Exception ignored in:" not in observed.stderr
    assert "ImportError" not in observed.stderr


def _assert_application_account_empty(
    ledger: ResourceLedger, scheduler: TileScheduler
) -> None:
    account = ledger.inventory()[_application_registry(scheduler).owner]
    assert (account.entries, account.nodes) == (0, 0)


def _assert_application_retired(
    ledger: ResourceLedger, scheduler: TileScheduler, identity: object
) -> None:
    assert identity not in _application_registry(scheduler).records
    _assert_application_account_empty(ledger, scheduler)


def _assert_application_observation_empty(
    ledger: ResourceLedger, scheduler: TileScheduler
) -> None:
    account = ledger.inventory()[_application_registry(scheduler).owner]
    assert (account.observed_entries, account.observed_nodes) == (0, 0)
