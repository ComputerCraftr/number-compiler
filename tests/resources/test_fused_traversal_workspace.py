"""Budget and cleanup checks for fused-interface traversal scratch."""

from __future__ import annotations

from typing import cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.resources.fused_traversal_inventory import (
    audit_fused_traversal_workspace,
)
from number_compiler.resources.fused_traversal_workspace import (
    FusedTraversalWorkspace,
    fused_traversal_workspace_owner_names,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerList
from number_compiler.resources.tile_runtime_inventory import audit_tile_runtime
from tests.support.tile_kernel import make_tile_from_symbols, make_tile_runtime


def test_fused_workspace_name_collision_preflights_without_inventory(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    prefix = "fused-name-collision"
    owner_names = fused_traversal_workspace_owner_names(prefix)
    owner = ledger.register(owner_names[1], "fused_interface_workspace")
    ledger.make_dict(owner)
    before = ledger.owner_count

    def forbidden_inventory(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("workspace setup must not inventory ledger stores")

    monkeypatch.setattr(ledger, "inventory", forbidden_inventory)
    with pytest.raises(ValueError, match="already registered"):
        FusedTraversalWorkspace(ledger, prefix)
    assert ledger.owner_count == before


def test_fused_workspace_rejects_reentry_and_releases_after_failure() -> None:
    ledger = ResourceLedger()
    workspace = FusedTraversalWorkspace(ledger, "test")
    with (
        pytest.raises(RuntimeError, match="already active"),
        workspace.scope(3, 2),
        workspace.scope(0, 2),
    ):
        raise AssertionError("unreachable")
    account = ledger.inventory()[workspace.owner]
    assert workspace.active is False and workspace.nodes == 0
    assert (account.nodes, account.observed_nodes) == (0, 0)
    frame_account = ledger.inventory()[workspace.frame_owner]
    value_account = ledger.inventory()[workspace.value_owner]
    assert (frame_account.entries, frame_account.observed_entries) == (0, 0)
    assert (value_account.entries, value_account.observed_entries) == (0, 0)


def test_fused_workspace_budget_rejects_before_becoming_active() -> None:
    ledger = ResourceLedger(max_nodes=0)
    workspace = FusedTraversalWorkspace(ledger, "test")
    before = ledger.snapshot()
    with pytest.raises(BlockContextBudgetExceeded), workspace.scope(1, 2):
        raise AssertionError("unreachable")
    assert ledger.snapshot() == before
    assert workspace.active is False and workspace.nodes == 0


def test_fused_workspace_rejects_unscoped_and_over_bound_mutation() -> None:
    ledger = ResourceLedger()
    workspace = FusedTraversalWorkspace(ledger, "test")
    with pytest.raises(RuntimeError, match="active scope"):
        workspace.append_frame(object())
    with workspace.scope(0, 2):
        workspace.append_frame(object())
        workspace.append_value(object())
        with pytest.raises(RuntimeError, match="frame bound"):
            workspace.append_frame(object())
        with pytest.raises(RuntimeError, match="value bound"):
            workspace.append_value(object())


def test_fused_workspace_inventory_reconciles_active_exhausted_and_cleanup() -> None:
    ledger, tiles, adapter, primitive, _scheduler = make_tile_runtime(
        BaseBlockEffect(3)
    )
    action = adapter.power(primitive, 2)
    with make_tile_from_symbols(tiles, adapter, primitive, (0, 1)) as source:
        ports = adapter.initial_ports(primitive)
        interface = adapter.fused_interface(
            action,
            source.tile,
            ports,
            adapter.wiring(action),
        )
        workspace = cast(
            FusedTraversalWorkspace,
            object.__getattribute__(adapter, "_fused_workspace"),
        )
        with workspace.scope(1, len(ports)):
            for ready in (False, False, True):
                workspace.append_frame((source.tile, ports, ready))
            workspace.append_value(interface)
            workspace.append_value(interface)
            containers = dict(ledger.iter_containers())
            approved, invalid = audit_fused_traversal_workspace(adapter, containers)
            assert not invalid
            assert id(workspace) in approved
            _, runtime_invalid = audit_tile_runtime(
                ledger,
                containers,
                tuple(ledger.iter_execution_roots()),
            )
            assert not runtime_invalid

        containers = dict(ledger.iter_containers())
        approved, invalid = audit_fused_traversal_workspace(adapter, containers)
        assert not invalid
        assert id(workspace) in approved
        _, runtime_invalid = audit_tile_runtime(
            ledger,
            containers,
            tuple(ledger.iter_execution_roots()),
        )
        assert not runtime_invalid


@pytest.mark.parametrize("owner_name", ["frame_owner", "value_owner", "owner"])
@pytest.mark.parametrize("after_release", [False, True])
def test_cleanup_attempts_every_owner_and_can_retry_release(
    monkeypatch: pytest.MonkeyPatch, owner_name: str, after_release: bool
) -> None:
    ledger = ResourceLedger()
    workspace = FusedTraversalWorkspace(ledger, "release-failure")
    target = {
        "frame_owner": workspace.frame_owner,
        "value_owner": workspace.value_owner,
        "owner": workspace.owner,
    }[owner_name]
    original = ledger.release
    failed = False

    def fail_once(owner: int, entries: int = 0, nodes: int = 0) -> None:
        nonlocal failed
        if owner == target and not failed:
            failed = True
            if after_release:
                original(owner, entries=entries, nodes=nodes)
            raise RuntimeError("injected cleanup failure")
        original(owner, entries=entries, nodes=nodes)

    with monkeypatch.context() as patch:
        patch.setattr(ledger, "release", fail_once)
        with pytest.raises(RuntimeError, match="injected") as raised:
            with workspace.scope(1, 2):
                workspace.append_frame(object())
                workspace.append_value(object())
                raise ValueError("original body failure")
    assert not workspace.frames and not workspace.values
    assert not workspace.active
    # Keep the body failure discoverable, even when cleanup also fails.
    error: BaseException | None = raised.value
    chain: list[str] = []
    while error is not None:
        chain.append(str(error))
        error = error.__cause__ or error.__context__
    assert "original body failure" in chain
    workspace.dispose()
    workspace.dispose()
    assert (ledger.entries, ledger.nodes) == (0, 0)


def test_pop_release_failure_leaves_no_untracked_entry_charge(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    workspace = FusedTraversalWorkspace(ledger, "pop-failure")
    original = ledger.release
    failed = False

    def fail_once(owner: int, entries: int = 0, nodes: int = 0) -> None:
        nonlocal failed
        if owner == workspace.value_owner and not failed:
            failed = True
            raise RuntimeError("injected pop release failure")
        original(owner, entries=entries, nodes=nodes)

    with monkeypatch.context() as patch:
        patch.setattr(ledger, "release", fail_once)
        with pytest.raises(RuntimeError, match="pop release"), workspace.scope(0, 0):
            workspace.append_value(object())
            workspace.pop_value()
    assert (ledger.entries, ledger.nodes) == (0, 0)
    with pytest.raises(RuntimeError, match="active scope"):
        workspace.pop_value()
    workspace.dispose()


def test_partial_clear_failure_still_clears_other_stack(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    workspace = FusedTraversalWorkspace(ledger, "partial-clear")
    original = LedgerList[object].clear

    def fail_clear(store: LedgerList[object]) -> None:
        original(store)
        if store is workspace.frames:
            raise RuntimeError("injected partial clear failure")

    with monkeypatch.context() as patch:
        patch.setattr(LedgerList, "clear", fail_clear)
        with pytest.raises(RuntimeError, match="partial clear"), workspace.scope(0, 0):
            workspace.append_frame(object())
            workspace.append_value(object())
    assert not workspace.frames and not workspace.values
    assert (ledger.entries, ledger.nodes) == (0, 0)
    workspace.dispose()


@pytest.mark.parametrize("after_pop_release", [False, True])
def test_caught_pop_error_keeps_active_store_accounting_consistent(
    monkeypatch: pytest.MonkeyPatch, after_pop_release: bool
) -> None:
    ledger = ResourceLedger()
    workspace = FusedTraversalWorkspace(ledger, "caught-pop")
    original = ledger.release

    def reject_pop(owner: int, entries: int = 0, nodes: int = 0) -> None:
        if after_pop_release:
            original(owner, entries=entries, nodes=nodes)
        raise RuntimeError("caught pop error")

    with workspace.scope(1, 0):
        token = object()
        workspace.append_value(token)
        with monkeypatch.context() as patch:
            patch.setattr(ledger, "release", reject_pop)
            with pytest.raises(RuntimeError, match="caught pop"):
                workspace.pop_value()
        expected = 0 if after_pop_release else 1
        assert len(workspace.values) == expected
        assert ledger.account_status(workspace.value_owner).entries == expected
        workspace.append_value(token)
        assert workspace.pop_value() is token
    workspace.dispose()
    assert (ledger.entries, ledger.nodes) == (0, 0)


@pytest.mark.parametrize("after_mark", [False, True])
def test_partial_disposal_cannot_reenter_but_can_finish(
    monkeypatch: pytest.MonkeyPatch, after_mark: bool
) -> None:
    ledger = ResourceLedger()
    workspace = FusedTraversalWorkspace(ledger, "partial-disposal")
    original = ledger.mark_disposed

    def reject_value_owner(owner: int) -> None:
        if owner == workspace.value_owner:
            if after_mark:
                original(owner)
            raise RuntimeError("injected owner retirement failure")
        original(owner)

    with monkeypatch.context() as patch:
        patch.setattr(ledger, "mark_disposed", reject_value_owner)
        with pytest.raises(RuntimeError, match="retirement"):
            workspace.dispose()
    assert ledger.account_status(workspace.frame_owner).disposed
    with pytest.raises(RuntimeError, match="closing"), workspace.scope(1, 0):
        raise AssertionError("partially disposed scope reopened")
    workspace.dispose()
    assert all(
        ledger.account_status(owner).disposed
        for owner in (workspace.frame_owner, workspace.value_owner, workspace.owner)
    )
