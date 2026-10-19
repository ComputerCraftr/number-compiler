"""Budget and cleanup checks for fused-interface traversal scratch."""

from __future__ import annotations

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
        workspace = adapter._fused_workspace
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
