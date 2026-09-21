"""Source-cylinder audit validates stores without executing their methods."""

from dataclasses import replace
from typing import Never

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.sequences.reverse_add.source_images import (
    ReverseCylinderConstructionUnavailable,
    ReverseSourceImageWorkspace,
)


@pytest.mark.parametrize("steps", [0, 1, 2, 20])
def test_audit_is_readonly_with_runtime_callbacks_poisoned(
    steps: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    ledger = ResourceLedger()
    workspace = ReverseSourceImageWorkspace(ledger, (1 << 260) + 196, steps)
    if steps < 3:
        workspace.width()
    else:
        with pytest.raises(ReverseCylinderConstructionUnavailable):
            workspace.width()

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("payload audit executed a runtime method")

    monkeypatch.setattr(type(workspace.actions), "source", forbidden)
    monkeypatch.setattr(type(workspace.actions), "node", forbidden)
    before = dict(ledger.counters)
    report = audit_registered_payloads(ledger)
    assert report.forbidden_future_payloads == 0
    assert report.unknown_payloads == 0
    assert dict(ledger.counters) == before


def test_forged_action_chronology_is_rejected() -> None:
    ledger = ResourceLedger()
    workspace = ReverseSourceImageWorkspace(ledger, 196, 20)
    action = workspace.root_action
    node = workspace.actions._nodes[action.local_id]
    workspace.actions._nodes[action.local_id] = replace(node, steps=node.steps + 1)
    assert audit_registered_payloads(ledger).forbidden_future_payloads > 0


def test_replaced_original_source_is_rejected() -> None:
    ledger = ResourceLedger()
    workspace = ReverseSourceImageWorkspace(ledger, 196, 1)
    source = workspace.actions._sources[workspace.source.local_id].exact
    object.__setattr__(source, "digits", (9, 9, 9))
    assert audit_registered_payloads(ledger).forbidden_future_payloads > 0


def test_foreign_cached_image_is_rejected() -> None:
    ledger = ResourceLedger()
    workspace = ReverseSourceImageWorkspace(ledger, 196, 1)
    other = ReverseSourceImageWorkspace(ResourceLedger(), 89, 1)
    workspace.width()
    other.width()
    workspace._image = other._image
    assert audit_registered_payloads(ledger).forbidden_future_payloads > 0


def test_foreign_child_action_is_rejected() -> None:
    ledger = ResourceLedger()
    workspace = ReverseSourceImageWorkspace(ledger, 196, 2)
    other = ReverseSourceImageWorkspace(ResourceLedger(), 89, 1)
    action = workspace.root_action
    node = workspace.actions._nodes[action.local_id]
    workspace.actions._nodes[action.local_id] = replace(
        node, before=other.actions.primitive
    )
    assert audit_registered_payloads(ledger).forbidden_future_payloads > 0


def test_foreign_spatial_port_projection_is_rejected_by_audit_and_runtime() -> None:
    ledger = ResourceLedger()
    workspace = ReverseSourceImageWorkspace(ledger, 196, 2)
    other = ReverseSourceImageWorkspace(ledger, 89, 2)
    workspace.width()
    other.width()
    workspace.adapter._ports = other.adapter._ports
    assert audit_registered_payloads(ledger).forbidden_future_payloads > 0
    with pytest.raises(ValueError, match="foreign"):
        workspace.digit(0)


def test_invalid_spatial_interval_geometry_is_rejected_without_evaluation() -> None:
    from number_compiler.arithmetic.carry.carry_monoid import CarryFn

    ledger = ResourceLedger()
    workspace = ReverseSourceImageWorkspace(ledger, 196, 2)
    workspace.width()
    ports = workspace.adapter._ports
    assert ports is not None
    ports._cache[(2, 0, 1024)] = CarryFn.ID
    assert audit_registered_payloads(ledger).forbidden_future_payloads > 0
