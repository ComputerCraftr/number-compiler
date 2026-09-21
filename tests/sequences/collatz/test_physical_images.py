"""Differential checks for the bounded source-only Collatz physical image."""

from __future__ import annotations

import pytest

from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.sequences.collatz.physical_images import (
    CollatzPhysicalImageWorkspace,
)


def _reference(seed: int, steps: int) -> tuple[int, int, tuple[int, ...]]:
    value = seed
    odd = 0
    branches: list[int] = []
    for _ in range(steps):
        if value & 1:
            branches.append(1)
            odd += 1
            value = 3 * value + 1
        else:
            branches.append(0)
            value //= 2
    return value, odd, tuple(branches)


@pytest.mark.parametrize("steps", (0, 1, 2, 7, 64, 65, 129, 257))
def test_source_image_matches_fixed_physical_recurrence(steps: int) -> None:
    expected, odd, branches = _reference(27, steps)
    workspace = CollatzPhysicalImageWorkspace(ResourceLedger(), 27, steps)
    assert workspace.endpoint() == expected
    assert workspace.odd_steps() == odd
    actual: list[int] = []
    for start, width, word in workspace.segments():
        assert start == len(actual)
        actual.extend((word >> offset) & 1 for offset in range(width))
    assert tuple(actual) == branches
    assert workspace.scheduler._source_only


def test_composed_images_do_not_construct_a_causal_engine(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("physical source images invoked the causal engine")

    monkeypatch.setattr(CausalTileEngine, "__init__", forbidden)
    workspace = CollatzPhysicalImageWorkspace(ResourceLedger(), 27, 1024)
    assert workspace.endpoint() == _reference(27, 1024)[0]
    assert workspace.ledger.counters["collatz_physical_action_compositions"] > 0
    assert workspace.ledger.counters["collatz_physical_composition_operand_bits"] > 0


def test_leaf_kernel_rejects_an_unbounded_primitive() -> None:
    workspace = CollatzPhysicalImageWorkspace(ResourceLedger(), 27, 0)
    action = workspace._append_action(
        workspace.actions[workspace.identity.local_id].__class__(65, None)
    )
    source = workspace._append_source(
        workspace.sources[workspace.root_source.local_id].__class__(
            27, 65, 0, None, None, None, 0
        )
    )
    origin = workspace.scheduler._source_image_core()._origin(workspace, source)
    with pytest.raises(ValueError, match="bounded leaf"):
        workspace.apply_primitive(
            action, workspace.scheduler._source_image_core().view(origin)
        )


def test_publication_uses_ledger_owned_support_and_reports_policy_audit() -> None:
    workspace = CollatzPhysicalImageWorkspace(ResourceLedger(), 27, 130)
    report = audit_registered_payloads(workspace.ledger)
    assert report.unknown_payloads == 0
    assert report.forbidden_future_payloads == 0
    support = next(
        item
        for item in workspace.ledger.inventory()
        if item.role == "dyadic_return_support"
    )
    assert support.entries == len(workspace.support)
    workspace.validate_source(workspace.root_source)
    workspace.validate_action(workspace.root_action)
    workspace.validate_payload(workspace.root_payload)
