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


def test_composed_action_applies_to_recursive_source_and_publishes_complete_target(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Generic temporal cutover must not descend into temporal children.

    Build a recursive first-child source occurrence under a larger parent, then
    apply a still-composite child action to that occurrence.  The live adapter
    must publish the complete target directly through ``apply_composite`` even
    when every chronological fallback hook is poisoned.
    """
    from typing import Never

    from number_compiler.arithmetic.fields.skew_transfer import (
        integer_dyadic_fiber_action,
    )

    ledger = ResourceLedger()
    workspace = CollatzPhysicalImageWorkspace(ledger, 27, 0)
    parent_action = workspace._action(514)
    children = workspace.action_node(parent_action).children
    assert children is not None
    before, after = children
    assert workspace.action_node(before).width == 512
    assert workspace.action_node(before).children is not None

    source_type = workspace.sources[workspace.root_source.local_id].__class__
    parent_source = workspace._append_source(
        source_type(27, 514, 0, None, None, None, 0, True)
    )
    core = workspace.scheduler._source_image_core()
    parent_origin = core._origin(workspace, parent_source)
    child_source = workspace.first_child_source(
        parent_action,
        core.view(parent_origin),
        before,
        after,
    )
    child_node = workspace.source_node(child_source)
    assert child_node.parent == parent_source
    assert child_node.parent_action == parent_action
    assert child_node.side == 1

    primitive_before = ledger.counters.get("source_image_primitive_applications", 0)
    chronology_before = ledger.counters.get(
        "source_image_chronological_compositions", 0
    )

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError(
            "generic Collatz composite apply reopened temporal descent"
        )

    monkeypatch.setattr(workspace, "apply_primitive", forbidden)
    monkeypatch.setattr(workspace, "first_child_source", forbidden)
    monkeypatch.setattr(workspace, "second_child_source", forbidden)
    monkeypatch.setattr(workspace, "compose_chronological", forbidden)

    image = workspace.scheduler.source_image(workspace, child_source, before)
    view = core.view(image)
    assert view.binding.source == child_source
    assert view.binding.action == before
    payload = view.payload
    summary = workspace.image_node(payload).summary  # type: ignore[arg-type]
    chart = integer_dyadic_fiber_action(
        summary.transfer, child_node.residue, child_node.precision
    )
    actual = chart.addend + chart.multiplier * child_node.lift
    expected = _reference(27, 512)[0]
    assert actual == expected
    assert summary.width == 512
    assert ledger.counters.get("source_image_composite_applications", 0) == 1
    assert (
        ledger.counters.get("source_image_primitive_applications", 0)
        == primitive_before
    )
    assert (
        ledger.counters.get("source_image_chronological_compositions", 0)
        == chronology_before
    )
    assert (
        ledger.counters.get("collatz_physical_composite_cutover_publications", 0) >= 1
    )


def test_saturated_support_demand_recovers_after_budget_refusal() -> None:
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )
    from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm

    steps = 257
    seed = (1 << 256) | 0xABCD12345
    term = PoweredCollatzTerm(seed, steps)
    term.digit(0)
    workspace = term._workspace
    assert workspace is not None
    assert len(workspace.support) == 1
    before = (term._ledger.nodes, term._ledger.entries)
    term._ledger.max_nodes = term._ledger.nodes + 3
    try:
        with pytest.raises(BlockContextBudgetExceeded):
            list(workspace.segments())
    finally:
        term._ledger.max_nodes = None
    assert (term._ledger.nodes, term._ledger.entries) == before
    assert len(workspace.support) == 1
    assert not workspace.macros and not workspace.macro_stack
    assert not workspace.balanced_stack and not workspace.demanded_support
    emitted = sum(width for _, width, _ in workspace.segments())
    assert emitted == steps
    assert workspace.demanded_support[workspace.root_payload]
