"""A rejected direct macro leaves an already-live source workspace intact."""

from __future__ import annotations

from collections.abc import Iterable

import pytest

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.hashlife.execution.source_bound_images import SourceImageDemand
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.antihydra.arithmetic_images import (
    AntihydraArithmeticImageWorkspace,
)
from number_compiler.sequences.collatz.physical_images import (
    CollatzPhysicalImageWorkspace,
)


@pytest.mark.parametrize("family,seed", (("collatz", 27), ("antihydra", 8)))
@pytest.mark.parametrize("failure_stage", ("candidate", "publication"))
def test_live_workspace_rolls_back_rejected_balanced_support(
    family: str,
    seed: int,
    failure_stage: str,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger(max_nodes=4096, max_cache_entries=4096)
    workspace: CollatzPhysicalImageWorkspace | AntihydraArithmeticImageWorkspace
    if family == "collatz":
        workspace = CollatzPhysicalImageWorkspace(ledger, seed, 514)
    else:
        workspace = AntihydraArithmeticImageWorkspace(ledger, 514)

    core = workspace.scheduler._source_image_core()
    children = workspace.action_node(workspace.root_action).children
    assert children is not None
    action, after = children
    root_origin = core._origin(workspace, workspace.root_source)
    source = workspace.first_child_source(
        workspace.root_action,
        core.view(root_origin),
        action,
        after,
    )
    core._origin(workspace, source)
    before = (
        ledger.entries,
        ledger.nodes,
        len(workspace.support),
        len(workspace.support_snapshots),
        len(workspace.images),
        len(workspace.image_snapshots),
        len(core._nodes),
        len(core._applications),
    )
    original = ledger.reserve_many
    original_single = ledger.reserve
    appended = 0
    source_image_owner = core._node_owner
    # Aggregate-only publication constructs one support node. An explicitly
    # chronological consumer still exercises rollback after several children.
    rejection_at = 4 if workspace.retain_chronological_support() else 1

    def inspect_reservations(rows: tuple[tuple[int, int, int], ...]) -> None:
        nonlocal appended
        if any(owner == workspace.support_owner for owner, _, _ in rows):
            appended += 1
            if failure_stage == "candidate" and appended == rejection_at:
                # The ledger itself rejects this reservation after several
                # support nodes have been published for the second query.
                ledger.max_nodes = ledger.nodes
        if (
            failure_stage == "publication"
            and any(owner == source_image_owner for owner, _, _ in rows)
            and len(workspace.support) > before[2]
        ):
            # Reject the shared scheduler's publication after the family
            # constructor returned its complete candidate.
            ledger.max_nodes = ledger.nodes

    def capped_many(reservations: Iterable[tuple[int, int, int]]) -> None:
        rows = tuple(reservations)
        inspect_reservations(rows)
        original(rows)

    def capped_single(owner: int, entries: int = 0, nodes: int = 0) -> None:
        inspect_reservations(((owner, entries, nodes),))
        original_single(owner, entries=entries, nodes=nodes)

    monkeypatch.setattr(ledger, "reserve_many", capped_many)
    monkeypatch.setattr(ledger, "reserve", capped_single)
    try:
        with pytest.raises(BlockContextBudgetExceeded):
            workspace.scheduler.source_image_demanded(
                workspace,
                source,
                action,
                SourceImageDemand("physical-summary"),
            )
    finally:
        ledger.max_nodes = 4096
        monkeypatch.setattr(ledger, "reserve_many", original)
        monkeypatch.setattr(ledger, "reserve", original_single)

    assert appended >= rejection_at
    assert (
        ledger.entries,
        ledger.nodes,
        len(workspace.support),
        len(workspace.support_snapshots),
        len(workspace.images),
        len(workspace.image_snapshots),
        len(core._nodes),
        len(core._applications),
    ) == before
    assert not workspace.balanced_stack and not workspace.macro_stack
    workspace.validate()
    assert all(item.accounting_delta in (None, 0) for item in ledger.inventory())
