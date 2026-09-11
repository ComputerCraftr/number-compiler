"""Integration attacks on state erasure and exact synchronization geometry."""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from number_compiler.hashlife.execution.continuations.diamond_tasks import (
    Initial,
    ResetTransfer,
    Transfer,
)
from number_compiler.hashlife.interfaces.diamond_boundary import (
    BoundaryStateID,
    ImageBinding,
)
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from tests.support.diamond_runtime import build

if TYPE_CHECKING:
    from number_compiler.hashlife.actions.diamond_actions import CellID
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )
    from number_compiler.hashlife.interfaces.diamond_boundary import ImageBinding


def identity_provider(
    runtime: DiamondRuntime,
    cell: CellID,
) -> ImageBinding:
    identity = runtime.actions.identity
    left = runtime.execute(Initial(identity, 0))
    right = runtime.execute(Initial(identity, 1))
    return ImageBinding(identity, cell, left, right)


def test_foreign_incoming_state_cannot_disappear_into_warm_reset_key() -> None:
    runtime, action = build(CollatzPhysicalBlockEffect(), (0, 1), 2, 2)
    other, other_action = build(CollatzPhysicalBlockEffect(), (0, 1), 2, 2)
    provider = identity_provider(runtime, runtime.cells.source(0, 1))
    incoming = runtime.execute(Initial(action, 1))
    foreign = other.execute(Initial(other_action, 1))
    wrong_side = runtime.execute(Initial(action, 0))
    assert isinstance(incoming, BoundaryStateID)
    malformed = BoundaryStateID(
        runtime.boundaries.token, "wrong-kind", incoming.local_id
    )
    for warm in (False, True):
        if warm:
            valid = Transfer(provider, action, incoming, 1)
            expected = runtime.execute(valid)
            canonical = runtime._canonical_task(valid)
            assert isinstance(canonical, ResetTransfer)
            assert runtime.transfers[canonical] == expected
        absent = BoundaryStateID(
            runtime.boundaries.token,
            "diamond-boundary-state",
            len(runtime.boundaries.states),
        )
        for invalid in (foreign, wrong_side, malformed, absent):
            task = Transfer(provider, action, invalid, 1)
            for method in (
                runtime._canonical_task,
                runtime._probe,
                runtime.execute,
                runtime._cached_transfer,
            ):
                before = runtime.ledger.snapshot()
                with pytest.raises(ValueError):
                    method(task)
                assert runtime.ledger.snapshot() == before


def test_distinct_source_suffixes_share_only_the_certified_reset_prefix() -> None:
    runtime, action = build(
        CollatzPhysicalBlockEffect(), (0, 1, 0, 0, 0, 1, 1, 1), 8, 2
    )
    first, second = runtime.cells.source(0, 2), runtime.cells.source(4, 2)
    assert first != second
    incoming = runtime.execute(Initial(action, 1))
    requests = tuple(
        Transfer(identity_provider(runtime, cell), action, incoming, 1)
        for cell in (first, second)
    )
    canonical = tuple(runtime._canonical_task(request) for request in requests)
    assert all(isinstance(task, ResetTransfer) for task in canonical)
    assert canonical[0] == canonical[1]
    assert isinstance(canonical[0], ResetTransfer)
    assert canonical[0].provider.cell == runtime.cells.source(0, 1)
    assert runtime.execute(requests[0]) == runtime.execute(requests[1])
    assert runtime.ledger.counters["synchronizing_source_prefix_normalizations"] >= 2


def test_short_cell_and_wrong_scan_side_cannot_claim_reset_transfer() -> None:
    runtime, action = build(CollatzPhysicalBlockEffect(), (0, 1), 2, 2)
    short = identity_provider(runtime, runtime.cells.source(0, 0))
    enough = identity_provider(runtime, runtime.cells.source(0, 1))
    right = runtime.execute(Initial(action, 1))
    left = runtime.execute(Initial(action, 0))
    assert runtime.resets.radius(action) == 2
    short_request = Transfer(short, action, right, 1)
    left_request = Transfer(enough, action, left, 0)
    assert runtime._canonical_task(short_request) == short_request
    assert runtime._canonical_task(left_request) == left_request
    for invalid in (ResetTransfer(short, action, 1), ResetTransfer(enough, action, 0)):
        retained = len(runtime.transfers)
        with pytest.raises(ValueError, match="synchronization certificate"):
            runtime.execute(invalid)
        assert len(runtime.transfers) == retained
