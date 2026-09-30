"""Parent identities are available early and published as one retained unit."""

from __future__ import annotations

from dataclasses import replace
from functools import partial
from typing import TYPE_CHECKING, Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.hashlife.execution.continuations.diamond_tasks import (
    MacroTransferKey,
)
from number_compiler.hashlife.execution.diamond_parent import publish_parent_identity
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from tests.support.assertions import assert_rejected_atomically
from tests.support.diamond_runtime import build

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )


def setup() -> tuple[DiamondRuntime, MacroTransferKey]:
    runtime, action = build(CollatzPhysicalBlockEffect(), (1, 0, 1, 1), 8, 2)
    key = MacroTransferKey(action, action, runtime.cells.source(0, 3), 0)
    return runtime, key


@pytest.mark.parametrize("room", range(5))
def test_failed_parent_reservation_changes_no_associated_container_or_count(
    room: int,
) -> None:
    runtime, key = setup()
    runtime.ledger.max_cache_entries = runtime.ledger.entries + room
    assert_rejected_atomically(
        runtime.ledger,
        lambda: publish_parent_identity(
            runtime.actions, runtime.cells, runtime.macros, key
        ),
        BlockContextBudgetExceeded,
    )


def test_parent_action_image_and_binding_share_one_reservation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime, key = setup()
    runtime.ledger.max_cache_entries = runtime.ledger.entries + 5
    before = runtime.ledger.snapshot()
    result = publish_parent_identity(
        runtime.actions, runtime.cells, runtime.macros, key
    )
    after = runtime.ledger.snapshot()
    assert after.entries - before.entries == 5
    assert after.nodes - before.nodes == 2
    assert runtime.macros[key] == result
    assert any(
        node.kind == "image"
        and node.action == result.local_id
        and node.left == key.cell.local_id
        for node in runtime.cells._nodes
    )
    assert all(row.accounting_delta == 0 for row in runtime.ledger.inventory())

    def forbidden(*args: object) -> Never:
        raise AssertionError(
            "warm canonical parent planned descendants or another allocation"
        )

    monkeypatch.setattr(runtime.actions, "_plan_compose", forbidden)
    monkeypatch.setattr(runtime.ledger, "reserve_many", forbidden)
    assert (
        publish_parent_identity(runtime.actions, runtime.cells, runtime.macros, key)
        == result
    )


@pytest.mark.parametrize("warm", [False, True])
def test_foreign_parent_handles_reject_before_work_or_publication(warm: bool) -> None:
    runtime, key = setup()
    _, foreign = setup()
    if warm:
        publish_parent_identity(runtime.actions, runtime.cells, runtime.macros, key)
    for invalid in (
        replace(key, before=foreign.before),
        replace(key, cell=foreign.cell),
        replace(key, side=True),
    ):
        assert_rejected_atomically(
            runtime.ledger,
            partial(
                publish_parent_identity,
                runtime.actions,
                runtime.cells,
                runtime.macros,
                invalid,
            ),
            (TypeError, ValueError),
        )


def test_image_hidden_inside_join_rejects_before_parent_publication() -> None:
    runtime, key = setup()
    leaf = runtime.cells.source(0, 0)
    image = runtime.cells.image(key.before, leaf)
    mixed = runtime.cells.join(leaf, image)
    invalid = replace(key, cell=mixed)
    assert_rejected_atomically(
        runtime.ledger,
        lambda: publish_parent_identity(
            runtime.actions, runtime.cells, runtime.macros, invalid
        ),
        ValueError,
        match="original source geometry",
    )
