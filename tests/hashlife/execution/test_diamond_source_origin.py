"""Warm source admission uses an owned structural proof, never descendant replay."""

from __future__ import annotations

from dataclasses import replace
from typing import TYPE_CHECKING, Literal, Never, cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.hashlife.actions.diamond_actions import CellNode
from number_compiler.hashlife.execution.continuations.diamond_higher_tasks import (
    HigherUnarySummary,
)
from number_compiler.hashlife.execution.continuations.diamond_tasks import (
    Initial,
    PairSummary,
    SpatialSummary,
    Transfer,
)
from number_compiler.hashlife.execution.diamond_payload import DiamondPayloadRegistry
from number_compiler.hashlife.interfaces.diamond_boundary import ImageBinding
from tests.support.diamond_higher_context import machine

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
    from number_compiler.hashlife.actions.diamond_actions import CellID
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )


def _joined_source(
    level: int = 6,
) -> tuple[DiamondRuntime, ActionProgramID, CellID]:
    runtime, action = machine((0, 1), 2)
    cell = runtime.cells.join(runtime.cells.source(1, 0), runtime.cells.source(0, 0))
    for _ in range(level - 1):
        cell = runtime.cells.join(cell, cell)
    assert runtime.cells.node(cell).kind == "join"
    return runtime, action, cell


def _request(
    runtime: DiamondRuntime,
    action: ActionProgramID,
    cell: CellID,
    kind: str,
) -> HigherUnarySummary | PairSummary | SpatialSummary | Transfer:
    if kind == "higher":
        return HigherUnarySummary(runtime.actions.identity, cell, 0)
    if kind == "spatial":
        return SpatialSummary(action, cell, 0)
    if kind == "pair":
        return PairSummary(runtime.actions.compose(action, action), cell)
    identity = runtime.actions.identity
    left = runtime.execute(Initial(identity, 0))
    right = runtime.execute(Initial(identity, 1))
    return Transfer(ImageBinding(identity, cell, left, right), identity, left, 0)


@pytest.mark.parametrize("kind", ("higher", "spatial", "pair", "transfer"))
def test_warm_parent_never_reads_source_descendants_for_admission(
    monkeypatch: pytest.MonkeyPatch, kind: str
) -> None:
    runtime, action, cell = _joined_source()
    request = _request(runtime, action, cell, kind)
    expected = runtime.execute(request)
    original = runtime.cells.resolve
    reads = []

    def only_root(
        reference: CellID,
    ) -> CellNode:
        assert reference == cell, "warm source admission revisited a descendant"
        reads.append(reference)
        return original(reference)

    def forbidden(*args: object) -> None:
        pytest.fail("warm parent expanded or observed an original-source descendant")

    monkeypatch.setattr(runtime.cells, "resolve", only_root)
    monkeypatch.setattr(runtime.cells, "reference", forbidden)
    monkeypatch.setattr(runtime.cells, "split", forbidden)
    monkeypatch.setattr(runtime.cells, "source_symbol", forbidden)
    before = runtime.ledger.snapshot()
    assert runtime.execute(request) == expected
    after = runtime.ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    assert reads
    assert (
        after.counters["scheduler_transitions"]
        == before.counters["scheduler_transitions"] + 1
    )
    if kind == "higher":
        assert len(reads) == 2
        assert after.counters["higher_context_admission_visits"] == before.counters[
            "higher_context_admission_visits"
        ] + len(reads)


@pytest.mark.parametrize("kind", ("higher", "spatial", "pair", "transfer"))
def test_warm_admission_still_rejects_foreign_reflected_and_future_cells(
    kind: str,
) -> None:
    runtime, action, cell = _joined_source(3)
    runtime.execute(_request(runtime, action, cell, kind))
    foreign, _, foreign_cell = _joined_source(3)
    assert foreign.ledger is not runtime.ledger
    image = runtime.cells.image(action, cell)
    invalid = (
        foreign_cell,
        runtime.cells.mirror(cell),
        image,
        runtime.cells.join(cell, image),
        runtime.cells.slice(image, 0, 0),
    )
    for bad_cell in invalid:
        request = _request(runtime, action, cell, kind)
        request = (
            replace(request, provider=replace(request.provider, cell=bad_cell))
            if isinstance(request, Transfer)
            else replace(request, cell=bad_cell)
        )
        before = runtime.ledger.snapshot()
        with pytest.raises((TypeError, ValueError)):
            runtime.execute(request)
        assert runtime.ledger.snapshot() == before


def test_original_metadata_is_derived_and_independently_audited() -> None:
    runtime, action, cell = _joined_source(3)
    image = runtime.cells.image(action, cell)
    assert runtime.cells.require_original(cell).original_forward is True
    assert runtime.cells.node(image).original_forward is False
    forged = CellNode(
        "join",
        runtime.cells.node(cell).level + 1,
        left=cell.local_id,
        right=image.local_id,
        original_forward=True,
    )
    joined = runtime.cells._intern(forged)
    assert runtime.cells.node(joined).original_forward is False
    record = runtime.cells.node(joined)
    assert DiamondPayloadRegistry(runtime.ledger).valid(record)
    object.__setattr__(record, "original_forward", True)
    try:
        assert not DiamondPayloadRegistry(runtime.ledger).valid(record)
    finally:
        object.__setattr__(record, "original_forward", False)


def test_origin_metadata_and_node_publication_share_the_same_budget_reservation() -> (
    None
):
    runtime, _ = machine((0, 1), 2)
    leaf = runtime.cells.source(0, 0)
    runtime.ledger.tighten_limits(None, runtime.ledger.entries + 1)
    before = runtime.ledger.snapshot()
    nodes, keys = tuple(runtime.cells._nodes), tuple(runtime.cells._ids.items())
    with pytest.raises(BlockContextBudgetExceeded):
        runtime.cells._intern(
            CellNode("join", 1, left=leaf.local_id, right=leaf.local_id)
        )
    assert runtime.ledger.snapshot() == before
    assert tuple(runtime.cells._nodes) == nodes
    assert tuple(runtime.cells._ids.items()) == keys


def test_source_validation_no_longer_retains_a_second_boolean_cache() -> None:
    runtime, action, cell = _joined_source(3)
    runtime.execute(_request(runtime, action, cell, "transfer"))
    assert not hasattr(runtime, "original_cells")
    assert all(
        not row.name.endswith("-original-cells") for row in runtime.ledger.inventory()
    )


def test_source_kind_proof_cannot_be_supplied_by_an_equality_callback() -> None:
    class SourceImpostor:
        def __eq__(self, other: object) -> Never:
            pytest.fail("source-kind admission executed a payload callback")

    with pytest.raises(ValueError):
        CellNode(
            cast(
                "Literal['source', 'image', 'slice', 'join', 'mirror']",
                SourceImpostor(),
            ),
            0,
            source_tile=0,
            original_forward=True,
        )
