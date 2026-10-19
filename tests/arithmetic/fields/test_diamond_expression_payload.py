"""The expression carrier admits typed programs, not packed observations."""

from __future__ import annotations

from dataclasses import replace
from typing import TYPE_CHECKING, Literal

import pytest

from number_compiler.hashlife.execution.diamond_payload import DiamondPayloadRegistry
from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
    BoundaryExpressionArena,
    ExprID,
    ExprSubstitutionKey,
    FunctionSort,
    StateSort,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from tests.support.dataclass_records import replace_record
from tests.support.diamond_boundary_expr import context

if TYPE_CHECKING:
    from number_compiler.arithmetic.fields.dyadic_tile import DyadicTile


def populated() -> tuple[ResourceLedger, BoundaryExpressionArena, ExprID]:
    ledger, actions, boundaries, arena, first, second = context()
    pair = actions.compose(first, second)
    left = arena.state_sort(first, 0)
    right = arena.state_sort(first, 1)
    x, y = arena.variable(left, "outer"), arena.variable(right, "inner")
    target = arena.variable(arena.state_sort(second, 0), "target")
    nested = arena.lambda_(x, arena.pair(pair, 0, x, arena.lambda_(y, target)))
    free = arena.variable(left, "free")
    arena.apply(nested, free)
    arena.substitute(nested, {target: arena.literal(boundaries.literal(second, 0, 0))})
    return ledger, arena, nested


@pytest.mark.parametrize("flag", (False, 1))
def test_binding_admission_metadata_must_equal_the_independent_graph_proof(
    flag: bool | int,
) -> None:
    ledger, arena, _ = populated()
    node = next(node for node in arena.nodes if node.kind == "port")
    assert node.binding_safe is True
    forged = replace_record(node, {"binding_safe": flag})
    ledger.reserve(arena.node_owner, entries=1, nodes=1)
    arena.nodes.append(forged)
    assert collect_ledger_metrics(ledger).forbidden_future_payloads > 0


def test_actual_open_binders_are_valid_only_as_typed_internal_dag_nodes() -> None:
    ledger, arena, root = populated()
    before = ledger.snapshot()
    report = collect_ledger_metrics(ledger)
    assert ledger.snapshot() == before
    assert (
        report.resource_audit_complete == report.representation_boundary_complete == 1
    )
    assert report.spatial_action_program_nodes == len(arena.nodes)
    registry = DiamondPayloadRegistry(ledger)
    assert registry.valid(root)
    for index, node in enumerate(arena.nodes):
        assert registry.valid(node)
        if node.scope:
            handle = ExprID(arena.token, "diamond-boundary-expression", index)
            assert registry.valid(
                handle
            )  # Canonical interner metadata may name an internal node.
            assert not registry.valid(
                ExprSubstitutionKey(handle, ())
            )  # Public programs must be closed.


@pytest.mark.parametrize(
    "field,value",
    [
        ("value", 1 << 1000),
        ("role", "hidden-field"),
        ("scope", 40),
        ("children", (1 << 1000,)),
    ],
)
def test_expression_record_mutation_cannot_hide_future_payload_or_invalid_scope(
    field: str, value: Literal["hidden-field"] | int | tuple[int]
) -> None:
    ledger, arena, root = populated()
    node = arena.nodes[root.local_id]
    malformed = replace_record(node, {field: value})
    ledger.reserve(arena.node_owner, entries=1, nodes=1)
    arena.nodes.append(malformed)
    report = collect_ledger_metrics(ledger)
    assert report.forbidden_future_payloads > 0


def test_lambda_binder_sort_is_checked_independently_of_claimed_scope() -> None:
    ledger, arena, root = populated()
    node = arena.nodes[root.local_id]
    assert type(node.sort) is FunctionSort
    malformed = replace(
        node,
        sort=replace(
            node.sort,
            domain=StateSort(node.sort.domain.action, 1 - node.sort.domain.side),
        ),
    )
    ledger.reserve(arena.node_owner, entries=1, nodes=1)
    arena.nodes.append(malformed)
    assert collect_ledger_metrics(ledger).forbidden_future_payloads > 0


@pytest.mark.parametrize("query_kind", ("point", "width"))
@pytest.mark.parametrize("warm", (False, True))
def test_direct_parametric_queries_block_exact_construction_inside_callbacks(
    query_kind: str, warm: bool, monkeypatch: pytest.MonkeyPatch
) -> None:
    from devtools.verification.parametric_query import (
        parametric_point,
        parametric_width,
    )
    from number_compiler.arithmetic.contracts.exact_tree_context import (
        ExactTreeConstructionForbidden,
    )
    from number_compiler.arithmetic.fields.dyadic_tile import leaf, tile_arena_metrics
    from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
    from tests.support.collatz_diamond_fixtures import build_collatz_diamond_application

    app = build_collatz_diamond_application(
        CollatzPhysicalBlockEffect(), (1, 0, 1), 8, 2
    )

    def query() -> int:
        return (
            parametric_point(app.runtime, app.root, 0)
            if query_kind == "point"
            else parametric_width(app.runtime, app.root, app.observer, 8)
        )

    if warm:
        query()
    leaf(1)
    before = tile_arena_metrics()

    def injected(*args: object) -> DyadicTile:
        return leaf(1)

    monkeypatch.setattr(app.runtime, "execute", injected)
    with pytest.raises(ExactTreeConstructionForbidden):
        query()
    after = tile_arena_metrics()
    assert (after["intern_hits"], after["intern_misses"]) == (
        before["intern_hits"],
        before["intern_misses"],
    )
