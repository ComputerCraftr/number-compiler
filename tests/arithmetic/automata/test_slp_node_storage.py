"""Standalone SLP node storage protects numeric identity from mutation."""

from __future__ import annotations

from collections.abc import Iterator

import pytest

from number_compiler.arithmetic.automata.slp import SLPArena, SLPNode
from number_compiler.arithmetic.automata.slp_node_storage import SLPNodeStorage


@pytest.mark.parametrize("edit", ("replace", "delete", "slice", "reorder"))
def test_destructive_node_edits_invalidate_generation_and_interner(
    edit: str,
) -> None:
    arena = SLPArena()
    first = arena.terminal(1)
    arena.terminal(2)
    generation = arena.node_id_generation

    if edit == "replace":
        arena.nodes[first] = SLPNode(first, "TERM", 1, symbol=3)
    elif edit == "delete":
        del arena.nodes[first]
    elif edit == "slice":
        arena.nodes[first : first + 1] = [SLPNode(first, "TERM", 1, symbol=3)]
    else:
        arena.nodes.reverse()

    assert arena.node_id_generation > generation
    with pytest.raises(RuntimeError, match="canonical interners are stale"):
        arena.terminal(3)


def test_storage_is_not_a_builtin_list_and_append_preserves_old_ids() -> None:
    arena = SLPArena()
    nodes = arena.nodes
    assert isinstance(nodes, SLPNodeStorage)
    assert not isinstance(nodes, list)
    generation = arena.node_id_generation

    nodes.append(SLPNode(len(nodes), "TERM", 1, symbol=3))

    assert arena.node_id_generation == generation
    assert arena.terminal(1) == len(nodes) - 1


def test_in_place_self_extension_keeps_storage_identity_and_row_order() -> None:
    arena = SLPArena()
    nodes = arena.nodes
    assert isinstance(nodes, SLPNodeStorage)
    original = tuple(nodes)
    generation = arena.node_id_generation

    arena.nodes += nodes

    assert arena.nodes is nodes
    assert tuple(nodes) == original + original
    assert arena.node_id_generation == generation


def test_append_failure_cannot_reuse_existing_node_ids() -> None:
    arena = SLPArena()
    original = arena.nodes[0]
    generation = arena.node_id_generation

    def failing_rows() -> Iterator[SLPNode]:
        yield SLPNode(len(arena.nodes), "TERM", 1, symbol=3)
        raise RuntimeError("injected append source failure")

    with pytest.raises(RuntimeError, match="append source failure"):
        arena.nodes.extend(failing_rows())

    assert arena.node_id_generation == generation
    assert arena.nodes[0] is original
    assert len(arena.nodes) == 2
    assert arena.terminal(1) == 2


def test_invalid_slice_edit_invalidates_before_assignment_refusal() -> None:
    arena = SLPArena()
    first = arena.terminal(1)
    arena.terminal(2)
    nodes = arena.nodes
    assert isinstance(nodes, SLPNodeStorage)
    snapshot = tuple(nodes)
    generation = arena.node_id_generation

    with pytest.raises(ValueError):
        nodes[slice(first, first + 1, 2)] = (
            SLPNode(first, "TERM", 1, symbol=3),
            SLPNode(first, "TERM", 1, symbol=4),
        )

    assert arena.node_id_generation > generation
    assert tuple(nodes) == snapshot


def test_sort_refuses_to_reorder_identity_bearing_rows() -> None:
    arena = SLPArena()
    arena.terminal(1)
    nodes = arena.nodes
    assert isinstance(nodes, SLPNodeStorage)
    generation = arena.node_id_generation

    with pytest.raises(TypeError, match="sorting identity-bearing"):
        nodes.sort()

    assert arena.node_id_generation == generation


def test_reinitialization_replaces_storage_without_recycling_generation() -> None:
    arena = SLPArena()
    old_rows = arena.nodes
    generation = arena.node_id_generation
    SLPArena.__init__(arena)
    assert arena.nodes is not old_rows
    assert arena.node_id_generation > generation
    assert not arena.node_storage_poisoned
    assert arena.terminal(1) == 1
