"""Recycled grammar indices cannot authorize stale temporal responses."""

from __future__ import annotations

import pytest

from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.temporal_hashlife import stencil_cell


def test_rollback_recycles_slice_root_without_reusing_its_cached_output() -> None:
    with DoubleReverseTerm(173488, 4) as term:
        engine = term.temporal_engine
        arena = engine.arena
        stable = engine.scoped_handle(engine.source_root)
        for digit in range(10):
            arena.terminal(digit)
        checkpoint = len(arena.nodes)
        old = arena.word((2, 6, 6, 4, 7, 3, 7, 8))
        old_handle = engine.scoped_handle(old)
        assert arena.materialize(engine.part(old, 1, 7)) == (6, 6, 4, 7, 3, 7)
        arena.rollback_unpublished_suffix(checkpoint)
        new = arena.word((2, 8, 8, 3, 0, 0, 5, 9))
        assert new == old
        assert engine.root_of(stable) == engine.source_root
        with pytest.raises(ValueError, match="stale"):
            engine.root_of(old_handle)
        assert arena.materialize(engine.part(new, 1, 7)) == (8, 8, 3, 0, 0, 5)


def test_equal_content_reallocation_does_not_revive_a_stale_handle() -> None:
    with DoubleReverseTerm(173488, 4) as term:
        engine = term.temporal_engine
        arena = engine.arena
        for digit in range(10):
            arena.terminal(digit)
        checkpoint = len(arena.nodes)
        word = (2, 6, 6, 4, 7, 3, 7, 8)
        old = arena.word(word)
        old_handle = engine.scoped_handle(old)
        arena.rollback_unpublished_suffix(checkpoint)
        new = arena.word(word)
        assert new == old
        with pytest.raises(ValueError, match="stale"):
            engine.root_of(old_handle)
        assert engine.root_of(engine.scoped_handle(new)) == new


def test_recycled_cone_root_recomputes_its_ordered_stencil() -> None:
    with DoubleReverseTerm(173488, 4) as term:
        engine = term.temporal_engine
        arena = engine.arena
        for digit in range(10):
            arena.terminal(digit)
        checkpoint = len(arena.nodes)
        old = arena.word((0, 2, 5, 6))
        engine._cone_step(old, 1)
        arena.rollback_unpublished_suffix(checkpoint)
        new = arena.word((0, 5, 2, 7))
        assert new == old
        result = engine._cone_step(new, 1)
        assert arena.materialize(result) == (
            stencil_cell(0, 5, 2),
            stencil_cell(5, 2, 7),
        )


def test_cached_action_rejects_a_rolled_back_target() -> None:
    with DoubleReverseTerm(173488, 4) as term:
        engine = term.temporal_engine
        arena = engine.arena
        source = term.source_root
        phase = engine.certify(source)
        assert phase is not None
        checkpoint = len(arena.nodes)
        action = engine.advance_action(source, 2, phase)
        assert action.target.local_id >= checkpoint
        removed = tuple(arena.nodes[checkpoint:])
        arena.rollback_unpublished_suffix(checkpoint)
        for node in removed:
            if node.kind == "TERM":
                rebuilt = arena.terminal(node.symbol)
            elif node.kind == "CONCAT":
                rebuilt = arena.concat(node.left, node.right)
            else:
                assert node.kind == "REPEAT"
                rebuilt = arena.repeat(node.child, node.count)
            assert rebuilt == node.id
        with pytest.raises(ValueError):
            engine.advance_action(source, 2, phase)


def test_action_issued_before_rollback_remains_authorized() -> None:
    with DoubleReverseTerm(173488, 4) as term:
        engine = term.temporal_engine
        arena = engine.arena
        source = term.source_root
        phase = engine.certify(source)
        assert phase is not None
        action = engine.advance_action(source, 2, phase)
        checkpoint = len(arena.nodes)
        arena.word((9, 0, 2, 5, 6, 9))
        arena.rollback_unpublished_suffix(checkpoint)
        assert engine.advance_action(source, 2, phase) is action
