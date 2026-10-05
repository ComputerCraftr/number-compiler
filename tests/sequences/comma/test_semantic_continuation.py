"""Focused contract tests for the source-owned comma semantic bridge."""

from __future__ import annotations

import pytest

from devtools.verification.comma_b1_quotient import (
    B1State,
    observe_b1,
    offset_orbit,
    offset_representatives,
)
from number_compiler.sequences.comma.boundary_chart import BoundaryChart
from number_compiler.sequences.comma.cyclotomic_clock import CyclotomicClock
from number_compiler.sequences.comma.semantic_continuation import (
    ContinuationID,
    SemanticContinuationArena,
    TerminalWeight,
)


def _root(offset: int, delta: int = 0) -> BoundaryChart:
    return BoundaryChart("entry", 1, delta, offset)


def test_terminal_weight_is_the_b32_occurrence_codec() -> None:
    fork = TerminalWeight.local(3).after_complete_decades(4)
    landmine = TerminalWeight.local(8).after_complete_decades(2)
    assert fork.d == 39
    assert fork.height == 4
    assert fork.stop_j == 3
    assert fork.fork_a == 5
    assert not fork.is_landmine
    assert landmine.d == 26
    assert landmine.is_landmine
    assert landmine.fork_a is None


def test_source_delta_is_external_to_the_scoped_cid() -> None:
    offset = offset_representatives()[0]
    source = _root(offset)
    arena = SemanticContinuationArena()
    arena.compile(source)
    view = arena.publish((source,))
    shifted = view.evaluate(_root(offset, 1849), 17)
    expected = view.evaluate(source, (17 + 1849) % 924)
    cid, shift = view.source_address(_root(offset, 1849))
    assert shifted.action == expected.action
    assert view.source_ids[source] == view.source_ids[_root(offset)]
    assert cid == view.source_ids[source]
    assert shift == 1849


def test_cids_are_scoped_and_gotos_descend() -> None:
    source = _root(offset_representatives()[1])
    first = SemanticContinuationArena()
    identifier = first.compile(source)
    view = first.publish((source,))
    assert type(identifier) is ContinuationID
    assert view.evaluate_id(identifier, 0).kind in {"live", "stop"}
    foreign = SemanticContinuationArena()
    other = foreign.compile(source)
    with pytest.raises(ValueError):
        view.evaluate_id(other, 0)


def test_live_and_stop_controls_match_independent_chart_observer() -> None:
    representatives = offset_representatives()
    arena = SemanticContinuationArena()
    roots = tuple(_root(representatives[index]) for index in (0, 7, 23, 45))
    arena.compile_many(roots)
    view = arena.publish(roots)
    for fiber, source in zip((0, 7, 23, 45), roots, strict=True):
        for phase in (0, 1, 17, 460, 923):
            actual = view.evaluate(source, phase).action
            expected = observe_b1(B1State(fiber, phase)).observation
            if expected.kind == "live":
                assert actual.kind == "live"
                assert actual.live_root is not None
                assert offset_orbit(actual.live_root) == expected.value
            elif expected.kind == "fork":
                assert actual.kind == "stop"
                assert actual.stop_j == expected.value - 2
            else:
                assert actual.kind == "stop"
                assert actual.stop_j == 8


def test_apply_decades_returns_weighted_stop_and_resolves_live_roots() -> None:
    representatives = offset_representatives()
    source = _root(representatives[0])
    arena = SemanticContinuationArena()
    roots = tuple(_root(offset) for offset in representatives)
    arena.compile_many(roots)
    view = arena.publish(roots)

    def source_for_root(root: int) -> BoundaryChart:
        return _root(representatives[offset_orbit(root)])

    result = view.apply_decades(
        source,
        0,
        2,
        source_for_live_root=source_for_root,
    )
    if result.terminal is not None:
        assert result.terminal.d >= 0
        assert result.terminal.d % 9 == result.action.stop_j


def test_powered_application_memoizes_parent_blocks_and_stop_offset() -> None:
    representatives = offset_representatives()
    roots = tuple(_root(offset) for offset in representatives)
    arena = SemanticContinuationArena()
    arena.compile_many(roots)
    view = arena.publish(roots)

    def source_for_root(root: int) -> BoundaryChart:
        return _root(representatives[offset_orbit(root)])

    application = view.powered_application(
        source_for_live_root=source_for_root,
    )
    first = application.apply(roots[0], 0, 15)
    requests = application.requests
    second = application.apply(roots[0], 0, 15)
    assert second == first
    assert application.requests > requests
    assert application.hits > 0
    assert application.misses > 0
    shifted = application.apply(roots[0], 0, 3, delta=1849)
    rebased = application.apply(roots[0], 1849 % 924, 3)
    assert shifted == rebased
    if first.terminal is not None:
        assert first.action.stop_j is not None
        assert first.terminal.d == 9 * first.complete_decades + first.action.stop_j
    retained = view.ledger.entries
    application.close()
    assert view.ledger.entries < retained
    with pytest.raises(RuntimeError, match="closed"):
        application.apply(roots[0], 0, 0)


def test_moore_refinement_is_independent_and_has_no_hardcoded_count() -> None:
    roots = tuple(_root(offset) for offset in offset_representatives()[:3])
    arena = SemanticContinuationArena()
    arena.compile_many(roots)
    refinement = arena.refinement()
    view = arena.publish(roots)
    assert refinement.class_count <= len(view.actions_by_id)
    assert refinement.rounds >= 1
    assert refinement.classes == view.refine_moore().classes


def test_validation_rejects_bool_phase_and_invalid_clock_projection() -> None:
    source = _root(offset_representatives()[0])
    arena = SemanticContinuationArena()
    arena.compile(source)
    view = arena.publish((source,))
    with pytest.raises(ValueError):
        view.evaluate(source, True)
    with pytest.raises(ValueError):
        CyclotomicClock.from_phase(-1)
