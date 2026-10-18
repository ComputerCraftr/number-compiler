"""Focused contract tests for the source-owned comma semantic bridge."""

from __future__ import annotations

import weakref
from collections.abc import Callable

import pytest

from devtools.verification.comma_b1_quotient import (
    B1State,
    observe_b1,
    offset_orbit,
    offset_representatives,
)
from number_compiler.resources.fused_traversal_workspace import (
    fused_traversal_workspace_owner_names,
)
from number_compiler.sequences.comma.boundary_chart import BoundaryChart
from number_compiler.sequences.comma.cyclotomic_clock import CyclotomicClock
from number_compiler.sequences.comma.semantic_continuation import (
    ContinuationID,
    SemanticContinuation,
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


def test_powered_application_preflights_workspace_names_before_registration(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    representatives = offset_representatives()
    roots = tuple(_root(offset) for offset in representatives)
    arena = SemanticContinuationArena()
    arena.compile_many(roots)
    view = arena.publish(roots)
    prefix = f"comma-semantic-powered-{view.ledger.owner_count + 1}"
    workspace_names = fused_traversal_workspace_owner_names(prefix)
    collision_owner = view.ledger.register(
        workspace_names[2], "fused_interface_workspace"
    )
    view.ledger.make_dict(collision_owner)
    before = view.ledger.owner_count

    def forbidden_inventory(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("application setup must not inventory ledger stores")

    monkeypatch.setattr(view.ledger, "inventory", forbidden_inventory)
    with pytest.raises(ValueError, match="already registered"):
        view.powered_application(source_for_live_root=lambda root: roots[root])
    assert view.ledger.owner_count == before


def _live_request(
    view: SemanticContinuation, roots: tuple[BoundaryChart, ...]
) -> tuple[BoundaryChart, int]:
    for source in roots:
        for phase in range(924):
            if view.evaluate(source, phase).action.kind == "live":
                return source, phase
    raise AssertionError("compiled comma view has no live request")


def test_powered_convenience_reuses_one_owner_and_rebinds_each_callback() -> None:
    representatives = offset_representatives()
    roots = tuple(_root(offset) for offset in representatives)
    arena = SemanticContinuationArena()
    arena.compile_many(roots)
    view = arena.publish(roots)
    source, phase = _live_request(view, roots)
    owner_count = view.ledger.owner_count
    first_calls: list[int] = []
    second_calls: list[int] = []

    def first_resolver(root: int) -> BoundaryChart:
        first_calls.append(root)
        return _root(representatives[offset_orbit(root)])

    def second_resolver(root: int) -> BoundaryChart:
        second_calls.append(root)
        return _root(representatives[offset_orbit(root)], 137)

    view.apply_decades_powered(source, phase, 1, source_for_live_root=first_resolver)
    application = view._convenience_application
    assert application is not None
    first_binding = application.binding
    assert first_calls
    assert view.ledger.owner_count == owner_count + 5
    assert len(application._memo) == 0
    assert len(application._root_bindings) == 0
    assert application._workspace.nodes == 0

    view.apply_decades_powered(source, phase, 1, source_for_live_root=second_resolver)
    assert second_calls
    assert application.binding != first_binding
    assert application._source_for_live_root is None
    assert view.ledger.owner_count == owner_count + 5
    assert len(application._memo) == 0
    assert len(application._root_bindings) == 0
    assert application._workspace.nodes == 0


def test_powered_convenience_rejects_reentry_and_active_close() -> None:
    representatives = offset_representatives()
    roots = tuple(_root(offset) for offset in representatives)
    arena = SemanticContinuationArena()
    arena.compile_many(roots)
    view = arena.publish(roots)
    source, phase = _live_request(view, roots)
    refused: list[str] = []

    def resolver(root: int) -> BoundaryChart:
        with pytest.raises(RuntimeError, match="already active"):
            view.apply_decades_powered(source, phase, 1, source_for_live_root=resolver)
        refused.append("reentry")
        with pytest.raises(RuntimeError, match="active"):
            view.close()
        refused.append("close")
        return _root(representatives[offset_orbit(root)])

    view.apply_decades_powered(source, phase, 1, source_for_live_root=resolver)
    application = view._convenience_application
    assert application is not None
    assert refused == ["reentry", "close"]
    assert not application._active
    assert not application._closed
    assert not view._convenience_closed


def test_powered_convenience_drops_callback_closure_after_request() -> None:
    representatives = offset_representatives()
    roots = tuple(_root(offset) for offset in representatives)
    arena = SemanticContinuationArena()
    arena.compile_many(roots)
    view = arena.publish(roots)
    source, phase = _live_request(view, roots)

    class CapturedPayload:
        pass

    def make_resolver(
        captured: CapturedPayload,
    ) -> tuple[Callable[[int], BoundaryChart], weakref.ReferenceType[CapturedPayload]]:
        payload_ref = weakref.ref(captured)

        def resolver(root: int) -> BoundaryChart:
            assert captured is not None
            return _root(representatives[offset_orbit(root)])

        return resolver, payload_ref

    resolver, payload_ref = make_resolver(CapturedPayload())

    view.apply_decades_powered(source, phase, 1, source_for_live_root=resolver)
    application = view._convenience_application
    assert application is not None
    assert application._source_for_live_root is None
    del resolver
    # This payload has no reference cycle: request cleanup must release the
    # callback immediately, without relying on a whole-process GC sweep.
    assert payload_ref() is None
    view.close()


def test_manual_powered_application_releases_resolver_when_closed() -> None:
    source = _root(offset_representatives()[0])
    arena = SemanticContinuationArena()
    arena.compile(source)
    view = arena.publish((source,))

    class CapturedPayload:
        pass

    def make_resolver(
        captured: CapturedPayload,
    ) -> tuple[Callable[[int], BoundaryChart], weakref.ReferenceType[CapturedPayload]]:
        payload_ref = weakref.ref(captured)

        def resolver(_root_value: int) -> BoundaryChart:
            assert captured is not None
            return source

        return resolver, payload_ref

    resolver, payload_ref = make_resolver(CapturedPayload())

    application = view.powered_application(source_for_live_root=resolver)
    assert application._source_for_live_root is resolver
    del resolver
    assert payload_ref() is not None
    application.close()
    assert application._source_for_live_root is None
    assert payload_ref() is None


def test_failed_powered_close_is_fail_closed_and_retryable(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = _root(offset_representatives()[0])
    arena = SemanticContinuationArena()
    arena.compile(source)
    view = arena.publish((source,))

    def resolver(_root_value: int) -> BoundaryChart:
        return source

    application = view.powered_application(source_for_live_root=resolver)
    owners = (
        application._memo.owner,
        application._root_bindings.owner,
        application._workspace.owner,
    )

    def fail_memo_dispose() -> None:
        raise RuntimeError("memo cleanup failed")

    def fail_roots_dispose() -> None:
        raise ValueError("root cleanup failed")

    def fail_workspace_dispose() -> None:
        raise OSError("workspace cleanup failed")

    monkeypatch.setattr(application._memo, "dispose", fail_memo_dispose)
    monkeypatch.setattr(application._root_bindings, "dispose", fail_roots_dispose)
    monkeypatch.setattr(application._workspace, "dispose", fail_workspace_dispose)

    with pytest.raises(OSError, match="workspace cleanup failed") as failure:
        application.close()

    context_messages: list[str] = []
    context = failure.value.__context__
    while context is not None:
        context_messages.append(str(context))
        context = context.__context__
    assert context_messages == ["root cleanup failed", "memo cleanup failed"]
    assert application._closing
    assert not application._closed
    assert application._source_for_live_root is None
    assert all(not view.ledger.inventory_owner(owner).disposed for owner in owners)
    with pytest.raises(RuntimeError, match="closing or closed"):
        application.apply(source, 0, 0)

    monkeypatch.undo()
    application.close()
    assert application._closed
    assert not application._closing
    assert all(view.ledger.inventory_owner(owner).disposed for owner in owners)


def test_powered_convenience_clears_failed_request_and_closes_only_its_owner() -> None:
    representatives = offset_representatives()
    roots = tuple(_root(offset) for offset in representatives)
    arena = SemanticContinuationArena()
    arena.compile_many(roots)
    view = arena.publish(roots)
    source, phase = _live_request(view, roots)

    def failing_resolver(_root_value: int) -> BoundaryChart:
        raise RuntimeError("resolver failed")

    with pytest.raises(RuntimeError, match="resolver failed"):
        view.apply_decades_powered(
            source, phase, 1, source_for_live_root=failing_resolver
        )

    application = view._convenience_application
    assert application is not None
    workspace = application._workspace
    assert not application._active
    assert len(application._memo) == 0
    assert len(application._root_bindings) == 0
    assert not workspace.active
    assert workspace.nodes == 0
    assert not workspace.frames
    assert not workspace.values

    def valid_resolver(root_value: int) -> BoundaryChart:
        return _root(representatives[offset_orbit(root_value)])

    view.apply_decades_powered(source, phase, 1, source_for_live_root=valid_resolver)
    manual = view.powered_application(source_for_live_root=valid_resolver)
    helper_owners = (
        application._memo.owner,
        application._root_bindings.owner,
        workspace.owner,
        workspace.frame_owner,
        workspace.value_owner,
    )
    view.close()
    assert application._closed
    assert all(view.ledger.inventory_owner(owner).disposed for owner in helper_owners)
    with pytest.raises(RuntimeError, match="convenience owner is closed"):
        view.apply_decades_powered(
            source, phase, 1, source_for_live_root=valid_resolver
        )

    # Explicit manual applications retain their separate lifecycle.
    assert manual.apply(source, phase, 0).complete_decades == 0
    manual.close()


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
