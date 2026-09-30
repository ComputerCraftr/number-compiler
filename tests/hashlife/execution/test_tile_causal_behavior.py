"""Behavior proofs discharge real dependencies without emitting their tiles."""

from __future__ import annotations

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.execution.tile_causal_behavior import quiescent_boundary
from number_compiler.hashlife.execution.tile_causal_boundary_step import (
    boundary_step as _canonical_boundary_step,
)
from number_compiler.hashlife.execution.tile_causal_tasks import (
    CausalFrame,
    CausalPrefix,
)
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from tests.support.tile_kernel import _runtime, _tile, powered_runtime


@pytest.mark.parametrize("base", (2, 3, 10))
@pytest.mark.parametrize("exponent", (4, 8))
@pytest.mark.parametrize("side", (0, 1))
def test_quiescent_deep_boundary_reuses_input_without_constructors(
    base: int,
    exponent: int,
    side: int,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(base))
    action = adapter.power(primitive, exponent)
    engine = CausalTileEngine(scheduler)
    blank = adapter.primitive_law(primitive).blank
    with _tile(tiles, adapter, primitive, (blank,) * 4) as source:
        view = BoundaryTileView(source.tile, 11, 4, side)
        anchor = engine._initial(action, side)
        argument = engine._initial(action, 1 - side)

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("behavior constructed an exact causal boundary")

        monkeypatch.setattr(tiles, "leaf", forbidden)
        monkeypatch.setattr(tiles, "join", forbidden)
        monkeypatch.setattr(engine, "output", forbidden)
        result = quiescent_boundary(engine, action, side, view, anchor, argument)
        assert result == BoundaryTileView(source.tile, 0, 4, side)
        assert ledger.counters["causal_extent_discharged_by_behavior"] == 4
        assert ledger.counters.get("tile_causal_boundary_output_completions", 0) == 0


@pytest.mark.parametrize("exponent", (4, 8))
def test_public_scheduler_blank_dependencies_avoid_boundary_output(
    exponent: int,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.hashlife.execution.tile_causal as causal

    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    action = adapter.power(primitive, exponent)
    ordinary = _canonical_boundary_step

    def forbid_boundary(
        engine: object, frame: CausalFrame, frames: object, values: list[object]
    ) -> bool:
        if frame.op == "output_boundary":
            raise AssertionError("certified blank dependency constructed output")
        return ordinary(engine, frame, frames, values)

    with _tile(tiles, adapter, primitive, (5,) * 8) as source:
        monkeypatch.setattr(causal, "boundary_step", forbid_boundary)
        with scheduler.application(
            action,
            source.tile,
            adapter.initial_ports(action),
            adapter.wiring(action),
        ) as application:
            assert application.point(3) == 5
            assert application.point(6) == 5
            assert application._root is None
    assert ledger.counters["tile_causal_quiescent_boundary_reuses"] > 0
    assert ledger.counters["powered_absorption_max_span"] == exponent


def test_active_input_and_unsafe_physical_left_context_decline() -> None:
    _ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    engine = CausalTileEngine(scheduler)
    law = adapter.primitive_law(primitive)
    action = adapter.power(primitive, 4)
    unsafe = next(
        left
        for left in range(law.left_count)
        if any(
            law.emit(left, law.blank, right) != law.blank
            for right in range(law.right_count)
        )
    )
    with _tile(tiles, adapter, primitive, (5,) * 4) as blank:
        # For a right scan the physical LEFT context is the opposite argument.
        left = engine._initial(action, 0, unsafe)
        right = engine._initial(action, 1)
        assert (
            quiescent_boundary(
                engine,
                action,
                1,
                BoundaryTileView(blank.tile, 0, 4, 1),
                right,
                left,
            )
            is None
        )
    with _tile(tiles, adapter, primitive, (0, 0, 0, 1)) as active:
        assert (
            quiescent_boundary(
                engine,
                action,
                0,
                BoundaryTileView(active.tile, 0, 4),
                engine._initial(action, 0),
                engine._initial(action, 1),
            )
            is None
        )


def test_nonblank_left_prefix_is_not_erased() -> None:
    _ledger, tiles, adapter, primitive, scheduler, action, _blank = powered_runtime(
        BaseBlockEffect(3), 4
    )
    engine = CausalTileEngine(scheduler)
    initial = adapter.initial_ports(primitive)
    with (
        _tile(tiles, adapter, primitive, (5,) * 4) as blank,
        _tile(
            tiles,
            adapter,
            primitive,
            (4, 4, 4, 4),
        ) as active,
    ):
        left = CausalPrefix(
            action,
            0,
            initial[0],
            initial[0],
            BoundaryTileView(active.tile, 0, 4),
        )
        assert (
            quiescent_boundary(
                engine,
                action,
                0,
                BoundaryTileView(blank.tile, 0, 4),
                left,
                engine._initial(action, 1),
            )
            is None
        )


def test_failed_behavior_width_releases_active_application_context(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.hashlife.execution.tile_causal_api as causal_api

    _ledger, tiles, adapter, primitive, scheduler, action, _blank = powered_runtime(
        BaseBlockEffect(3), 4
    )
    engine = CausalTileEngine(scheduler)

    def fail(*_args: object, **_kwargs: object) -> Never:
        raise RuntimeError("injected behavior failure")

    with _tile(tiles, adapter, primitive, (5,) * 4) as source:
        monkeypatch.setattr(causal_api, "quiescent_boundary", fail)
        with pytest.raises(RuntimeError, match="injected behavior failure"):
            engine.width(action, source.tile, limit=4, application=17)
        assert engine._application is None
        assert not engine._hold_workspace


def test_blank_output_proof_does_not_invent_a_right_transfer() -> None:
    from array import array

    from number_compiler.arithmetic.contracts.block_effect import BoundarySide
    from number_compiler.arithmetic.contracts.block_kernel import FiniteBlockEffect

    effect = FiniteBlockEffect(
        base=2,
        exponent=1,
        left_count=1,
        right_count=2,
        alphabet_size=4,
        initial_left=0,
        initial_right=0,
        left_transitions=array("I", (0,) * 4),
        right_transitions=array("I", (0, 0, 0, 0, 1, 1, 1, 0)),
        outputs=bytes(
            3 if symbol == 3 else (symbol + right) % 3
            for symbol in range(4)
            for right in range(2)
        ),
        kernel_name="blank-output-nonidentity-right",
        storage_bytes=0,
        uncompressed_bytes=0,
        blank_left_tail=0,
        blank_right_tail=0,
        stable_blank_output=True,
    )
    _ledger, tiles, adapter, primitive, scheduler = _runtime(effect)
    law = adapter.primitive_law(primitive)
    assert law.advance(BoundarySide.RIGHT, 1, law.blank) == 0
    with _tile(tiles, adapter, primitive, (3, 3, 3, 3)) as source:
        engine = CausalTileEngine(scheduler)
        assert (
            quiescent_boundary(
                engine,
                primitive,
                0,
                BoundaryTileView(source.tile, 0, 4),
                0,
                1,
            )
            is not None
        )
        assert scheduler.results.retained_results == 0
        # Exact completion still computes and preserves the actual right exit.
        with scheduler.complete(
            primitive,
            source.tile,
            (0, 1),
            adapter.wiring(primitive),
        ) as result:
            assert result.result.outgoing_ports[1] == 0


def test_new_behavior_admission_rolls_back_after_binding_write_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    engine = CausalTileEngine(scheduler)
    action = adapter.power(primitive, 4)
    blank = adapter.primitive_law(primitive).blank
    with _tile(tiles, adapter, primitive, (blank,) * 4) as source:
        before = ledger.snapshot()
        next_profile = adapter.quotients._next_future_profile
        next_class = adapter.quotients._next_future_class

        def fail_reverse_index(*_args: object, **_kwargs: object) -> Never:
            raise RuntimeError("injected reverse-index failure")

        monkeypatch.setattr(scheduler.results, "_add_membership", fail_reverse_index)
        with pytest.raises(RuntimeError, match="injected reverse-index failure"):
            quiescent_boundary(
                engine,
                action,
                0,
                BoundaryTileView(source.tile, 0, 4),
                engine._initial(action, 0),
                engine._initial(action, 1),
            )

        assert not adapter.quotients._future_admissions
        assert not adapter.quotients._future_profiles
        assert not adapter.quotients._future_classes
        assert not adapter.quotients._future_certificates
        assert not adapter.quotients._future_snapshots
        assert adapter.quotients._next_future_profile > next_profile
        assert adapter.quotients._next_future_class > next_class
        assert not scheduler.results._memo
        assert not scheduler.results._reverse
        after = ledger.snapshot()
        before_semantic = {
            item.name: (item.entries, item.nodes)
            for item in before.inventory
            if item.role != "observation_memo"
        }
        after_semantic = {
            item.name: (item.entries, item.nodes)
            for item in after.inventory
            if item.role != "observation_memo"
        }
        assert after_semantic == before_semantic
        # The cold miss remains as charged diagnostic evidence of failed work.
        assert after.entries - before.entries == 2
        assert after.nodes == before.nodes


def test_explicit_producer_and_consumer_admissibility_are_independent() -> None:
    from number_compiler.hashlife.execution.tile_causal_tasks import bound_states
    from number_compiler.hashlife.tiles.tile_ports import (
        BoundPorts,
        FusedBoundaryContract,
    )

    _ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    action = adapter.power(primitive, 4)
    law = adapter.primitive_law(primitive)
    assert law.behavior is not None
    profile, _ = adapter.quotients.admit_quiescent_blank(law.behavior)
    safe = adapter.quotients.future_certificate(profile).safe_blank_left_states
    raw_safe = [i for i, q in enumerate(law.behavior.left_classes) if q in safe]
    unsafe = next(i for i, q in enumerate(law.behavior.left_classes) if q not in safe)
    right = adapter.initial_ports(action)[1]
    wiring = adapter.wiring(action)
    with _tile(tiles, adapter, primitive, (5, 5, 5, 5)) as source:
        engine = CausalTileEngine(scheduler)
        for consumer, accepted in ((raw_safe[-1], True), (unsafe, False)):
            contract = FusedBoundaryContract(
                BoundPorts((raw_safe[0], right), wiring),
                BoundPorts((consumer, right), wiring),
            )
            left, right_state = bound_states(
                adapter, scheduler.results, action, source.tile, contract
            )
            result = quiescent_boundary(
                engine,
                action,
                1,
                BoundaryTileView(source.tile, 0, 4, 1),
                right_state,
                left,
            )
            assert (result is not None) == accepted
