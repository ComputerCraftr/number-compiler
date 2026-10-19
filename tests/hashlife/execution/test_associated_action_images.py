from __future__ import annotations

import pytest

from number_compiler.arithmetic.fields.consumer_pullback import (
    AssociatedActionArena,
    AssociatedActionID,
    ExactRational,
    SaturatingAffineAction,
    ThresholdDemand,
)
from number_compiler.hashlife.execution.associated_action_images import (
    AssociatedActionSourceAdapter,
    AssociatedScalarSource,
)
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageDemand,
)
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_audit import audit_registered_payloads


def _runtime() -> tuple[
    ResourceLedger, TileScheduler, AssociatedActionArena, AssociatedActionSourceAdapter
]:
    ledger = ResourceLedger()
    scheduler = TileScheduler.source_only(ledger)
    arena = AssociatedActionArena(ledger)
    adapter = AssociatedActionSourceAdapter(arena)
    scheduler.register_source_image_adapter(adapter)
    return ledger, scheduler, arena, adapter


def _decrement_fixture() -> tuple[
    ResourceLedger,
    TileScheduler,
    AssociatedActionArena,
    AssociatedActionSourceAdapter,
    AssociatedActionID,
    AssociatedActionID,
]:
    fixture = _runtime()
    arena = fixture[2]
    decrement = arena.admit(
        SaturatingAffineAction(offset=ExactRational(-1)), logical_extent=1
    )
    return (*fixture, decrement, arena.compose(decrement, decrement))


def _assert_threshold_failure(
    scheduler: TileScheduler,
    adapter: AssociatedActionSourceAdapter,
    block: AssociatedActionID,
    threshold: ThresholdDemand,
) -> None:
    demand = SourceImageDemand("threshold", (threshold,))
    image = scheduler.source_image_demanded(
        adapter, AssociatedScalarSource(ExactRational(1, 2), threshold), block, demand
    )
    assert scheduler.source_projection(adapter, image, demand).value is True
    assert scheduler.source_first_failure(adapter, image) == 1


def test_source_only_scheduler_accepts_a_certified_safe_composite() -> None:
    (
        ledger,
        scheduler,
        _unused_arena_binding,
        adapter,
        _unused_decrement_binding,
        block,
    ) = _decrement_fixture()
    threshold = ThresholdDemand()
    demand = SourceImageDemand("threshold", (threshold,))
    image = scheduler.source_image_demanded(
        adapter,
        AssociatedScalarSource(ExactRational(3), threshold),
        block,
        demand,
    )
    assert scheduler.source_projection(adapter, image, demand).value is True
    assert scheduler.source_first_failure(adapter, image) is None
    assert ledger.counters["source_image_demanded_composite_applications"] == 1
    assert ledger.counters.get("source_image_primitive_applications", 0) == 0


def test_failing_composite_descends_to_the_first_leaf() -> None:
    _, scheduler, _unused_arena_binding, adapter, _unused_decrement_binding, block = (
        _decrement_fixture()
    )
    threshold = ThresholdDemand()
    demand = SourceImageDemand("threshold", (threshold,))
    image = scheduler.source_image_demanded(
        adapter,
        AssociatedScalarSource(ExactRational(3, 2), threshold),
        block,
        demand,
    )
    assert scheduler.source_projection(adapter, image, demand).value is False
    assert scheduler.source_first_failure(adapter, image) == 2


def test_recovering_final_value_does_not_hide_an_earlier_failure() -> None:
    ledger, scheduler, arena, adapter = _runtime()
    decrement = arena.admit(
        SaturatingAffineAction(offset=ExactRational(-1)), logical_extent=1
    )
    recover = arena.admit(
        SaturatingAffineAction(offset=ExactRational(2)), logical_extent=1
    )
    block = arena.compose(decrement, recover)
    threshold = ThresholdDemand()
    _assert_threshold_failure(scheduler, adapter, block, threshold)
    assert ledger.counters.get("source_image_demanded_composite_applications", 0) == 0


def test_weak_zero_threshold_does_not_accept_equality_as_no_recovery() -> None:
    _, scheduler, arena, adapter = _runtime()
    decrement = arena.admit(
        SaturatingAffineAction(offset=ExactRational(-1)), logical_extent=1
    )
    recover_to_zero = arena.admit(
        SaturatingAffineAction(offset=ExactRational(1), cap=ExactRational(0)),
        logical_extent=1,
    )
    block = arena.compose(decrement, recover_to_zero)
    threshold = ThresholdDemand(strict=False)
    _assert_threshold_failure(scheduler, adapter, block, threshold)


def test_infinite_source_is_projected_without_a_sentinel() -> None:
    _, scheduler, arena, adapter = _runtime()
    capped = arena.admit(
        SaturatingAffineAction(cap=ExactRational(-2)), logical_extent=1
    )
    threshold = ThresholdDemand()
    demand = SourceImageDemand("threshold", (threshold,))
    image = scheduler.source_image_demanded(
        adapter, AssociatedScalarSource(None, threshold), capped, demand
    )
    assert scheduler.source_projection(
        adapter, image, SourceImageDemand("value")
    ).value == ExactRational(-2)
    assert scheduler.source_first_failure(adapter, image) == 1


def test_source_only_scheduler_rejects_physical_execution_and_disposes_core() -> None:
    ledger, scheduler, arena, adapter = _runtime()
    scheduler.source_image(
        adapter, AssociatedScalarSource(ExactRational(1)), arena.identity
    )
    with pytest.raises(RuntimeError, match="source-only"):
        _ = scheduler.physical_supports
    scheduler.dispose_source_images()
    assert all(
        row.entries == 0
        for row in ledger.inventory()
        if row.role.startswith("source_image")
    )


def test_payload_audit_accepts_canonical_associated_records_and_rejects_forgery() -> (
    None
):
    ledger, scheduler, arena, adapter = _runtime()
    action = arena.admit(
        SaturatingAffineAction(
            ExactRational(2, 3), ExactRational(-5, 7), ExactRational(11, 13)
        )
    )
    scheduler.source_image(adapter, AssociatedScalarSource(ExactRational(1)), action)
    clean = audit_registered_payloads(ledger)
    assert (
        clean.forbidden_future_payloads,
        clean.unbounded_future_integers,
        clean.unknown_payloads,
    ) == (0, 0, 0)
    coefficient = arena.semantic(action).scale
    object.__setattr__(coefficient, "numerator", 4)
    object.__setattr__(coefficient, "denominator", 6)
    damaged = audit_registered_payloads(ledger)
    assert damaged.forbidden_future_payloads > 0


@pytest.mark.parametrize("poison", ("semantic", "absorption"))
def test_warm_image_rejects_reflected_action_poisoning(poison: str) -> None:
    _, scheduler, arena, adapter = _runtime()
    action = arena.admit(
        SaturatingAffineAction(offset=ExactRational(-1)), logical_extent=1
    )
    source = AssociatedScalarSource(ExactRational(2))
    scheduler.source_image(adapter, source, action)
    if poison == "semantic":
        object.__setattr__(arena.semantic(action), "cap", ExactRational(0))
    else:
        record = arena.record(action)
        object.__setattr__(record, "zero_failure_absorbing", False)
    with pytest.raises(ValueError, match="publication was altered"):
        scheduler.source_image(adapter, source, action)
