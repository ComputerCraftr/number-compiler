"""Recursive radix images keep stage identity separate from exact leaf blocks."""

from typing import cast

import pytest

from devtools.proofs.radix_stage_images import (
    RadixDivisionImageArena,
    RadixDivisionImageID,
    RadixDivisionInterfaceID,
)
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.execution.radix_consumer import (
    RadixDivisionAction,
    RadixDivisionActionArena,
    RadixDivisionActionID,
)
from number_compiler.hashlife.observation.tile_projection import LazyProjection
from number_compiler.hashlife.tiles.tiles import TileArena
from number_compiler.projection.lazy_radix import RadixProjection, collatz_radix_digit
from number_compiler.projection.microblock_cache import MicroblockCache
from number_compiler.projection.tile_radix import TileRadixObservation
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm


def _observation(term: PoweredCollatzTerm, radix: int) -> TileRadixObservation:
    projection = term._point_index()._lazy_application
    assert type(projection) is LazyProjection
    return TileRadixObservation(projection, radix)


def test_division_images_are_strong_scoped_constant_size_records() -> None:
    ledger = ResourceLedger()
    arena = RadixDivisionImageArena(ledger, 3, 101)
    first = arena.advance(arena.source, 99)
    second = arena.advance(first, 97)
    assert arena.resolve(first).parent == arena.source
    assert arena.resolve(second).parent == first
    assert arena.resolve_interface(arena.interface).radix == 3
    assert not any(
        hasattr(arena.resolve(second), name)
        for name in ("digits", "blocks", "remainder", "quotient", "payload")
    )
    ledger.evict_query_memos()
    assert arena.resolve(second).width == 97
    assert arena.advance(first, 97) == second


@pytest.mark.parametrize("radix", (3, 6, 10, 12))
def test_division_consumer_primitive_is_the_exact_bounded_kernel(radix: int) -> None:
    arena = RadixDivisionActionArena(ResourceLedger(), radix)
    for carry in range(radix):
        for symbol in (0, 1):
            inputs = {
                arena.carry_port.variable: carry,
                arena.symbol_port.variable: symbol,
            }
            total = 2 * carry + symbol
            assert (
                arena.bits.evaluate(
                    arena.primitive_semantics.remainder,
                    inputs,
                )
                == total % radix
            )
            assert (
                arena.bits.evaluate(
                    arena.primitive_semantics.quotient,
                    inputs,
                )
                == total // radix
            )


def test_division_consumer_power_is_canonical_logarithmic_and_scoped() -> None:
    ledger = ResourceLedger()
    arena = RadixDivisionActionArena(ledger, 3)
    powered = arena.power(257)
    assert arena.resolve(powered).exponent == 257
    assert arena.power(257) == powered
    assert len(arena._nodes) <= 2 * (257).bit_length() + 1
    foreign = RadixDivisionActionArena(ResourceLedger(), 3)
    for invalid in (
        foreign.primitive,
        powered.local_id,
        True,
        float(powered.local_id),
        RadixDivisionActionID(powered.owner, "other-action", powered.local_id),
    ):
        with pytest.raises((TypeError, ValueError)):
            arena.resolve(cast(RadixDivisionActionID, invalid))


def test_radix_provider_action_roots_are_audited_and_counted_as_field_actions() -> None:
    term = PoweredCollatzTerm(27, 2)
    observation = _observation(term, 3)
    division = observation.adapter.power(observation.division, 9)
    observation.adapter.validate_action(division)

    audit = audit_registered_payloads(term._ledger)
    assert audit == type(audit)(0, 0, 0)
    report = collect_ledger_metrics(term._ledger)
    radix_rows = tuple(
        row
        for row in report.resource_inventory
        if row.name.startswith("primitive-tile-actions-")
        and row.name.endswith("-nodes")
    )
    assert len(radix_rows) == 1
    assert radix_rows[0].role == "field_action"
    assert report.field_action_nodes >= sum(
        row.observed_nodes or 0 for row in radix_rows
    )
    assert report.field_action_publications >= sum(
        row.observed_nodes or 0 for row in radix_rows
    )


def test_radix_action_semantic_records_are_append_only_and_remain_auditable() -> None:
    ledger = ResourceLedger()
    arena = RadixDivisionActionArena(ledger, 3)
    assert audit_registered_payloads(ledger).forbidden_future_payloads == 0
    with pytest.raises(TypeError, match="append-only"):
        arena._nodes[0] = RadixDivisionAction(5, 1)
    assert audit_registered_payloads(ledger).forbidden_future_payloads == 0


def test_division_image_ids_reject_foreign_wrong_sort_and_numeric_aliases() -> None:
    first = RadixDivisionImageArena(ResourceLedger(), 3, 7)
    foreign = RadixDivisionImageArena(ResourceLedger(), 3, 7)
    for value in (
        foreign.source,
        first.source.local_id,
        True,
        float(first.source.local_id),
        RadixDivisionInterfaceID(
            first.token, "radix-division-interface", first.source.local_id
        ),
    ):
        with pytest.raises((TypeError, ValueError)):
            first.resolve(cast(RadixDivisionImageID, value))
    stale = RadixDivisionImageID(first.token, "radix-division-image", 99)
    with pytest.raises(ValueError):
        first.resolve(stale)


def test_projection_exposes_no_stage_zero_replay_adapter() -> None:
    ledger = ResourceLedger()
    cache = MicroblockCache(ledger, ArenaToken("test-programs"), lambda _program: None)
    projection = RadixProjection(3, 17, ledger, cache)
    assert not any(
        hasattr(projection, name)
        for name in (
            "_ensure_block_stage",
            "_fill_source_stage",
            "_compute_block_stage",
            "_resolve_division_image",
            "_division_images",
            "_image_bindings",
        )
    )


def test_new_digit_uses_one_provider_observation_without_stage_replay() -> None:
    term = PoweredCollatzTerm(140137, 11)
    assert collatz_radix_digit(term, 3, 5) == 2
    evaluations = term._ledger.counters["radix_provider_digit_evaluations"]
    assert collatz_radix_digit(term, 3, 6) == 0
    assert term._ledger.counters["radix_provider_digit_evaluations"] == evaluations + 1
    assert term._ledger.counters.get("radix_microblock_stage_evaluations", 0) == 0
    assert term._ledger.counters.get("radix_microblock_source_fills", 0) == 0
    assert term._ledger.counters["radix_provider_digit_requests"] == 2
    assert term._ledger.counters.get("radix_provider_digit_early_hits", 0) == 0


def test_new_radix_consumer_reuses_complete_leaf_interfaces(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    exact = 140137
    for _ in range(11):
        exact = exact // 2 if exact % 2 == 0 else 3 * exact + 1
    term = PoweredCollatzTerm(140137, 11)
    observation = _observation(term, 3)
    assert observation.digit(0) == exact % 3
    hits_before = term._ledger.counters.get("tile_radix_observation_early_hits", 0)
    monkeypatch.setattr(
        TileArena,
        "point",
        lambda *_args: pytest.fail("reread the original source leaf"),
    )
    assert observation.digit(0) == exact % 3
    assert (
        term._ledger.counters.get("tile_radix_observation_early_hits", 0) > hits_before
    )


@pytest.mark.parametrize("radix", (3, 6, 10, 12))
@pytest.mark.validation  # Four-radix public provider integration.
def test_radix_projection_consumes_sealed_provider_without_public_term_replay(
    monkeypatch: pytest.MonkeyPatch,
    radix: int,
) -> None:
    term = PoweredCollatzTerm(140137, 11)
    expected = collatz_radix_digit(term, radix, 2)
    term = PoweredCollatzTerm(140137, 11)
    monkeypatch.setattr(
        PoweredCollatzTerm,
        "digit",
        lambda *_args: (_ for _ in ()).throw(AssertionError("public digit replay")),
    )
    assert collatz_radix_digit(term, radix, 2) == expected
