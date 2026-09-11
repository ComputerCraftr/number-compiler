"""Division activity cannot erase its carry or quotient output distinctions."""

from dataclasses import replace
from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.hashlife.observation.tile_projection import LazyProjection
from number_compiler.projection.tile_radix import TileRadixObservation
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm


def _observation() -> tuple[PoweredCollatzTerm, TileRadixObservation]:
    term = PoweredCollatzTerm(140137, 11)
    projection = term._point_index()._lazy_application
    assert type(projection) is LazyProjection
    return term, TileRadixObservation(projection, 3)


def test_division_output_preserves_remainder_and_activity_ports() -> None:
    _, observation = _observation()
    kernel = observation.adapter.primitive_law(observation.division)
    # State is 2 * remainder + higher-quotient activity.  Activity does not
    # alter the arithmetic remainder transition, while carry does.
    assert kernel.advance(BoundarySide.RIGHT, 0, 1) == 2
    assert kernel.advance(BoundarySide.RIGHT, 1, 1) == 3
    assert kernel.advance(BoundarySide.RIGHT, 2, 1) == 1
    assert kernel.emit(0, 1, 0) != kernel.emit(0, 1, 2)


@pytest.mark.parametrize("invalid", (True, 0.0, -1, (1 << 63) + 1))
def test_invalid_radix_rejects_before_application_publication(
    invalid: bool | float | int,
) -> None:
    term = PoweredCollatzTerm(27, 4)
    projection = term._point_index()._lazy_application
    assert type(projection) is LazyProjection
    before = term._ledger.snapshot()
    with pytest.raises((TypeError, ValueError)):
        TileRadixObservation(projection, invalid)  # type: ignore[arg-type]
    after = term._ledger.snapshot()
    assert (before.entries, before.nodes) == (after.entries, after.nodes)


def test_foreign_division_action_cannot_hit_warm_adapter_lookup() -> None:
    _, observation = _observation()
    _, foreign = _observation()
    invalid = replace(observation.division, owner=foreign.division.owner)
    before = observation.scheduler.ledger.snapshot()
    with pytest.raises(ValueError):
        observation.adapter.primitive_law(invalid)
    after = observation.scheduler.ledger.snapshot()
    assert (before.entries, before.nodes) == (after.entries, after.nodes)


def test_general_radix_cold_work_uses_tile_interfaces() -> None:
    term, observation = _observation()
    assert observation.digit(10) == 0
    counters = term._ledger.counters
    assert counters.get("tile_radix_interface_observations", 0) > 0
    assert counters.get("higher_runtime_summary_publications", 0) == 0
    assert counters.get("concrete_port_task_frames", 0) == 0
    assert counters.get("radix_source_bit_visits", 0) == 0


def test_repeated_tile_interface_hits_before_leaf_observation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    seed = (1 << 17) - 1
    term = PoweredCollatzTerm(seed, 1)
    observation = _observation_for(term, 3)
    expected_value = 3 * seed + 1
    expected: list[int] = []
    while expected_value:
        expected.append(expected_value % 3)
        expected_value //= 3
    assert observation.digit(0) == expected[0]

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("replayed the public binary point path")

    monkeypatch.setattr(PoweredCollatzTerm, "digit", forbidden)
    assert [observation.digit(index) for index in range(len(expected))] == expected
    assert term._ledger.counters.get("radix_source_bit_visits", 0) == 0


def _observation_for(term: PoweredCollatzTerm, radix: int) -> TileRadixObservation:
    projection = term._point_index()._lazy_application
    assert type(projection) is LazyProjection
    return TileRadixObservation(projection, radix)
