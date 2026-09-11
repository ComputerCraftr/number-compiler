"""Public radix projection consumes the authenticated tile application."""

from copy import copy
from typing import Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.radix_division import SymbolicBinaryDivisionEffect
from number_compiler.hashlife.execution.tile_scheduler import TileApplication
from number_compiler.hashlife.observation.tile_projection import LazyProjection
from number_compiler.hashlife.tiles.tiles import TileArena
from number_compiler.projection.lazy_radix import collatz_radix_digit
from number_compiler.projection.tile_radix import TileRadixObservation
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm


def _exact(seed: int, steps: int) -> int:
    for _ in range(steps):
        seed = 3 * seed + 1 if seed & 1 else seed // 2
    return seed


def _observation(term: PoweredCollatzTerm, radix: int) -> TileRadixObservation:
    projection = term._point_index()._lazy_application
    assert type(projection) is LazyProjection
    return TileRadixObservation(projection, radix)


def test_symbolic_division_definition_has_complete_fixed_semantics() -> None:
    radix = (1 << 63) - 25
    effect = SymbolicBinaryDivisionEffect(radix)
    assert effect.boundary_universe(BoundarySide.RIGHT) is None
    assert effect.boundary_universe(BoundarySide.LEFT) == (0,)
    with pytest.raises(ValueError, match="malformed fixed semantics"):
        SymbolicBinaryDivisionEffect(radix, exponent=2)
    with pytest.raises(TypeError, match="exact integer"):
        effect.boundary_universe(BoundarySide.RIGHT, max_states=True)


@pytest.mark.parametrize("radix", (3, 6, 10, 12))
@pytest.mark.parametrize("seed,steps", ((27, 8), (140137, 11), (28, 3)))
@pytest.mark.validation  # Full-digit matrix through public Collatz and radix paths.
def test_general_radix_digits_do_not_replay_binary_points(
    monkeypatch: pytest.MonkeyPatch, radix: int, seed: int, steps: int
) -> None:
    term = PoweredCollatzTerm(seed, steps)
    expected = _exact(seed, steps)

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("radix projection replayed a binary scalar API")

    monkeypatch.setattr(PoweredCollatzTerm, "digit", forbidden)
    coordinate = 0
    while expected:
        assert collatz_radix_digit(term, radix, coordinate) == expected % radix
        expected //= radix
        coordinate += 1
    with pytest.raises(IndexError):
        collatz_radix_digit(term, radix, coordinate)
    counters = term._ledger.counters
    assert counters.get("radix_source_bit_visits", 0) == 0
    assert counters.get("sequential_generation_advances", 0) == 0
    assert counters.get("tile_radix_interface_observations", 0) > 0


def test_warm_radix_parent_does_not_emit_or_compile_descendants(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = PoweredCollatzTerm(140137, 11)
    observation = _observation(term, 3)
    assert observation.digit(5) == 2
    before = term._ledger.snapshot()

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("warm parent descended into a primitive")

    monkeypatch.setattr(type(observation.adapter), "primitive_law", forbidden)
    monkeypatch.setattr(TileArena, "point", forbidden)
    assert observation.digit(5) == 2
    after = term._ledger.snapshot()
    assert (after.nodes, after.entries) == (before.nodes, before.entries)


def test_copied_projection_cannot_be_substituted() -> None:
    term = PoweredCollatzTerm(27, 4)
    projection = term._point_index()._lazy_application
    assert type(projection) is LazyProjection
    forged = copy(projection)
    before = term._ledger.snapshot()
    with pytest.raises(ValueError, match="was not issued"):
        TileRadixObservation(forged, 3)
    after = term._ledger.snapshot()
    assert (after.nodes, after.entries) == (before.nodes, before.entries)


def test_large_radix_executes_through_the_symbolic_tile_interface() -> None:
    radix = (1 << 63) - 25
    term = PoweredCollatzTerm((1 << 120) + 27, 3)
    expected = _exact((1 << 120) + 27, 3)
    assert collatz_radix_digit(term, radix, 0) == expected % radix
    assert collatz_radix_digit(term, radix, 1) == expected // radix
    with pytest.raises(IndexError):
        collatz_radix_digit(term, radix, 2)
    observation = _observation(term, radix)
    effect = observation.adapter.kernels.kernel(
        observation.adapter._action(observation.division).kernel
    ).effect
    assert type(effect) is SymbolicBinaryDivisionEffect
    high_state = 2 * (radix - 1) + 1
    assert effect.boundary_universe(BoundarySide.RIGHT) is None
    assert effect.advance(BoundarySide.RIGHT, high_state, 1) == 2 * (radix - 1) + 1
    assert effect.emit(0, 1, high_state) == 1
    record = observation.adapter._action(observation.division)
    assert record.cocycle.physical_ticks == record.cocycle.event_weight == 0
    assert record.cocycle.frame_shift == 0
    assert record.spatial_events_add is False
    assert term._ledger.counters.get("higher_concrete_continuation_evaluations", 0) == 0
    assert term._ledger.counters.get("symbolic_tile_division_leaf_compilations", 0) > 0
    report = audit_registered_payloads(term._ledger)
    assert (report.forbidden_future_payloads, report.unbounded_future_integers) == (
        0,
        0,
    )


def test_radix_action_is_bounded_and_payload_audited() -> None:
    term = PoweredCollatzTerm(140137, 11)
    observation = _observation(term, 3)
    assert observation.digit(10) == _exact(140137, 11) // 3**10 % 3
    action = observation.adapter._action(observation.division)
    kernel = observation.adapter.kernels.kernel(action.kernel).effect
    assert type(kernel) is SymbolicBinaryDivisionEffect
    assert kernel.radix == 3
    audit = audit_registered_payloads(term._ledger)
    assert (audit.forbidden_future_payloads, audit.unbounded_future_integers) == (0, 0)


def test_radix_observation_owns_no_continuation_or_future_word() -> None:
    term = PoweredCollatzTerm(140137, 11)
    observation = _observation(term, 3)
    assert observation.digit(10) == _exact(140137, 11) // 3**10 % 3
    for application in observation._apps.values():
        assert type(application) is TileApplication
        assert not any(
            hasattr(application, name)
            for name in ("provider", "continuation", "digits", "word", "tail")
        )


@pytest.mark.parametrize("seed", (1, 2, 4))
@pytest.mark.parametrize("steps", (3, 4, 5, 11))
@pytest.mark.parametrize("radix", (3, 6, 10, 12))
def test_fixed_cycle_phases_retain_the_certified_shortcut(
    seed: int, steps: int, radix: int
) -> None:
    term = PoweredCollatzTerm(seed, steps)
    expected = _exact(seed, steps)
    index = 0
    while expected:
        assert collatz_radix_digit(term, radix, index) == expected % radix
        expected //= radix
        index += 1
    with pytest.raises(IndexError):
        collatz_radix_digit(term, radix, index)
    assert (
        term._ledger.counters.get("tile_collatz_cycle_completions", 0)
        + term._ledger.counters.get("radix_fixed_cycle_observations", 0)
        > 0
    )
