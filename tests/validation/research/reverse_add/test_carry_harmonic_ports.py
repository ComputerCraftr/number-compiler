"""Port-conditioned harmonic laws and limits of their spatial quotient."""

from itertools import product
from typing import cast

import pytest

from devtools.verification.carry_harmonic_port_probe import direct_rows, finite
from devtools.verification.carry_harmonic_ports import (
    CarryHarmonicPortAction as Action,
)
from devtools.verification.carry_harmonic_ports import (
    population_harmonics,
    populations,
    prefix_harmonics,
)
from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    scan_carry_automaton,
    value_carry_fn,
)
from number_compiler.arithmetic.carry.event_memory import pair_step


def test_phase_inversion_composition_and_length_indexed_identity() -> None:
    for even, odd in product(range(5), repeat=2):
        assert populations(*population_harmonics(even, odd)) == (even, odd)
    eq2 = Action.from_domains((CarryFn.ID,) * 2)
    eq4 = eq2.then(eq2)
    eq12 = Action.from_domains((CarryFn.ID,) * 12)
    assert eq2.rows != eq4.rows  # Same phase and carry function are insufficient.
    assert eq2.rows == eq12.rows
    assert eq2.length_indexed_code() == eq4.length_indexed_code() == (0,)
    assert eq2.rows == ((0, 0, 0), (1, 3, 4))
    assert eq2.then(Action.empty()) == Action.empty().then(eq2) == eq2
    with pytest.raises(ValueError):
        Action(-1, eq2.rows)


def test_complete_finite_generator_closure_and_fixed_length_counts() -> None:
    result = finite()
    assert result["untyped_emission_rows"] == 510
    assert result["phase_typed_states"] == 1010
    assert result["all_eq_emissions"] == 10
    counts = result["fixed_length_counts"]
    assert isinstance(counts, list)
    expected = {
        1: (3, 3),
        2: (7, 7),
        4: (27, 15),
        6: (69, 21),
        8: (141, 21),
        12: (335, 21),
        16: (473, 21),
        18: (501, 21),
    }
    for row in cast(list[dict[str, int]], counts):
        assert row["punctured_border"] == row["border"] - 1
        if row["width"] >= 6:
            assert row["punctured_border"] == 20
        if row["width"] in expected:
            assert (row["occupancy"], row["border"]) == expected[row["width"]]
        if row["width"] >= 18:
            assert row["occupancy"] == 501 and row["border"] == 21


def test_harmonic_kernel_is_separated_but_pointwise_carries_are_not_retained() -> None:
    left = Action.from_domains(value_carry_fn(v, 10) for v in (8,) * 9)
    right = Action.from_domains(value_carry_fn(v, 10) for v in (9,) + (10,) * 7 + (9,))
    assert left.rows == ((0, 0, 0), (0, 1, 1))
    assert right.rows == ((1, 0, 3), (1, 3, 2))
    # Equal emissions do not expose the individual interior carry ports.
    assert direct_rows((10, 0, 0, 0)) == direct_rows((0, 0, 10, 0))
    assert scan_carry_automaton((10, 0, 0, 0)).boundaries[1] == 1
    assert scan_carry_automaton((0, 0, 10, 0)).boundaries[1] == 0


def test_spatial_powering_does_not_reconstruct_carry_words(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import devtools.verification.carry_harmonic_ports as ports

    action = Action.leaf(CarryFn.ID)

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("spatial composition replayed a leaf or scanned values")

    monkeypatch.setattr(ports, "apply_carry_fn", forbidden)
    monkeypatch.setattr(ports, "harmonic_sum", forbidden)
    for _ in range(128):
        action = action.then(action)
    assert action.width == 2**128
    assert action.rows == ((0, 0, 0), (1, *prefix_harmonics(action.width)))


def test_spatial_action_is_not_a_temporal_successor_quotient() -> None:
    sources = ((4, 4), (8, 8))
    actions = [
        Action.from_domains(value_carry_fn(v, 10) for v in row) for row in sources
    ]
    assert actions[0] == actions[1]
    next_actions = [
        Action.from_domains(value_carry_fn(v, 10) for v in pair_step(row, 10)[0])
        for row in sources
    ]
    assert next_actions[0] != next_actions[1]
