"""Cold endpoint reuse and mod-90 factors of the iterative 2rev10 scheduler."""

from __future__ import annotations

import pytest

from number_compiler.sequences.double_reverse import temporal_seed_cli
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.source_bound_bank import (
    PointedBankSource,
)
from number_compiler.sequences.double_reverse.temporal_hashlife import (
    edge_phase_of_integer,
)
from number_compiler.sequences.double_reverse.temporal_laurent_return import (
    physical_carry_field_borrow_projection,
)
from number_compiler.sequences.double_reverse.temporal_seed_morphism import (
    CertifiedSeedOrbitMorphism,
    certified_seed_orbit_morphism,
)
from tests.sequences.double_reverse.packet_helpers import integer_field, object_mapping


def _reverse(value: int) -> int:
    return int(str(value)[::-1])


def _uncarried_field(value: int) -> int:
    return int("".join(str(2 * int(digit)) for digit in str(value)))


def test_uncarried_digit_field_has_exact_mod90_factor() -> None:
    for value in range(1, 10001):
        assert _uncarried_field(value) % 90 == 2 * value % 90


@pytest.mark.parametrize(("seed", "period"), ((1, 12), (168, 4), (196, 12)))
def test_authenticated_phase_factors_match_literal_physical_orbit(
    seed: int, period: int
) -> None:
    value = seed
    checked = 0
    for _ in range(84):
        phase = edge_phase_of_integer(value)
        if phase is None:
            value = 2 * _reverse(value)
            continue
        packet = physical_carry_field_borrow_projection(
            target_phase=phase,
            physical_mod198=value % 198,
            seed_mod9=seed % 9,
        )
        assert packet["physical_target_mod990"] == value % 990
        assert packet["carry_field_mod90"] == _uncarried_field(value) % 90
        assert packet["carry_field_primitive_period_physical_steps"] == period
        next_value = 2 * _reverse(value)
        assert packet["physical_subtraction_borrow_low_digit"] == int(
            next_value % 10 < value % 10
        )
        checked += 1
        value = next_value
    assert checked > 0


def test_seed_morphism_packet_reuses_completed_scheduler_endpoint(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = certified_seed_orbit_morphism
    witnessed: list[int] = []

    def checked(
        source: PointedBankSource,
        *,
        steps: int,
        start_f_steps: int = 0,
        known_previous: CertifiedSeedOrbitMorphism | None = None,
        completed_term: DoubleReverseTerm | None = None,
    ) -> CertifiedSeedOrbitMorphism:
        if completed_term is None:
            raise AssertionError("seed morphism bypassed completed endpoint authority")
        completed = completed_term.issued_completed_endpoint_root()
        if completed is None:
            raise AssertionError("seed morphism received an unissued endpoint")
        witnessed.append(completed)
        return original(
            source,
            steps=steps,
            start_f_steps=start_f_steps,
            known_previous=known_previous,
            completed_term=completed_term,
        )

    monkeypatch.setattr(temporal_seed_cli, "certified_seed_orbit_morphism", checked)
    with DoubleReverseTerm(168, 256) as term:
        packet = temporal_seed_cli.seed_morphism_cli_packet(term)
        endpoint = object_mapping(packet["endpoint"])
        assert endpoint["full_digit_slp"] is True
        assert witnessed == [term.issued_completed_endpoint_root()]
        value = 168
        for _ in range(256):
            value = 2 * _reverse(value)
        laurent = object_mapping(packet["normalized_laurent_accumulator"])
        clock = object_mapping(laurent["physical_carry_field_borrow_clock"])
        assert integer_field(clock, "physical_target_mod990") == value % 990
        assert integer_field(clock, "carry_field_mod90") == _uncarried_field(value) % 90


@pytest.mark.parametrize(
    ("phase", "residue", "seed_residue"),
    (
        (-1, 168, 6),
        (4, 168, 6),
        (0, 198, 6),
        (0, 168, 9),
    ),
)
def test_mod90_projection_rejects_forged_clock_inputs(
    phase: int, residue: int, seed_residue: int
) -> None:
    with pytest.raises(ValueError):
        physical_carry_field_borrow_projection(
            target_phase=phase,
            physical_mod198=residue,
            seed_mod9=seed_residue,
        )
