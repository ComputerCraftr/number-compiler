"""Independent decimal oracles for the NC19 defect-clock production cutover."""

from __future__ import annotations

import json
import random
from dataclasses import replace

import pytest

from number_compiler.api import cli
from number_compiler.sequences.double_reverse.temporal_defect_quotient import (
    DefectAffineClock,
    FourSymbolSpatialQuotient,
    defect_from_normalized_suffix,
)
from tests.sequences.double_reverse.packet_helpers import (
    integer_field,
    object_list,
    object_mapping,
    string_field,
)


def reverse_double(x: int) -> int:
    return 2 * int(str(x)[::-1])


def full_mask(x: int) -> int:
    return int("".join("1" if int(c) >= 5 else "0" for c in str(x)))


def check_independent_defect(x: int, width: int) -> None:
    first = reverse_double(reverse_double(x))
    second = reverse_double(reverse_double(first))
    carry_x = full_mask(x)
    carry_first = full_mask(first)
    g0 = int(x % 10 >= 5)
    g1 = int(first % 10 >= 5)
    if g0 + g1 != 1:
        return
    source = tuple(map(int, str(x)))
    low = ((0,) * (width + 4) + source)[-(width + 4) :]
    action = defect_from_normalized_suffix(low, width)
    j_full = 4 * carry_x + (carry_first // 10 if g1 == 0 else carry_first)
    assert action.combined_decimal == j_full % 10**width
    assert action.input_modulus == x % (2 * 10**width)
    assert action.output_modulus == second % (2 * 10**width)
    assert action.first_growth == g0 and action.second_growth == g1
    assert action.combined_decimal == 4 * action.first_carries + action.second_carries
    assert set(action.emission_digits()) <= set("0145")
    assert set(action.base5_digits()) <= set("0123")
    assert len(action.base5_digits()) == width
    assert DefectAffineClock.from_defect(action).apply(x) == action.output_modulus


def test_exact_two_direction_arithmetic_many_sources() -> None:
    rng = random.Random(0x19)
    for seed in (1, 5, 168, 196, 2882, 7777, 17019868):
        x = seed
        for _ in range(35):
            if x % 10:
                check_independent_defect(x, 1)
                check_independent_defect(x, 7)
                check_independent_defect(x, 17)
            x = reverse_double(reverse_double(x))
    for _ in range(2500):
        x = rng.randrange(1, 10**40)
        if x % 10:
            check_independent_defect(x, rng.randrange(1, 33))


def test_four_symbol_defect_rejects_boolean_and_out_of_range_fields() -> None:
    defect = defect_from_normalized_suffix((0, 0, 0, 1, 6, 8), 2)
    malformed = (
        replace(defect, first_growth=True),
        replace(defect, second_growth=False),
        replace(defect, width=0),
        replace(defect, first_carries=100),
        replace(defect, combined_decimal=100),
        replace(defect, combined_base5=25),
        replace(defect, input_modulus=200),
    )
    for candidate in malformed:
        with pytest.raises(ValueError):
            candidate.verify()


def test_affine_temporal_composition_and_power() -> None:
    rng = random.Random(2026)
    for width in (1, 2, 7, 16):
        for _ in range(80):
            x = rng.randrange(1, 10**26)
            if x % 10 == 0:
                continue
            local = ((0,) * (width + 4) + tuple(map(int, str(x))))[-(width + 4) :]
            try:
                defect = defect_from_normalized_suffix(local, width)
            except ValueError:
                continue
            step = DefectAffineClock.from_defect(defect)
            q = rng.randrange(1, 50)
            powered = step.power(q)
            repeated = DefectAffineClock.identity(width)
            for _ in range(q):
                repeated = repeated.then(step)
            assert powered == repeated
            assert step.then(step).then(step) == step.then(step.then(step))
            assert powered.steps == q
        # The homogeneous macro multiplier dies in this 10-adic projection.
        assert (
            DefectAffineClock(
                width, width, pow(160, width, 2 * 10**width), 0
            ).multiplier
            == 0
        )
    assert DefectAffineClock(7, 1, 160, 0).power(10**14).steps == 10**14


def test_four_symbol_spatial_quotient_and_repeat() -> None:
    rng = random.Random(10)
    for width in (1, 2, 7, 16):
        for _ in range(100):
            low = "".join(rng.choice("0145") for _ in range(rng.randrange(1, 25)))
            high = "".join(rng.choice("0145") for _ in range(rng.randrange(1, 25)))
            joined = FourSymbolSpatialQuotient.from_digits(low, width).then(
                FourSymbolSpatialQuotient.from_digits(high, width)
            )
            literal = FourSymbolSpatialQuotient.from_digits(high + low, width)
            assert joined == literal
        block = FourSymbolSpatialQuotient.from_digits("5410", width)
        assert block.power(11) == FourSymbolSpatialQuotient.from_digits(
            "5410" * 11, width
        )
        huge = block.power(10**14)
        assert huge.length == 4 * 10**14
        assert huge.decimal == int(("5410" * (width // 4 + 2))[-width:])


@pytest.mark.parametrize("seed", [1, 168, 196])
def test_production_defect_clock_matches_exact_integer_oracle(
    seed: int, capsys: pytest.CaptureFixture[str]
) -> None:
    n = 128
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                str(seed),
                "--nth",
                str(n),
                "--no-value",
                "--format",
                "json",
                "--info",
                "temporal.defect-clock",
                "--temporal-defect-digits",
                "12",
                "--temporal-period-samples",
                "12",
            ]
        )
        == 0
    )
    raw_packet: object = json.loads(capsys.readouterr().out)
    packet = object_mapping(raw_packet)
    info = object_mapping(packet["info"])
    out = object_mapping(info["temporal.defect-clock"])
    assert out["status"] == "available"
    assert out["infinite_period_certified"] is False
    assert out["independent_intermediate_cones"] == 0
    x = seed
    terms: list[int] = [x]
    for _ in range(n + 3):
        x = reverse_double(x)
        terms.append(x)
    for raw_row in object_list(out["rows"]):
        row = object_mapping(raw_row)
        gen = integer_field(row, "generation")
        assert 0 <= gen <= n - 4
        x0, x2, x4 = terms[gen], terms[gen + 2], terms[gen + 4]
        g0 = int(x0 % 10 >= 5)
        g1 = int(x2 % 10 >= 5)
        j = 4 * full_mask(x0) + (full_mask(x2) // 10 if g1 == 0 else full_mask(x2))
        assert string_field(row, "defect_decimal") == str(j % 10**12).zfill(12)
        assert integer_field(row, "source_mod_2x10w") == x0 % (2 * 10**12)
        assert integer_field(row, "target_mod_2x10w") == x4 % (2 * 10**12)
        assert row["growth_bits"] == [g0, g1]
        assert set(string_field(row, "defect_base5")) <= set("0123")
    assert out["signed_cocycle_temporal_seam_verified"] is True


def test_contraction_does_not_issue_false_defect_clock(
    capsys: pytest.CaptureFixture[str],
) -> None:
    # The scalar source operation loses a zero in the reversal. The bounded
    # defect issuer must refuse that phase rather than manufacture a growth bit.
    with pytest.raises(ValueError, match="nonzero units"):
        defect_from_normalized_suffix((0, 0, 0, 0, 1, 0), 2)
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "0",
                "--nth",
                "16",
                "--no-value",
                "--format",
                "json",
                "--info",
                "temporal.defect-clock",
            ]
        )
        == 3
    )
    raw_packet: object = json.loads(capsys.readouterr().out)
    packet = object_mapping(raw_packet)
    info = object_mapping(packet["info"])
    out = object_mapping(info["temporal.defect-clock"])
    assert out["status"] == "unavailable"
    assert out["infinite_period_certified"] is False


def test_shared_halo_reproduces_64_source_defects_and_hierarchy(
    capsys: pytest.CaptureFixture[str],
) -> None:
    seed, n, digits, count = 168, 512, 18, 64
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                str(seed),
                "--nth",
                str(n),
                "--no-value",
                "--format",
                "json",
                "--info",
                "temporal.defect-clock",
                "--temporal-defect-digits",
                str(digits),
                "--temporal-period-samples",
                str(count),
                "--temporal-period-max-lag",
                "36",
            ]
        )
        == 0
    )
    raw_packet: object = json.loads(capsys.readouterr().out)
    outer = object_mapping(raw_packet)
    info = object_mapping(outer["info"])
    packet = object_mapping(info["temporal.defect-clock"])
    assert packet["shared_source_halo"] is True
    assert packet["local_t_squared_steps"] == 2 * (count - 1)
    assert packet["samples"] == count
    expected_changes = [(1, 1), (2, 3), (7, 12)]
    actual_changes: list[tuple[int, int]] = []
    for raw_entry in object_list(packet["defect_suffix_period_hierarchy"]):
        entry = object_mapping(raw_entry)
        raw_candidate = entry["observed_tail_candidate"]
        if raw_candidate is None:
            continue
        candidate = object_mapping(raw_candidate)
        actual_changes.append(
            (
                integer_field(entry, "suffix_digits"),
                integer_field(candidate, "observed_lag"),
            )
        )
    assert actual_changes[:3] == expected_changes
    terms: list[int] = [seed]
    for _ in range(n):
        terms.append(reverse_double(terms[-1]))
    for raw_row in object_list(packet["rows"]):
        row = object_mapping(raw_row)
        gen = integer_field(row, "generation")
        first, second = terms[gen], terms[gen + 2]
        c0 = full_mask(first)
        c1 = full_mask(second)
        growth1 = int(second % 10 >= 5)
        j = 4 * c0 + (c1 // 10 if growth1 == 0 else c1)
        assert string_field(row, "defect_decimal") == str(j % 10**digits).zfill(digits)
        assert integer_field(row, "target_mod_2x10w") == terms[gen + 4] % (
            2 * 10**digits
        )


def test_existing_seed_morphism_period_path_uses_same_defect_action(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "196",
                "--nth",
                "256",
                "--no-value",
                "--format",
                "json",
                "--info",
                "temporal.seed-morphism",
                "--temporal-period-samples",
                "24",
                "--temporal-defect-digits",
                "12",
            ]
        )
        == 0
    )
    raw_packet: object = json.loads(capsys.readouterr().out)
    packet = object_mapping(raw_packet)
    info = object_mapping(packet["info"])
    morphism = object_mapping(info["temporal.seed-morphism"])
    clock = object_mapping(morphism["period_observations"])
    assert clock["status"] == "available"
    assert clock["shared_source_halo"] is True
    assert clock["full_endpoint_suffix_verified"] is True
    assert clock["signed_cocycle_temporal_seam_verified"] is True
    assert clock["infinite_period_certified"] is False
    assert "period_observations" in morphism
