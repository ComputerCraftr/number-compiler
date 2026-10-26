"""Independent fixed-sector p-adic event regressions for comma arithmetic."""

from __future__ import annotations

import pytest

from tests.sequences.comma.padic_event_oracle import (
    event_sign,
    fixed_sector_cycle,
    p_adic_cycle_period,
    primes_through,
    residue_event,
    valuation,
)


@pytest.mark.parametrize("prime", [2, 3, 5, 23, 29, 97])
def test_bounded_residue_identifies_gain_loss_and_neutral_events(prime: int) -> None:
    delta = prime
    modulus = prime * prime
    examples = (
        (modulus - delta, 1),
        (modulus, -1),
        (1, 0),
    )

    for value, expected in examples:
        assert residue_event(value, delta, prime) == expected
        assert event_sign(value, delta, prime) == expected


@pytest.mark.parametrize(
    ("value", "delta", "prime"),
    [(True, 1, 2), (1, True, 2), (1, 1, True)],
)
def test_event_inputs_reject_boolean_integer_aliases(
    value: int, delta: int, prime: int
) -> None:
    with pytest.raises(TypeError, match="exact integer"):
        event_sign(value, delta, prime)


def test_both_event_forms_and_clock_helpers_reject_boolean_coordinates() -> None:
    with pytest.raises(TypeError, match="exact integer"):
        residue_event(1, True, 2)
    with pytest.raises(TypeError, match="exact integer"):
        valuation(True, 2)
    with pytest.raises(TypeError, match="exact integer"):
        primes_through(True)
    with pytest.raises(TypeError, match="exact integer"):
        p_adic_cycle_period(2, 4, True)


@pytest.mark.parametrize(
    ("leading", "digit"), [(True, 0), (7, False), (0, 0), (10, 0), (7, 10)]
)
def test_sector_cycle_rejects_noncanonical_coordinates(
    leading: int, digit: int
) -> None:
    with pytest.raises((TypeError, ValueError)):
        fixed_sector_cycle(leading, digit)


def test_prime_clock_rejects_composites_and_nonpositive_increments() -> None:
    with pytest.raises(ValueError, match="prime"):
        p_adic_cycle_period(4, 87, 520)
    with pytest.raises(ValueError, match="positive"):
        p_adic_cycle_period(29, 0, 520)
    with pytest.raises(ValueError, match="positive"):
        p_adic_cycle_period(29, 87, 0)


def test_fixed_sector_cycles_keep_prime_channels_outside_mod_924() -> None:
    deltas = fixed_sector_cycle(7, 8)
    assert deltas == (87, 57, 27, 97, 67, 37, 7, 77, 47, 17)
    displacement = sum(deltas)
    assert displacement == 520

    assert valuation(displacement, 29) == 0
    assert p_adic_cycle_period(29, 87, displacement) == 29**2
    assert 924 % 29**2 != 0
    assert p_adic_cycle_period(2, 4, 8) == 1

    # The 97-adic channel is separate too: the fourth digit transition has
    # delta 97 and the same cycle displacement has 97-adic order zero.
    assert valuation(displacement, 97) == 0
    assert p_adic_cycle_period(97, 97, displacement) == 97**2
    assert 924 % 97**2 != 0


def test_29_adic_same_phase_witness_has_distinct_gain_and_loss() -> None:
    prime = 29
    delta = 87
    displacement = 520
    period = p_adic_cycle_period(prime, delta, displacement)
    base = 70_000_000_148
    modulus = prime**2
    inverse = pow(displacement, -1, modulus)
    loss_cycle = (-base * inverse) % modulus
    gain_cycle = (-(base + delta) * inverse) % modulus

    assert period == 841
    assert (loss_cycle, gain_cycle) == (37, 501)
    assert event_sign(base + loss_cycle * displacement, delta, prime) == -1
    assert event_sign(base + gain_cycle * displacement, delta, prime) == 1
    assert event_sign(base + period * displacement, delta, prime) == event_sign(
        base, delta, prime
    )


def test_event_residue_does_not_determine_valuation_magnitude() -> None:
    prime = 29
    shallow = prime**2 - prime
    deep = prime**4 - prime
    assert shallow % prime**2 == deep % prime**2
    assert residue_event(shallow, prime, prime) == 1
    assert residue_event(deep, prime, prime) == 1
    assert valuation(shallow + prime, prime) - valuation(shallow, prime) == 1
    assert valuation(deep + prime, prime) - valuation(deep, prime) == 3


def test_prime_events_are_not_limited_by_decimal_increment_factors() -> None:
    # The increment 1 has no prime factor, yet a larger prime can be gained
    # or lost. No finite list of increment factors covers this observer.
    assert residue_event(100, 1, 101) == event_sign(100, 1, 101) == 1
    assert residue_event(101, 1, 101) == event_sign(101, 1, 101) == -1


def test_fixed_sector_period_does_not_authorize_a_leading_digit_seam() -> None:
    leading = 7
    scale = 10**4
    lower = leading * scale
    upper = (leading + 1) * scale
    value = upper - 1
    delta = 97
    displacement = 520
    period = p_adic_cycle_period(97, delta, displacement)

    assert value % 10 == 9
    assert period == 97**2
    assert lower <= value < upper
    assert value + delta >= upper
    assert not (lower <= value < value + delta < upper)

    # The local event arithmetic can still be evaluated, but this crossing
    # must be handed to the authenticated next-sector chart before any clock
    # period is reused. This test does not choose or certify a B1 transition.
    assert event_sign(value, delta, 97) == residue_event(value, delta, 97)


@pytest.mark.validation
def test_exhaustive_fixed_sector_event_clock_matches_direct_valuations() -> None:
    """Full bounded differential grid; no global-sector or proof claim."""
    primes = primes_through(97)
    displacements: set[int] = set()
    event_checks = 0
    periodic_checks = 0
    maximum_period = 0

    for leading in range(1, 10):
        for entering_digit in range(10):
            deltas = fixed_sector_cycle(leading, entering_digit)
            displacement = sum(deltas)
            displacements.add(displacement)
            start = leading * 10**12 + entering_digit
            prefix = 0

            for digit_index, delta in enumerate(deltas):
                base = start + prefix
                digit = (entering_digit + digit_index * leading) % 10
                assert base % 10 == digit
                for prime in primes:
                    period = p_adic_cycle_period(prime, delta, displacement)
                    maximum_period = max(maximum_period, period)
                    for cycle_index in (0, 1, 7, 29):
                        value = base + cycle_index * displacement
                        shifted = value + period * displacement
                        sector_lower = leading * 10**12
                        sector_upper = (leading + 1) * 10**12
                        assert sector_lower <= value < value + delta < sector_upper
                        assert sector_lower <= shifted < shifted + delta < sector_upper
                        assert value % 10 == digit == shifted % 10

                        direct = event_sign(value, delta, prime)
                        assert direct == residue_event(value, delta, prime)
                        event_checks += 1
                        assert direct == event_sign(shifted, delta, prime)
                        periodic_checks += 1
                prefix += delta

            assert prefix == displacement

    assert len(displacements) == 17
    assert len(primes) == 25
    assert event_checks == 62_000
    assert periodic_checks == 62_000
    assert maximum_period == 9_409
