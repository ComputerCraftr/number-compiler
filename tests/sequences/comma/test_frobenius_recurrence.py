"""Finite clock laws over admitted displacements; no branch-safety admission."""

from __future__ import annotations

from math import gcd

import pytest

from number_compiler.arithmetic.fields.morphism_core import AffineCocycle, binary_power
from number_compiler.sequences.comma.arithmetic import (
    cycle_power_residue,
    cycle_residue_period,
    cycle_transfer,
)
from number_compiler.sequences.comma.boundary_chart import BoundaryChart, chart_step

DISPLACEMENTS = tuple(
    sorted({cycle_transfer(f, d).displacement for f in range(1, 10) for d in range(10)})
)


@pytest.mark.parametrize("leading", range(1, 10))
def test_normalized_carry_action_is_independent_of_orbit_residue(leading: int) -> None:
    divisor = gcd(leading, 10)
    period = 10 // divisor
    stride = leading // divisor
    for phase in range(period):
        next_phase, carry = (phase + stride) % period, (phase + stride) // period
        for orbit in range(divisor):
            digit = orbit + divisor * phase
            assert (digit + leading) % 10 == orbit + divisor * next_phase
            assert (digit + leading) // 10 == carry
            # The carry action forgets orbit; its occurrence weight must not.
            transfer = cycle_transfer(leading, digit)
            assert transfer.displacement == 10 * (
                period * orbit + 5 * (period - 1) + stride
            )
    if divisor > 1:
        assert (
            cycle_transfer(leading, 0).displacement
            != cycle_transfer(leading, 1).displacement
        )


def test_nine_coprime_cores_preserve_full_frobenius_residues() -> None:
    cores: set[int] = set()
    for displacement in DISPLACEMENTS:
        modulus = displacement // 10
        core = modulus
        for prime in (2, 5):
            while core % prime == 0:
                core //= prime
        primary = modulus // core
        cores.add(core)
        assert gcd(primary, core) == 1
        assert 10**5 % primary == 0
        for phase in range(924):
            residue = cycle_power_residue(displacement, phase) // 10
            exponent = phase + 923
            assert residue % primary == 0
            assert residue % core == pow(10, exponent, core)
            # Restore the occurrence modulus; equal cores do not mean equal
            # full residues. This also handles the trivial core=1.
            lifted = primary * (pow(10, exponent, core) * pow(primary, -1, core) % core)
            assert residue == lifted
    assert cores == {1, 3, 7, 11, 13, 21, 23, 27, 29}


@pytest.mark.algebra
@pytest.mark.parametrize("displacement", DISPLACEMENTS)
def test_raw_frobenius_clock_including_924_wrap(displacement: int) -> None:
    modulus = displacement // 10
    for phase in range(924):
        power = cycle_power_residue(displacement, phase)
        # This independent exponent is congruent modulo the complete clock,
        # rather than using the implementation's short-period projection.
        exponent = phase if phase >= 5 else phase + 924
        assert power == pow(10, exponent, displacement)
        assert power % 10 == 0
        successor = cycle_power_residue(displacement, (phase + 1) % 924) // 10
        assert successor == 10 * (power // 10) % modulus


@pytest.mark.algebra
@pytest.mark.parametrize("displacement", DISPLACEMENTS)
def test_reduced_affine_blocks_and_diagonal(displacement: int) -> None:
    modulus = displacement // 10
    period = cycle_residue_period(displacement)
    orbit = tuple(cycle_power_residue(displacement, r) // 10 for r in range(period))
    seed = orbit[0]
    divisor = modulus
    for power in orbit:
        divisor = gcd(divisor, power - seed)
    reduced_modulus = modulus // divisor
    assert 9 * seed % divisor == 0
    step = AffineCocycle(10 % reduced_modulus, (9 * seed // divisor) % reduced_modulus)

    def multiply(left: int, right: int) -> int:
        return left * right % reduced_modulus

    def add(left: int, right: int) -> int:
        return (left + right) % reduced_modulus

    def compose(
        left: AffineCocycle[int], right: AffineCocycle[int]
    ) -> AffineCocycle[int]:
        return left.then(right, multiply=multiply, add=add)

    for span in (1, 2, 4, 8, 16, 32):
        block = binary_power(
            step,
            span,
            identity=AffineCocycle(1 % reduced_modulus, 0),
            compose=compose,
        ).value
        squared = compose(block, block)
        assert squared.multiplier == block.multiplier**2 % reduced_modulus
        assert squared.addend == (block.multiplier + 1) * block.addend % reduced_modulus
        raw_factor = pow(10, span, modulus)
        assert pow(10, 2 * span, modulus) == raw_factor**2 % modulus
        for phase, power in enumerate(orbit):
            target = orbit[(phase + span) % period]
            encoded = (power - seed) // divisor % reduced_modulus
            result = block.apply(encoded, multiply=multiply, add=add)
            assert (seed + divisor * result) % modulus == target
            for spatial in range(modulus):
                innovation = (spatial - power) % modulus
                assert (
                    raw_factor * innovation + (1 - raw_factor) * spatial
                ) % modulus == (spatial - target) % modulus
    if period % 2 == 0:
        half = binary_power(
            step,
            period // 2,
            identity=AffineCocycle(1 % reduced_modulus, 0),
            compose=compose,
        ).value
        assert half.multiplier == (-1) % reduced_modulus
        center = half.addend * pow(2, -1, reduced_modulus) % reduced_modulus
        for power in orbit:
            encoded = (power - seed) // divisor % reduced_modulus
            reflected = half.apply(encoded, multiply=multiply, add=add)
            assert (reflected - center) % reduced_modulus == -(
                encoded - center
            ) % reduced_modulus


def test_fixed_clock_uses_charged_seed_without_modular_power(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden_power(*args: object) -> int:
        raise AssertionError("a fixed raw clock must not recompute modular powers")

    monkeypatch.setattr("builtins.pow", forbidden_power)
    for displacement in DISPLACEMENTS:
        if cycle_residue_period(displacement) != 1:
            continue
        charges: list[int] = []
        for phase in (0, 5, 923):
            assert cycle_power_residue(
                displacement, phase, charge_bits=charges.append
            ) == (100_000 % displacement)
        assert charges == [17 + displacement.bit_length()] * 3


@pytest.mark.parametrize("delta", (0, 1, 923, 924))
def test_chart_uses_receiving_clock_and_preserves_symbolic_weight(delta: int) -> None:
    residue = 923
    for leading in range(1, 10):
        offset = 17
        transfer = cycle_transfer(leading, offset % 10)
        chart = BoundaryChart("entry", leading, delta, offset)
        move = chart_step(residue, chart)
        phase = (residue + delta) % 924
        exponent = phase if phase >= 5 else phase + 924
        minimum = 1 + int(leading < 9)
        headroom = (
            minimum
            + (pow(10, exponent, transfer.displacement) - offset - minimum)
            % transfer.displacement
        )
        assert move.next_chart == BoundaryChart("near", leading, delta, headroom)
        assert move.weight.exponent_delta == delta
        assert move.weight.scale == transfer.period
        assert move.weight.denominator == transfer.displacement
        assert move.weight.offset == -transfer.period * (offset + headroom)
