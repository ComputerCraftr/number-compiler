"""Independent carry-first Euclidean reconstruction for comma Entry cases.

This is a bounded regression oracle only. It computes the quotient residue
before reconstructing the legacy boundary packet and never constructs
``10**width``. It does not issue source or branch authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd

from tests.sequences.comma.padic_event_oracle import exact_integer, fixed_sector_cycle


@dataclass(frozen=True, slots=True)
class CarryFirstResult:
    leading: int
    suffix: int
    width: int
    cycle_length: int
    displacement: int
    guard: int
    euclidean_residue_mod_1600p: int
    quotient_mod_1600: int
    remainder: int
    exponent_mod_1600: int
    target_suffix: int
    carry_mod_32: int
    beta: int
    reconstructed_headroom: int
    legacy_headroom: int


@dataclass(frozen=True, slots=True)
class C1SaturationSummary:
    leading: int
    suffix: int
    cycle_length: int
    displacement: int
    carry_count_50: int
    return_period: int


@dataclass(frozen=True, slots=True)
class C1ReturnResidue:
    steps_mod_period: int
    target_suffix: int
    carry_mod_32: int


def c1_phase_cycle(
    leading: int, suffix: int
) -> tuple[tuple[int, ...], tuple[int, ...]]:
    """Return phase suffixes and prefix carries through one 50-step C1 cycle."""
    sector = exact_integer(leading, "leading")
    low_suffix = exact_integer(suffix, "suffix")
    if not 1 <= sector <= 9 or not 0 <= low_suffix < 100:
        raise ValueError("invalid fixed-sector C1 phase")
    current = low_suffix
    carries = 0
    suffixes = [current]
    carry_prefix = [carries]
    for _ in range(50):
        raw = current + 10 * (current % 10) + sector
        carry = raw // 100
        if carry not in (0, 1):
            raise AssertionError("one C1 transition produced a non-Boolean carry")
        current = raw % 100
        carries += carry
        suffixes.append(current)
        carry_prefix.append(carries)
    if current != low_suffix:
        raise AssertionError("the admitted fixed-sector C1 phase did not close at 50")
    return tuple(suffixes), tuple(carry_prefix)


def _c1_target_and_carry_mod_32(
    leading: int, suffix: int, exponent_mod_1600: int
) -> tuple[int, int]:
    suffixes, carry_prefix = c1_phase_cycle(leading, suffix)
    complete_cycles, tail = divmod(exponent_mod_1600, 50)
    cycle_carries = carry_prefix[50]
    target = suffixes[tail]
    carries = complete_cycles * cycle_carries + carry_prefix[tail]
    return target, carries % 32


def _cycle_displacement(leading: int, suffix: int) -> tuple[int, int]:
    increments = fixed_sector_cycle(leading, suffix % 10)
    return len(increments), sum(increments)


def c1_saturation_summary(leading: int, suffix: int) -> C1SaturationSummary:
    """Derive the adaptive mod-32 return period from one shared 50-cycle."""
    sector = exact_integer(leading, "leading")
    low_suffix = exact_integer(suffix, "suffix")
    suffixes, carry_prefix = c1_phase_cycle(sector, low_suffix)
    cycle_length, displacement = _cycle_displacement(sector, low_suffix)
    carry_count_50 = carry_prefix[50]
    if displacement != 2 * cycle_length * carry_count_50:
        raise AssertionError("C1 50-block carry count differs from P/(2L)")
    return_period = 50 * (32 // gcd(32, carry_count_50))
    if suffixes[50] != low_suffix:
        raise AssertionError("C1 phase did not return at the block boundary")
    return C1SaturationSummary(
        sector,
        low_suffix,
        cycle_length,
        displacement,
        carry_count_50,
        return_period,
    )


def c1_entry_return_residue(
    leading: int,
    suffix: int,
    width: int,
    summary: C1SaturationSummary,
) -> C1ReturnResidue:
    """Get the Entry C1 endpoint/carry residue using only modular powers."""
    sector = exact_integer(leading, "leading")
    low_suffix = exact_integer(suffix, "suffix")
    exponent = exact_integer(width, "width")
    if type(summary) is not C1SaturationSummary or (
        summary.leading,
        summary.suffix,
    ) != (sector, low_suffix):
        raise ValueError("C1 saturation summary has another source phase")
    if exponent < 5:
        raise ValueError("Entry width must be at least five")

    quotient_modulus = summary.return_period // gcd(
        summary.return_period, summary.cycle_length
    )
    modulus = summary.displacement * quotient_modulus
    guard = 1 + int(sector < 9)
    residue = (pow(10, exponent, modulus) - low_suffix - guard) % modulus
    quotient_mod_period, remainder = divmod(residue, summary.displacement)
    if remainder >= summary.displacement:
        raise AssertionError("Euclidean residue is outside its period")
    steps_mod_period = (
        summary.cycle_length * quotient_mod_period
    ) % summary.return_period

    suffixes, carry_prefix = c1_phase_cycle(sector, low_suffix)
    complete_cycles, tail = divmod(steps_mod_period, 50)
    target_suffix = suffixes[tail]
    carry_mod_32 = (complete_cycles * summary.carry_count_50 + carry_prefix[tail]) % 32
    return C1ReturnResidue(steps_mod_period, target_suffix, carry_mod_32)


def reconstruct_carry_first(leading: int, suffix: int, width: int) -> CarryFirstResult:
    """Compute ``Q mod 1600`` first, then derive the small boundary packet.

    The occurrence quotient is represented only by its residue. In
    particular, this routine never forms the large ``Q``, ``n`` or ``10**q``.
    """
    sector = exact_integer(leading, "leading")
    low_suffix = exact_integer(suffix, "suffix")
    exponent = exact_integer(width, "width")
    if not 1 <= sector <= 9 or not 0 <= low_suffix <= 98 or exponent < 5:
        raise ValueError("invalid fixed-sector carry-first coordinates")

    cycle_length, displacement = _cycle_displacement(sector, low_suffix)
    if displacement <= 0:
        raise AssertionError("fixed-sector cycle displacement must be positive")

    guard = 1 + int(sector < 9)
    modulus = 1600 * displacement
    euclidean_residue = (pow(10, exponent, modulus) - low_suffix - guard) % modulus
    quotient_mod_1600, remainder_from_modulus = divmod(euclidean_residue, displacement)
    remainder = (pow(10, exponent, displacement) - low_suffix - guard) % displacement
    if remainder_from_modulus != remainder:
        raise AssertionError("Euclidean quotient and remainder residues disagree")

    exponent_mod_1600 = (cycle_length * quotient_mod_1600) % 1600
    target_suffix, carry_mod_32 = _c1_target_and_carry_mod_32(
        sector, low_suffix, exponent_mod_1600
    )

    beta = (pow(10, exponent - 2, 32) - carry_mod_32) % 32
    if not 1 <= beta <= 6:
        raise AssertionError("powered C1 carry does not select the unique small beta")
    reconstructed_headroom = 100 * beta - target_suffix
    legacy_headroom = guard + remainder
    if not 1 <= reconstructed_headroom <= 540:
        raise AssertionError("reconstructed boundary packet is outside its guard")
    if reconstructed_headroom != legacy_headroom:
        raise AssertionError("carry-first packet disagrees with Euclidean headroom")

    return CarryFirstResult(
        leading=sector,
        suffix=low_suffix,
        width=exponent,
        cycle_length=cycle_length,
        displacement=displacement,
        guard=guard,
        euclidean_residue_mod_1600p=euclidean_residue,
        quotient_mod_1600=quotient_mod_1600,
        remainder=remainder,
        exponent_mod_1600=exponent_mod_1600,
        target_suffix=target_suffix,
        carry_mod_32=carry_mod_32,
        beta=beta,
        reconstructed_headroom=reconstructed_headroom,
        legacy_headroom=legacy_headroom,
    )
