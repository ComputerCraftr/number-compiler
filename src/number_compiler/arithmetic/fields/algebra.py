"""Closed powered algebra that is genuinely independent of carry history."""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass
from math import comb

from number_compiler.arithmetic.fields.radix import digits_lsd


def radix_residue(values: Iterable[int], radix: int, modulus: int) -> int:
    from number_compiler.arithmetic.automata.guard import forbid_in_powered_jump

    forbid_in_powered_jump("radix_residue_materialized")
    z, m = int(radix), int(modulus)
    if m <= 1:
        raise ValueError(modulus)
    power = 1
    out = 0
    for value in values:
        out = (out + int(value) * power) % m
        power = power * z % m
    return out


@dataclass(frozen=True, slots=True)
class BulkPower:
    """Canonical carry-free interval operator ``2^q (U^-1+U)^r``."""

    steps: int
    growths: int

    def __post_init__(self) -> None:
        if self.steps < 0 or self.growths < 0 or self.growths > self.steps:
            raise ValueError((self.steps, self.growths))

    @property
    def no_growths(self) -> int:
        return self.steps - self.growths

    def compose(self, other: BulkPower) -> BulkPower:
        return BulkPower(self.steps + other.steps, self.growths + other.growths)

    def centered_multiplier(self, beta: int, prime: int) -> int:
        p = int(prime)
        b = int(beta) % p
        if p <= 1 or b == 0:
            raise ValueError((beta, prime))
        lam = (b + pow(b, -1, p)) % p
        return pow(2, self.no_growths, p) * pow(lam, self.growths, p) % p

    def lucas_factors(self, prime: int) -> tuple[tuple[int, int], ...]:
        p = int(prime)
        return tuple(
            (2 * p**j, d) for j, d in enumerate(digits_lsd(self.growths, p)) if d
        )

    def kernel_mod_prime(self, prime: int) -> dict[int, int]:
        p = int(prime)
        r = self.growths
        scalar = pow(2, self.no_growths, p)
        return {
            -r + 2 * m: scalar * comb(r, m) % p for m in range(r + 1) if comb(r, m) % p
        }

    def exact_edge_multiplier(self, base: int, modulus: int) -> int:
        b, m = int(base), int(modulus)
        if b < 2 or m <= 1 or (b * b - 1) % m:
            raise ValueError("modulus must divide base**2-1")
        return pow(2, self.no_growths, m) * pow(1 + b, self.growths, m) % m

    def description_bits(self) -> int:
        return max(1, self.steps.bit_length()) + max(1, self.growths.bit_length())


__all__ = ["BulkPower", "radix_residue"]
