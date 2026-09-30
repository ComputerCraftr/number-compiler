"""Bounded factor multiplicity labels for independent research audits."""

from __future__ import annotations

from number_compiler.sequences.prime.set import smallest_factor


def factor_multiplicities_truth(value: int) -> tuple[tuple[int, int], ...]:
    remaining = int(value)
    if remaining < 2:
        return ()
    factors: list[tuple[int, int]] = []
    while remaining > 1:
        factor = smallest_factor(remaining)
        prime = remaining if factor is None else factor
        multiplicity = 0
        while remaining % prime == 0:
            remaining //= prime
            multiplicity += 1
        factors.append((prime, multiplicity))
    return tuple(factors)
