"""Finite three-ingress carry actions for radix multiplication by three.

Chronological composition is LSD to MSD; set powers describe unknown digits,
not a selected source word or a temporal recurrence certificate.
"""

from __future__ import annotations

CarryFn = tuple[int, int, int]
IDENTITY: CarryFn = (0, 1, 2)
_MAX_RELATION_ORBIT = 32


def digit_transfer(base: int, digit: int) -> CarryFn:
    if type(base) is not int or base not in (2, 10):
        raise ValueError("only the exact binary/decimal joint owner is admitted")
    if type(digit) is not int or not 0 <= digit < base:
        raise ValueError("invalid radix digit")
    return (3 * digit // base, (3 * digit + 1) // base, (3 * digit + 2) // base)


def compose_transfer(first: CarryFn, after: CarryFn) -> CarryFn:
    """Apply the lower block, then the higher block, LSD first."""
    return after[first[0]], after[first[1]], after[first[2]]


def compose_sets(
    left: frozenset[CarryFn], right: frozenset[CarryFn]
) -> frozenset[CarryFn]:
    return frozenset(compose_transfer(a, b) for a in left for b in right)


def unknown_middle_transfer_set(base: int, width: int) -> frozenset[CarryFn]:
    """Exactly all carry functions realizable by ANY width-digit middle.

    Detects the finite relation's exact orbit, never reads the middle or
    assumes a repeated source block. Each relation contains at most 3**3
    carry functions. The orbit limit is a work budget, not a closure claim.
    """
    if (
        type(base) is not int
        or base not in (2, 10)
        or type(width) is not int
        or width < 0
    ):
        raise ValueError("invalid unknown middle width")
    if width.bit_length() > 65_536:
        raise ValueError("carry relation exponent exceeds coordinate budget")
    atoms = frozenset(digit_transfer(base, d) for d in range(base))
    current = frozenset((IDENTITY,))
    seen: dict[frozenset[CarryFn], int] = {}
    orbit: list[frozenset[CarryFn]] = []
    for exponent in range(_MAX_RELATION_ORBIT):
        if exponent == width:
            return current
        if current in seen:
            first = seen[current]
            return orbit[first + (width - first) % (exponent - first)]
        seen[current] = exponent
        orbit.append(current)
        current = compose_sets(current, atoms)
    raise ValueError("carry relation orbit exceeds work budget")
