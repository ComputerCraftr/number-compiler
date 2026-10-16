"""Finite three-ingress carry actions for radix multiplication by three.

Chronological composition is LSD to MSD; set powers describe unknown digits,
not a selected source word or a temporal recurrence certificate.
"""

from __future__ import annotations

from number_compiler.arithmetic.fields.morphism_core import binary_power

CarryFn = tuple[int, int, int]
IDENTITY: CarryFn = (0, 1, 2)


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

    Powers the *relation* in O(log width), never reads the middle or assumes
    a repeated block. In particular its set size is bounded by 3**3.
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
    return binary_power(
        frozenset(digit_transfer(base, d) for d in range(base)),
        width,
        identity=frozenset((IDENTITY,)),
        compose=compose_sets,
    ).value
