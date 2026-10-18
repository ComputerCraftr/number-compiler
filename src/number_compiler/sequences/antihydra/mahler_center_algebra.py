"""Conditional Mahler decimal-center algebra and its Moore quotient."""

from __future__ import annotations

STATES = 100


def center_next(center: int, lower_carry: int, upper_parity: int) -> int:
    """Exact Mahler decimal pair under a supplied external carry letter."""
    if type(center) is not int or not 0 <= center < STATES:
        raise ValueError("a two-decimal-digit center is required")
    if type(lower_carry) is not int or not 0 <= lower_carry <= 2:
        raise ValueError("Mahler lower tripling carry must be 0, 1 or 2")
    if type(upper_parity) is not int or upper_parity not in (0, 1):
        raise ValueError("upper division inlet source parity must be Boolean")
    high_carry, remainder = divmod(3 * center + lower_carry, 100)
    return remainder // 2 + 50 * ((upper_parity + high_carry) & 1)


def conditional_center_moore(
    letters: tuple[tuple[int, int], ...] = (
        (0, 0),
        (0, 1),
        (1, 0),
        (1, 1),
        (2, 0),
        (2, 1),
    ),
    *,
    output: str = "gt-eq-lt",
) -> tuple[tuple[int, ...], ...]:
    """Coarsest future-output partition for a declared input alphabet.

    Each inlet is a conditional external letter. The quotient does not claim
    that the alphabet is indefinitely source-realizable.
    """
    if (
        type(letters) is not tuple
        or not letters
        or any(type(letter) is not tuple or len(letter) != 2 for letter in letters)
    ):
        raise ValueError("Moore refinement requires a finite typed inlet alphabet")
    if output not in ("gt-eq-lt", "literal"):
        raise ValueError("unknown Mahler center output contract")
    for carry, parity in letters:
        center_next(0, carry, parity)
    emissions = tuple(
        ((center // 10 > center % 10) - (center // 10 < center % 10))
        if output == "gt-eq-lt"
        else center
        for center in range(STATES)
    )

    def colors(keys: tuple[object, ...]) -> tuple[int, ...]:
        interner: dict[object, int] = {}
        return tuple(interner.setdefault(key, len(interner)) for key in keys)

    current = colors(emissions)
    while True:
        refined = colors(
            tuple(
                (
                    emissions[center],
                    tuple(current[center_next(center, *letter)] for letter in letters),
                )
                for center in range(STATES)
            )
        )
        if refined == current:
            break
        current = refined
    groups: dict[int, list[int]] = {}
    for center, color in enumerate(current):
        groups.setdefault(color, []).append(center)
    return tuple(tuple(states) for states in groups.values())


__all__ = ["STATES", "center_next", "conditional_center_moore"]
