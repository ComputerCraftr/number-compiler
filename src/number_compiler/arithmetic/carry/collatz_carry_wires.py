"""Exact two-wire factorization of reachable multiply-by-three carries."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    apply_carry_fn,
    compose_carry_fn,
)


def _encode(carry: int) -> tuple[int, int]:
    if type(carry) is not int:
        raise TypeError("Collatz carry requires an exact integer")
    if carry not in (0, 1, 2):
        raise ValueError("Collatz carry must be zero, one, or two")
    return (int(carry >= 1), int(carry == 2))


def _decode(lower: int, upper: int) -> int:
    if (lower, upper) not in ((0, 0), (1, 0), (1, 1)):
        raise ValueError("two-wire carry escaped its staircase domain")
    return lower + upper


def _threshold_action(value: int, threshold: int) -> CarryFn:
    if value < threshold:
        return CarryFn.CONST0
    if value == threshold:
        return CarryFn.ID
    return CarryFn.CONST1


@dataclass(frozen=True, slots=True)
class CollatzCarryWires:
    """One exact action on ``c in {0,1,2}`` factored into Boolean wires.

    ``lower`` acts on ``[c >= 1]`` and ``upper`` acts on ``[c == 2]``.
    The six admitted pairs are closed under composition. Five arise from
    nonempty digit intervals; ``(ID, ID)`` is the empty-interval identity.
    """

    lower: CarryFn
    upper: CarryFn

    def __post_init__(self) -> None:
        if type(self.lower) is not CarryFn or type(self.upper) is not CarryFn:
            raise TypeError("Collatz carry wires require two CarryFn values")
        for carry in (0, 1, 2):
            lower, upper = _encode(carry)
            _decode(
                apply_carry_fn(self.lower, lower),
                apply_carry_fn(self.upper, upper),
            )

    @classmethod
    def identity(cls) -> CollatzCarryWires:
        return cls(CarryFn.ID, CarryFn.ID)

    def apply(self, carry: int) -> int:
        lower, upper = _encode(carry)
        return _decode(
            apply_carry_fn(self.lower, lower),
            apply_carry_fn(self.upper, upper),
        )

    def after(self, before: CollatzCarryWires) -> CollatzCarryWires:
        """Return ``self o before`` in the closed product carry algebra."""
        if type(before) is not CollatzCarryWires:
            raise TypeError("Collatz carry composition requires two wire actions")
        before.__post_init__()
        return CollatzCarryWires(
            compose_carry_fn(self.lower, before.lower),
            compose_carry_fn(self.upper, before.upper),
        )

    @property
    def outputs(self) -> tuple[int, int, int]:
        return (self.apply(0), self.apply(1), self.apply(2))


def collatz_digit_carry_wires(digit: int, *, base: int = 10) -> CollatzCarryWires:
    """Return the exact two-wire law for ``floor((3*digit+c)/base)``.

    The independent Boolean thresholds exist when ``base == 1 (mod 3)``.
    Other radices retain the ordinary three-state finite carry function.
    """
    if type(digit) is not int or type(base) is not int:
        raise TypeError("Collatz digit carry requires exact integers")
    if base < 4 or base % 3 != 1:
        raise ValueError("two-wire Collatz carry requires radix 1 modulo 3")
    if not 0 <= digit < base:
        raise ValueError("Collatz digit lies outside its radix")
    redundant = 3 * digit
    return CollatzCarryWires(
        _threshold_action(redundant, base - 1),
        _threshold_action(redundant, 2 * (base - 1)),
    )


def collatz_digit_carry_action(digit: int, *, base: int) -> tuple[int, int, int]:
    """Exact action ``c -> floor((3*digit+c)/base)`` for any radix.

    Unlike the two-wire factorization, this ternary action also covers dyadic
    radices congruent to two modulo three and the one-symbol radix used at a
    directional seam.
    """
    if type(digit) is not int or type(base) is not int:
        raise TypeError("Collatz carry action requires exact integers")
    if base < 1 or not 0 <= digit < base:
        raise ValueError("Collatz carry action digit is outside its radix")
    return (
        (3 * digit) // base,
        (3 * digit + 1) // base,
        (3 * digit + 2) // base,
    )


def collatz_dyadic_carry_partition(
    bits: int,
) -> tuple[tuple[tuple[int, int, int], ...], tuple[int, ...]]:
    """Canonical action rows and class map for the radix ``2**bits``."""
    if type(bits) is not int:
        raise TypeError("dyadic carry width requires an exact integer")
    if not 0 <= bits <= 16:
        raise ValueError("dyadic carry width exceeds the bounded local alphabet")
    base = 1 << bits
    rows = tuple(collatz_digit_carry_action(value, base=base) for value in range(base))
    actions = tuple(dict.fromkeys(rows))
    return actions, tuple(actions.index(row) for row in rows)


def compose_collatz_carry_actions(
    after: tuple[int, int, int], before: tuple[int, int, int]
) -> tuple[int, int, int]:
    """Return ``after o before`` on the three-valued carry boundary."""
    for action in (after, before):
        if type(action) is not tuple or len(action) != 3:
            raise TypeError("Collatz carry action must be an immutable ternary row")
        if any(type(value) is not int or not 0 <= value < 3 for value in action):
            raise ValueError("Collatz carry action leaves its boundary alphabet")
    return after[before[0]], after[before[1]], after[before[2]]


__all__ = [
    "CollatzCarryWires",
    "collatz_digit_carry_action",
    "collatz_digit_carry_wires",
    "collatz_dyadic_carry_partition",
    "compose_collatz_carry_actions",
]
