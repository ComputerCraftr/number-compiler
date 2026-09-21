"""Executable obstruction for a generic reverse/add carry-region constructor.

The primitive cylinder identity gives an exact coefficient expression
``P' = M*P + beta``.  A temporal D2 constructor additionally needs the spatial
carry transfer of ``P'``.  Existing source ports retain the carry transfer of
``P``; they do not retain a value-region partition from which a threshold of a
new affine expression can be pulled back.

This distinction already matters for a width-one decimal source.  With digit
``x`` and no growth, ``P_0=2x``, ``Q=0``, ``beta=0``, and ``P'_0=2P_0=4x``.
Digits 2 and 3 have the same original carry action (constant zero), but the
next pair coefficients 8 and 12 have different carry actions.  Consequently
there is no function

``original CarryFn -> successor CarryFn``

even after fixing base, extent, growth, radial shape and zero innovation.
Source identity distinguishes the occurrences, but using identity as an
evaluator would be an opaque future-coefficient callback rather than a
parameter-region rule.

The first missing constructive operation is therefore ``threshold_pullback``:
for a source-bound symbolic coefficient expression ``E`` it must construct a
canonical spatial predicate region whose interval summary satisfies

``T_E([a,c)) = T_E([b,c)) then T_E([a,b))``

and whose leaf is ``value_carry_fn(E(i), base)``.  Construction must use only
source regions, charts and expression DAG nodes; it may not enumerate every
``i``.  No current production owner provides this operation or a complexity
bound for radial/innovation sums.  This module records that precise boundary;
it is not a candidate scheduler or a callback-backed region implementation.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    value_carry_fn,
)


@dataclass(frozen=True, slots=True)
class WidthOneCarryCollision:
    """Two scalar source chambers aliased by the available carry summary."""

    base: int
    first_digit: int
    second_digit: int
    original_action: CarryFn
    first_successor_action: CarryFn
    second_successor_action: CarryFn

    @property
    def first_pair(self) -> int:
        return 2 * self.first_digit

    @property
    def second_pair(self) -> int:
        return 2 * self.second_digit

    @property
    def first_successor_pair(self) -> int:
        return 2 * self.first_pair

    @property
    def second_successor_pair(self) -> int:
        return 2 * self.second_pair

    def validate(self) -> None:
        if (
            type(self.base) is not int
            or type(self.first_digit) is not int
            or type(self.second_digit) is not int
            or type(self.original_action) is not CarryFn
            or type(self.first_successor_action) is not CarryFn
            or type(self.second_successor_action) is not CarryFn
        ):
            raise TypeError("carry-region witness requires exact finite values")
        if not 2 <= self.base or not (
            0 <= self.first_digit < self.second_digit < self.base
        ):
            raise ValueError("carry-region witness leaves its source alphabet")
        if self.first_pair >= self.base or self.second_pair >= self.base:
            raise ValueError("witness must stay in the no-growth primitive chamber")
        if (
            value_carry_fn(self.first_pair, self.base) is not self.original_action
            or value_carry_fn(self.second_pair, self.base) is not self.original_action
        ):
            raise ValueError("witness sources do not share their original carry action")
        if (
            value_carry_fn(self.first_successor_pair, self.base)
            is not self.first_successor_action
            or value_carry_fn(self.second_successor_pair, self.base)
            is not self.second_successor_action
            or self.first_successor_action is self.second_successor_action
        ):
            raise ValueError("witness does not separate successor carry actions")


@dataclass(frozen=True, slots=True)
class ThresholdPullbackObligation:
    """The exact law a nonenumerative source-region owner must discharge."""

    leaf_law: str
    interval_law: str
    construction_bound: str
    unavailable_input: str


@dataclass(frozen=True, slots=True)
class NonpalindromicD2Collision:
    """Two admitted D2 sources with equal first carry classes and unequal next ones."""

    first_source: tuple[int, ...]
    second_source: tuple[int, ...]
    original_actions: tuple[CarryFn, ...]
    first_output: tuple[int, ...]
    second_output: tuple[int, ...]
    first_successor_actions: tuple[CarryFn, ...]
    second_successor_actions: tuple[CarryFn, ...]


def first_width_one_collision(base: int = 10) -> WidthOneCarryCollision:
    """Find the first finite-alphabet proof that carry summaries do not factor.

    This scans the fixed radix alphabet, never a source word or spatial index.
    Only no-growth width-one sources are considered, so both primitive clauses
    have ``Q=beta=0`` and homogeneous multiplier 2.
    """
    if type(base) is not int:
        raise TypeError("radix must be an exact integer")
    if base < 2:
        raise ValueError("radix must be at least two")
    chambers: dict[CarryFn, tuple[int, CarryFn]] = {}
    for digit in range(1, base):
        pair = 2 * digit
        if pair >= base:
            continue
        original = value_carry_fn(pair, base)
        successor = value_carry_fn(2 * pair, base)
        previous = chambers.get(original)
        if previous is not None and previous[1] is not successor:
            result = WidthOneCarryCollision(
                base,
                previous[0],
                digit,
                original,
                previous[1],
                successor,
            )
            result.validate()
            return result
        chambers.setdefault(original, (digit, successor))
    raise ValueError("this radix has no width-one carry-region collision")


def _step(
    source: tuple[int, ...], base: int
) -> tuple[tuple[int, ...], tuple[int, ...]]:
    pairs = tuple(source[index] + source[-1 - index] for index in range(len(source)))
    carry = 0
    output: list[int] = []
    for pair in pairs:
        total = pair + carry
        carry, digit = divmod(total, base)
        output.append(digit)
    if carry:
        output.append(carry)
    return pairs, tuple(output)


def decimal_nonpalindromic_d2_collision() -> NonpalindromicD2Collision:
    """Return a direct D2 witness with neither source nor first output palindromic."""
    first_source = (0, 5, 3)
    second_source = (0, 5, 4)
    first_pairs, first_output = _step(first_source, 10)
    second_pairs, second_output = _step(second_source, 10)
    first_next_pairs, _ = _step(first_output, 10)
    second_next_pairs, _ = _step(second_output, 10)
    result = NonpalindromicD2Collision(
        first_source,
        second_source,
        tuple(value_carry_fn(value, 10) for value in first_pairs),
        first_output,
        second_output,
        tuple(value_carry_fn(value, 10) for value in first_next_pairs),
        tuple(value_carry_fn(value, 10) for value in second_next_pairs),
    )
    if (
        first_source == first_source[::-1]
        or second_source == second_source[::-1]
        or first_output == first_output[::-1]
        or second_output == second_output[::-1]
        or tuple(value_carry_fn(value, 10) for value in second_pairs)
        != result.original_actions
        or result.first_successor_actions == result.second_successor_actions
    ):
        raise AssertionError("invalid nonpalindromic D2 carry-region witness")
    return result


def missing_threshold_pullback() -> ThresholdPullbackObligation:
    """Return the first exact obligation not implemented by current owners."""
    return ThresholdPullbackObligation(
        leaf_law="leaf(E,i) = value_carry_fn(coefficient(E,i), base)",
        interval_law=("transfer(E,[a,c)) = transfer(E,[b,c)) then transfer(E,[a,b))"),
        construction_bound=(
            "region nodes and construction work bounded by symbolic clause size "
            "and log(width), without one branch per coefficient"
        ),
        unavailable_input=(
            "authenticated source value regions supporting threshold pullback "
            "through radial, chart, signed-sum and carry-atom DAG nodes"
        ),
    )


__all__ = [
    "NonpalindromicD2Collision",
    "ThresholdPullbackObligation",
    "WidthOneCarryCollision",
    "decimal_nonpalindromic_d2_collision",
    "first_width_one_collision",
    "missing_threshold_pullback",
]
