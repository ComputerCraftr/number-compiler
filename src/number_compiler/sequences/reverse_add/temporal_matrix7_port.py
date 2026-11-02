"""Exact 21-class affine action on supplied reverse/add carry ports.

The action consumes the aligned-difference residue and width-growth bit from
one authenticated physical step. Its finite power is valid for repeated
supplied port words only; it does not predict the next source port.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass

from number_compiler.arithmetic.fields.morphism_core import binary_power


@dataclass(frozen=True, slots=True)
class Mod7CarryPortAction:
    """Canonical affine map on the next source residue modulo seven."""

    multiplier: int
    correction: int

    def __post_init__(self) -> None:
        if type(self.multiplier) is not int or self.multiplier not in (1, 2, 4):
            raise ValueError("mod-7 multiplier must be one of 1, 2, or 4")
        if type(self.correction) is not int or not 0 <= self.correction < 7:
            raise ValueError("mod-7 correction must be in 0..6")

    @classmethod
    def identity(cls) -> Mod7CarryPortAction:
        return cls(1, 0)

    @classmethod
    def from_port(cls, *, difference_mod7: int, growth: int) -> Mod7CarryPortAction:
        if type(difference_mod7) is not int or not 0 <= difference_mod7 < 7:
            raise ValueError("aligned difference must be a canonical mod-7 residue")
        if type(growth) is not int or growth not in (0, 1):
            raise ValueError("growth must be a Boolean bit")
        radix_factor = 3 if growth else 1
        return cls(
            (1 + radix_factor) % 7,
            (growth - radix_factor * difference_mod7) % 7,
        )

    def apply(self, source_residue: int) -> int:
        if type(source_residue) is not int or not 0 <= source_residue < 7:
            raise ValueError("input must be a canonical mod-7 residue")
        return (self.multiplier * source_residue + self.correction) % 7

    def then(self, later: Mod7CarryPortAction) -> Mod7CarryPortAction:
        """Compose in chronological order: this action, then later."""
        if type(later) is not Mod7CarryPortAction:
            raise TypeError("mod-7 action composition requires the same action type")
        return Mod7CarryPortAction(
            (later.multiplier * self.multiplier) % 7,
            (later.multiplier * self.correction + later.correction) % 7,
        )

    def power(self, copies: int) -> Mod7CarryPortAction:
        """Power a repeated supplied action in logarithmic algebraic work."""
        if type(copies) is not int or copies < 0:
            raise ValueError("power must be a nonnegative exact integer")
        return binary_power(
            self,
            copies,
            identity=self.identity(),
            compose=lambda first, second: first.then(second),
        ).value


def _reversed_carry_runs(
    width: int, switches: Sequence[int]
) -> tuple[tuple[int, int], ...]:
    if type(width) is not int or width < 1:
        raise ValueError("carry width must be positive")
    forward: list[tuple[int, int]] = []
    start = 1
    carry = 0
    previous = 0
    for point in switches:
        if type(point) is not int or not previous < point <= width:
            raise ValueError("carry switches must be strictly ordered within width")
        if point > start:
            forward.append((carry, point - start))
        carry ^= 1
        start = point
        previous = point
    if start <= width:
        forward.append((carry, width + 1 - start))
    reversed_runs: list[tuple[int, int]] = []
    for symbol, length in reversed(forward):
        if reversed_runs and reversed_runs[-1][0] == symbol:
            previous_symbol, previous_length = reversed_runs[-1]
            reversed_runs[-1] = previous_symbol, previous_length + length
        else:
            reversed_runs.append((symbol, length))
    return tuple(reversed_runs)


def aligned_difference_mod7_from_switches(width: int, switches: Sequence[int]) -> int:
    """Compute D mod 7 from the complete carry-switch port in RLE time.

    If K is the carry correction, D = 99*floor(K/10) + 10*g.
    The least significant digit of K is omitted in floor(K/10). Carry
    digits are represented by run boundaries, so the work is linear in switch
    count and logarithmic in run lengths.
    """
    runs = _reversed_carry_runs(width, switches)
    growth = len(switches) & 1
    residue = 3 * growth % 7
    offset = 0
    for digit, count in runs:
        first = max(offset, 1)
        remaining = offset + count - first
        if digit and remaining:
            geometric = (pow(3, remaining, 7) - 1) * 4 % 7
            residue = (residue + pow(3, first - 1, 7) * geometric) % 7
        offset += count
    return residue


def action_from_carry_switches(
    width: int, switches: Sequence[int]
) -> Mod7CarryPortAction:
    """Build the exact action for one supplied physical carry-port letter."""
    growth = len(switches) & 1
    return Mod7CarryPortAction.from_port(
        difference_mod7=aligned_difference_mod7_from_switches(width, switches),
        growth=growth,
    )


__all__ = [
    "Mod7CarryPortAction",
    "action_from_carry_switches",
    "aligned_difference_mod7_from_switches",
]
