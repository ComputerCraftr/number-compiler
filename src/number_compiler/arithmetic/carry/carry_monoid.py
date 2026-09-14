"""Three-element carry-transfer monoid used by temporal block composition."""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from enum import Enum


class CarryFn(Enum):
    CONST0 = "0"
    ID = "id"
    CONST1 = "1"


def _exact_integer(value: object, role: str) -> int:
    if type(value) is not int:
        raise TypeError(f"{role} requires an exact integer")
    return value


def _carry_bit(value: object, role: str = "carry bit") -> int:
    bit = _exact_integer(value, role)
    if bit not in (0, 1):
        raise ValueError(f"{role} must be zero or one")
    return bit


def apply_carry_fn(fn: CarryFn, bit: int) -> int:
    if type(fn) is not CarryFn:
        raise TypeError("carry application requires a CarryFn")
    if type(bit) is not int:
        raise TypeError("carry bit requires an exact integer")
    if bit not in (0, 1):
        raise ValueError("carry bit must be zero or one")
    if fn is CarryFn.CONST0:
        return 0
    if fn is CarryFn.CONST1:
        return 1
    if fn is CarryFn.ID:
        return bit
    raise AssertionError("unreachable CarryFn member")


def compose_carry_fn(after: CarryFn, before: CarryFn) -> CarryFn:
    """Return ``after o before``."""
    if type(after) is not CarryFn or type(before) is not CarryFn:
        raise TypeError("carry composition requires two CarryFn values")
    # A reset destroys the incoming dependency; identity preserves it.  This
    # is the complete multiplication law, so composition need not execute the
    # function on either Boolean input to rediscover its canonical member.
    return before if after is CarryFn.ID else after


def value_carry_fn(symbol: int, base: int) -> CarryFn:
    if type(symbol) is not int or type(base) is not int:
        raise TypeError("pair symbol and carry radix require an exact integer")
    if base < 2 or not 0 <= symbol <= 2 * (base - 1):
        raise ValueError((symbol, base))
    if symbol < base - 1:
        return CarryFn.CONST0
    if symbol == base - 1:
        return CarryFn.ID
    return CarryFn.CONST1


def carry_fn_from_outputs(outputs: tuple[int, ...]) -> CarryFn:
    """Project an all-port Mealy response onto its monotone Boolean exit."""
    if type(outputs) is not tuple or len(outputs) != 2:
        raise TypeError("Boolean carry projection requires two immutable outputs")
    low, high = (_carry_bit(value) for value in outputs)
    if low > high:
        raise ValueError("Boolean carry projection must be monotone")
    if low != high:
        return CarryFn.ID
    return CarryFn.CONST1 if low else CarryFn.CONST0


@dataclass(frozen=True, slots=True)
class CarryScanAutomatonResult:
    """Exact two-state automaton run over one pair-coefficient row."""

    boundaries: tuple[int, ...]
    final_effect: CarryFn
    distinct_transition_functions: int

    def __post_init__(self) -> None:
        if type(self.boundaries) is not tuple or not self.boundaries:
            raise TypeError("carry boundaries require a nonempty immutable tuple")
        for bit in self.boundaries:
            _carry_bit(bit, "carry boundary")
        if type(self.final_effect) is not CarryFn:
            raise TypeError("final carry effect requires a CarryFn")
        count = _exact_integer(
            self.distinct_transition_functions,
            "distinct carry-function count",
        )
        if not 1 <= count <= len(CarryFn):
            raise ValueError("distinct carry-function count is out of range")


def scan_carry_automaton(
    values: Sequence[int],
    *,
    base: int = 10,
    incoming: int = 0,
) -> CarryScanAutomatonResult:
    """Run the canonical carry-transfer automaton over pair coefficients.

    This is the automaton form of the ordinary carry scan, not a parallel
    representation.  Each coefficient maps to one of the same three
    ``CarryFn`` monoid elements already consumed by block composition.
    """
    if not isinstance(values, Sequence) or isinstance(values, (str, bytes, bytearray)):
        raise TypeError("carry scan values require an integer sequence")
    vals = tuple(_exact_integer(value, "pair symbol") for value in values)
    base = _exact_integer(base, "carry radix")
    incoming = _carry_bit(incoming, "incoming carry")
    if not vals or base < 2:
        raise ValueError("carry scan requires values and radix at least two")
    effect = CarryFn.ID
    carry = incoming
    boundaries = [carry]
    seen: set[CarryFn] = set()
    for value in vals:
        fn = value_carry_fn(value, base)
        seen.add(fn)
        effect = compose_carry_fn(fn, effect)
        carry = apply_carry_fn(fn, carry)
        boundaries.append(carry)
    return CarryScanAutomatonResult(tuple(boundaries), effect, len(seen))


__all__ = [
    "CarryFn",
    "CarryScanAutomatonResult",
    "apply_carry_fn",
    "carry_fn_from_outputs",
    "compose_carry_fn",
    "scan_carry_automaton",
    "value_carry_fn",
]
