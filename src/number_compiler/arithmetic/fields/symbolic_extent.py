"""Compact exact extents whose represented integer may be exponentially large.

The source compiler frequently needs to retain *where* a sparse special-number
boundary lies without constructing that boundary as a Python integer.  A Fermat
word is the canonical example: its high one is at ``2**n``.  Storing the
integer ``2**n`` costs Theta(n) bits even though the sequence parameter ``n``
itself costs only Theta(log n) bits.

``DyadicExtent`` keeps the exact value ``2**power + offset`` as algebraic
metadata.  Equality and ordering against ordinary integers are decided from
bit lengths and power-of-two tests; they do not construct ``1 << power``.
Materialization is an explicit bounded operation.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Protocol, runtime_checkable

from number_compiler.arithmetic.contracts.input_validation import is_runtime_instance
from number_compiler.arithmetic.fields.radix import bit_width


def integer_text(value: int) -> str:
    """Render admitted integers without unbounded decimal conversion."""
    import sys

    limit = min(sys.get_int_max_str_digits() or 4096, 4096)
    return str(value) if value.bit_length() <= 3 * limit else hex(value)


@dataclass(frozen=True, slots=True)
class DyadicExtent:
    """Exact symbolic integer ``2**power + offset``.

    ``offset`` is deliberately restricted to -1, 0, or +1.  Those are the
    exact boundary forms needed by sparse Fermat extents and keep comparison
    semantics canonical without smuggling another large integer into the
    descriptor.
    """

    power: int
    offset: int = 0

    def __post_init__(self) -> None:
        p, c = int(self.power), int(self.offset)
        if p < 0 or c not in (-1, 0, 1):
            raise ValueError((p, c))
        if p == 0 and c == -1:
            raise ValueError((p, c))
        # Canonicalize the only tiny overlaps between 2**p +/- 1 forms so
        # semantic equality and the dataclass hash remain consistent.
        if p <= 2:
            value = (1 << p) + c
            if value == 1:
                p, c = 0, 0
            elif value == 2:
                p, c = 1, 0
            elif value == 3:
                p, c = 1, 1
        object.__setattr__(self, "power", p)
        object.__setattr__(self, "offset", c)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("dyadic-extent", self.power, self.offset)

    @property
    def description_bits(self) -> int:
        return bit_width(self.power) + bit_width(abs(self.offset)) + 1

    def _compare_int(self, other: int) -> int:
        """Compare this extent with ``other`` without constructing ``2**power``."""
        other = int(other)
        shifted = other - self.offset
        if shifted <= 0:
            return 1
        top = shifted.bit_length() - 1
        if self.power < top:
            return -1
        if self.power > top:
            return 1
        # Same top bit.  2**p equals shifted only when shifted is a power of two.
        if shifted & (shifted - 1):
            return -1
        return 0

    def _compare_dyadic(self, other: DyadicExtent) -> int:
        """Compare two algebraic dyadic extents without large materialization.

        Adjacent tiny powers need care because the +/-1 offsets can cross or
        coincide (for example ``2**1+1 == 2**2-1``).  Once the smaller power
        is at least two, even the extremal offsets cannot bridge one power-of-2
        step, so dominant-power comparison is exact.
        """
        if self.power == other.power:
            return (self.offset > other.offset) - (self.offset < other.offset)
        low, high = (self, other) if self.power < other.power else (other, self)
        if high.power - low.power >= 2 or low.power >= 2:
            result = -1
        else:
            # Only powers 0/1/2 can reach this path, so this is bounded and
            # cannot reintroduce a source-size asymptote.
            a = (1 << low.power) + low.offset
            b = (1 << high.power) + high.offset
            result = (a > b) - (a < b)
        return result if self is low else -result

    def __eq__(self, other: object) -> bool:
        if isinstance(other, DyadicExtent):
            return self._compare_dyadic(other) == 0
        if isinstance(other, int):
            return self._compare_int(other) == 0
        return False

    def __lt__(self, other: object) -> bool:
        if isinstance(other, DyadicExtent):
            return self._compare_dyadic(other) < 0
        if isinstance(other, int):
            return self._compare_int(other) < 0
        return NotImplemented

    def __le__(self, other: object) -> bool:
        if isinstance(other, (DyadicExtent, int)):
            return self == other or self < other
        return NotImplemented

    def __gt__(self, other: object) -> bool:
        if isinstance(other, (DyadicExtent, int)):
            return not self <= other
        return NotImplemented

    def __ge__(self, other: object) -> bool:
        if isinstance(other, (DyadicExtent, int)):
            return not self < other
        return NotImplemented

    def contains_index(self, position: int) -> bool:
        position = int(position)
        return position >= 0 and self._compare_int(position) > 0

    def materialize(self, *, max_power: int = 1_000_000) -> int:
        """Explicitly lower the algebraic extent to a Python integer.

        The power cap makes accidental asymptotic regressions visible.  Callers
        that intentionally need a larger concrete boundary must opt in by
        raising the cap.
        """
        cap = int(max_power)
        if cap < 0 or self.power > cap:
            raise ValueError((self.power, cap))
        return (1 << self.power) + self.offset

    def __repr__(self) -> str:
        return extent_expression(self)


CoordinatePresentation = tuple[int, str, dict[str, int | str]]


@runtime_checkable
class SymbolicExtent(Protocol):
    """Family-owned exact extent exposed through the shared geometry boundary."""

    @property
    def description_bits(self) -> int: ...

    def to_json_value(
        self, coordinate: CoordinatePresentation | None = None
    ) -> dict[str, object]: ...

    def __le__(self, other: int) -> bool: ...

    def __gt__(self, other: int) -> bool: ...


Extent = int | DyadicExtent | SymbolicExtent


def extent_expression(
    value: DyadicExtent | SymbolicExtent,
    coordinate: CoordinatePresentation | None = None,
) -> str:
    """Render exact descriptor coordinates only on explicit presentation demand."""
    if not isinstance(value, DyadicExtent):
        return repr(value)
    parameter = value.power
    text = (
        coordinate[1]
        if coordinate is not None and parameter == coordinate[0]
        else integer_text(parameter)
    )
    if is_runtime_instance(value, DyadicExtent):
        suffix = (
            ("+" if value.offset > 0 else "-") + integer_text(abs(value.offset))
            if value.offset
            else ""
        )
        return f"2**{text}{suffix}"
    raise AssertionError("unreachable extent expression")


def extent_json_value(
    value: Extent,
    *,
    coordinate: CoordinatePresentation | None = None,
) -> int | dict[str, object]:
    """Return a JSON-safe exact extent without forcing dyadic materialization."""
    if isinstance(value, DyadicExtent):
        return {
            "kind": "dyadic-extent",
            "power": coordinate[2]
            if coordinate is not None and value.power == coordinate[0]
            else value.power,
            "offset": value.offset,
            "expression": extent_expression(value, coordinate),
        }
    if not isinstance(value, int):
        return value.to_json_value(coordinate)
    if coordinate is not None and value == coordinate[0]:
        return dict(coordinate[2])
    return int(value)


def extent_description_bits(value: Extent) -> int:
    if isinstance(value, (DyadicExtent, SymbolicExtent)):
        return value.description_bits
    return bit_width(int(value))


__all__ = [
    "DyadicExtent",
    "Extent",
    "SymbolicExtent",
    "extent_description_bits",
    "extent_json_value",
]
