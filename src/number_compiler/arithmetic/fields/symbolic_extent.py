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

from number_compiler.arithmetic.fields.radix import bit_width


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

    def _compare_dyadic(self, other: "DyadicExtent") -> int:
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
        if self.offset:
            sign = "+" if self.offset > 0 else "-"
            return f"2**{self.power}{sign}{abs(self.offset)}"
        return f"2**{self.power}"


def _normalize_reverse_descriptor(obj: ReverseAddExtent | ReverseAddBitExtent) -> None:
    seed, base, generation = int(obj.seed), int(obj.base), int(obj.generation)
    if seed < 0 or base < 2 or generation < 0:
        raise ValueError((seed, base, generation))
    object.__setattr__(obj, "seed", seed)
    object.__setattr__(obj, "base", base)
    object.__setattr__(obj, "generation", generation)


@dataclass(frozen=True, slots=True)
class ReverseAddExtent:
    """Exact lazy radix width of one reverse/add term.

    The numeric width depends on the accumulated nonlinear growth observer, so
    forcing it during nth-term construction would reintroduce temporal
    projection work.  Keep the exact query as a compact algebraic descriptor;
    materialization is explicit and uses the binary-powered endpoint index.
    """

    seed: int
    base: int
    generation: int

    def __post_init__(self) -> None:
        _normalize_reverse_descriptor(self)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("reverse-add-extent", self.seed, self.base, self.generation)

    @property
    def description_bits(self) -> int:
        return (
            bit_width(self.seed) + bit_width(self.base) + bit_width(self.generation) + 3
        )

    @property
    def maximum(self) -> int:
        from number_compiler.arithmetic.fields.radix import digits_lsd

        return len(digits_lsd(self.seed, self.base)) + self.generation

    def materialize(self) -> int:
        from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

        return ReverseAddPoweredTerm(self.seed, self.generation, base=self.base).width()

    def contains_index(self, position: int) -> bool:
        position = int(position)
        if position < 0 or position >= self.maximum:
            return False
        return position < self.materialize()

    def __repr__(self) -> str:
        return (
            f"width(reverse_add(seed={self.seed},base={self.base})[{self.generation}])"
        )


@dataclass(frozen=True, slots=True)
class ReverseAddBitExtent:
    """Exact lazy upper bit extent implied by the exact reverse/add radix width."""

    seed: int
    base: int
    generation: int

    def __post_init__(self) -> None:
        _normalize_reverse_descriptor(self)

    @property
    def description_bits(self) -> int:
        return (
            bit_width(self.seed) + bit_width(self.base) + bit_width(self.generation) + 4
        )

    def materialize(self) -> int:
        from math import ceil, log2

        width = ReverseAddExtent(self.seed, self.base, self.generation).materialize()
        if self.base == 2:
            return width
        return max(1, ceil(width * log2(self.base)))

    def _compare_int(self, other: int) -> int:
        value = self.materialize()
        other = int(other)
        return (value > other) - (value < other)

    def __eq__(self, other: object) -> bool:
        if isinstance(other, ReverseAddBitExtent):
            return (self.seed, self.base, self.generation) == (
                other.seed,
                other.base,
                other.generation,
            )
        if isinstance(other, int):
            return self._compare_int(other) == 0
        return False

    def __lt__(self, other: object) -> bool:
        if isinstance(other, int):
            return self._compare_int(other) < 0
        return NotImplemented

    def __le__(self, other: object) -> bool:
        if isinstance(other, int):
            return self._compare_int(other) <= 0
        return NotImplemented

    def __gt__(self, other: object) -> bool:
        if isinstance(other, int):
            return self._compare_int(other) > 0
        return NotImplemented

    def __ge__(self, other: object) -> bool:
        if isinstance(other, int):
            return self._compare_int(other) >= 0
        return NotImplemented

    def __repr__(self) -> str:
        return f"bit_extent(reverse_add(seed={self.seed},base={self.base})[{self.generation}])"


Extent = int | DyadicExtent | ReverseAddExtent | ReverseAddBitExtent


def extent_json_value(value: Extent) -> int | dict[str, object]:
    """Return a JSON-safe exact extent without forcing dyadic materialization."""
    if isinstance(value, DyadicExtent):
        return {
            "kind": "dyadic-extent",
            "power": value.power,
            "offset": value.offset,
            "expression": repr(value),
        }
    if isinstance(value, ReverseAddExtent):
        return {
            "kind": "reverse-add-extent",
            "seed": value.seed,
            "base": value.base,
            "generation": value.generation,
            "expression": repr(value),
        }
    if isinstance(value, ReverseAddBitExtent):
        return {
            "kind": "reverse-add-bit-extent",
            "seed": value.seed,
            "base": value.base,
            "generation": value.generation,
            "expression": repr(value),
        }
    return int(value)


def extent_description_bits(value: Extent) -> int:
    if isinstance(value, (DyadicExtent, ReverseAddExtent, ReverseAddBitExtent)):
        return value.description_bits
    return bit_width(int(value))


__all__ = [
    "DyadicExtent",
    "ReverseAddExtent",
    "ReverseAddBitExtent",
    "Extent",
    "extent_json_value",
    "extent_description_bits",
]
