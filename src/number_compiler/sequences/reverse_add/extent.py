"""Lazy exact width descriptors owned by the reverse/add family."""

from __future__ import annotations

from dataclasses import dataclass
from math import ceil, log2

from number_compiler.arithmetic.fields.radix import bit_width, digits_lsd
from number_compiler.arithmetic.fields.symbolic_extent import (
    CoordinatePresentation,
    integer_text,
)


def _normalize(obj: ReverseAddExtent | ReverseAddBitExtent) -> None:
    seed, base, generation = int(obj.seed), int(obj.base), int(obj.generation)
    if seed < 0 or base < 2 or generation < 0:
        raise ValueError((seed, base, generation))
    object.__setattr__(obj, "seed", seed)
    object.__setattr__(obj, "base", base)
    object.__setattr__(obj, "generation", generation)


def _coordinate(generation: int, value: CoordinatePresentation | None) -> str:
    if value is not None and generation == value[0]:
        return value[1]
    return integer_text(generation)


@dataclass(frozen=True, slots=True)
class ReverseAddExtent:
    """Exact lazy radix width of one reverse/add term."""

    seed: int
    base: int
    generation: int

    def __post_init__(self) -> None:
        _normalize(self)

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
        return len(digits_lsd(self.seed, self.base)) + self.generation

    def materialize(self) -> int:
        from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

        return ReverseAddPoweredTerm(self.seed, self.generation, base=self.base).width()

    def contains_index(self, position: int) -> bool:
        position = int(position)
        return 0 <= position < self.maximum and position < self.materialize()

    def __lt__(self, other: object) -> bool:
        if isinstance(other, int):
            return self.materialize() < other
        return NotImplemented

    def __le__(self, other: object) -> bool:
        if isinstance(other, int):
            return self.materialize() <= other
        return NotImplemented

    def __gt__(self, other: object) -> bool:
        if isinstance(other, int):
            return self.materialize() > other
        return NotImplemented

    def __ge__(self, other: object) -> bool:
        if isinstance(other, int):
            return self.materialize() >= other
        return NotImplemented

    def to_json_value(
        self, coordinate: CoordinatePresentation | None = None
    ) -> dict[str, object]:
        generation = (
            coordinate[2]
            if coordinate is not None and self.generation == coordinate[0]
            else self.generation
        )
        return {
            "kind": "reverse-add-extent",
            "seed": self.seed,
            "base": self.base,
            "generation": generation,
            "expression": f"width(reverse_add(seed={integer_text(self.seed)},base={integer_text(self.base)})[{_coordinate(self.generation, coordinate)}])",
        }

    def __repr__(self) -> str:
        return str(self.to_json_value()["expression"])


@dataclass(frozen=True, slots=True)
class ReverseAddBitExtent:
    """Exact lazy upper bit extent implied by the radix width."""

    seed: int
    base: int
    generation: int

    def __post_init__(self) -> None:
        _normalize(self)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("reverse-add-bit-extent", self.seed, self.base, self.generation)

    @property
    def description_bits(self) -> int:
        return (
            bit_width(self.seed) + bit_width(self.base) + bit_width(self.generation) + 4
        )

    def materialize(self) -> int:
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

    def to_json_value(
        self, coordinate: CoordinatePresentation | None = None
    ) -> dict[str, object]:
        generation = (
            coordinate[2]
            if coordinate is not None and self.generation == coordinate[0]
            else self.generation
        )
        return {
            "kind": "reverse-add-bit-extent",
            "seed": self.seed,
            "base": self.base,
            "generation": generation,
            "expression": f"bit_extent(reverse_add(seed={integer_text(self.seed)},base={integer_text(self.base)})[{_coordinate(self.generation, coordinate)}])",
        }

    def __repr__(self) -> str:
        return str(self.to_json_value()["expression"])


__all__ = ["ReverseAddBitExtent", "ReverseAddExtent"]
