"""Finite spatial carry summaries shared by source-backed Collatz observers."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.resources.proof_payload_admission import (
    register_proof_geometry_fields,
)

__all__ = ["CarryRangeSummary", "CarryRangeTransfer"]


@dataclass(frozen=True, slots=True)
class CarryRangeSummary:
    length: int
    exit_carry: int
    first_one: int | None
    last_one: int | None

    def __post_init__(self) -> None:
        if (
            type(self.length) is not int
            or self.length < 0
            or type(self.exit_carry) is not int
            or not 0 <= self.exit_carry <= 2
        ):
            raise ValueError("invalid finite carry summary")
        if any(
            point is not None
            and (type(point) is not int or not 0 <= point < self.length)
            for point in (self.first_one, self.last_one)
        ):
            raise ValueError("carry witnesses must be coordinates within the range")
        if (self.first_one is None) != (self.last_one is None):
            raise ValueError("carry witness endpoints must agree on emptiness")
        if (
            self.first_one is not None
            and self.last_one is not None
            and self.first_one > self.last_one
        ):
            raise ValueError("carry witnesses must be ordered")

    @property
    def all_zero(self) -> bool:
        return self.first_one is None

    def then(self, following: CarryRangeSummary) -> CarryRangeSummary:
        """Combine adjacent ranges already evaluated with matched carry ports."""
        return CarryRangeSummary(
            self.length + following.length,
            following.exit_carry,
            self.first_one
            if self.first_one is not None
            else (
                None
                if following.first_one is None
                else self.length + following.first_one
            ),
            self.last_one
            if following.last_one is None
            else self.length + following.last_one,
        )


@dataclass(frozen=True, slots=True)
class CarryRangeTransfer:
    """Complete three-state carry transfer with geometric output witnesses."""

    rows: tuple[CarryRangeSummary, ...]

    def __post_init__(self) -> None:
        if (
            type(self.rows) is not tuple
            or len(self.rows) != 3
            or any(type(row) is not CarryRangeSummary for row in self.rows)
        ):
            raise ValueError("a mul3 transfer has exactly three carry rows")
        if any(row.length != self.rows[0].length for row in self.rows):
            raise ValueError("all carry rows must cover the same range")

    @property
    def length(self) -> int:
        return self.rows[0].length

    @classmethod
    def bit(cls, bit: int) -> CarryRangeTransfer:
        if type(bit) is not int or bit not in (0, 1):
            raise ValueError(bit)
        return cls(
            tuple(
                CarryRangeSummary(
                    1,
                    (3 * bit + carry) >> 1,
                    0 if (3 * bit + carry) & 1 else None,
                    0 if (3 * bit + carry) & 1 else None,
                )
                for carry in range(3)
            )
        )

    def compose(self, following: CarryRangeTransfer) -> CarryRangeTransfer:
        return CarryRangeTransfer(
            tuple(row.then(following.rows[row.exit_carry]) for row in self.rows)
        )

    def repeat(self, count: int) -> CarryRangeTransfer:
        if type(count) is not int or count < 0:
            raise ValueError(count)
        result = CarryRangeTransfer(
            tuple(CarryRangeSummary(0, carry, None, None) for carry in range(3))
        )
        factor = self
        while count:
            if count & 1:
                result = result.compose(factor)
            count >>= 1
            if count:
                factor = factor.compose(factor)
        return result


register_proof_geometry_fields(
    {
        CarryRangeSummary: frozenset(("length", "first_one", "last_one")),
        CarryRangeTransfer: frozenset(),
    }
)
