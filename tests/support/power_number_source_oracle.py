"""Literal source references independent of the bounded modular ports."""

from __future__ import annotations

from typing import NamedTuple


class LiteralRadixPort(NamedTuple):
    source_prefix: int
    target_prefix: int
    carry: tuple[int, ...]
    borrow: tuple[int, ...]
    xor: tuple[int, ...]


def literal_power_number_source(family: str, level: int) -> int:
    """Build only small test sources by their defining integer recurrence."""
    if type(level) is not int or level < 0:
        raise ValueError(level)
    if family == "fermat":
        return int(3 ** (1 << level))
    if family == "mersenne":
        value = 4
        for _ in range(level):
            value = value * value - 2
        return value
    raise ValueError(family)


def literal_power_number_radix_port(
    family: str, level: int, base: int
) -> LiteralRadixPort:
    """Use a literal source and digit-column multiplication as a reference."""
    if type(base) is not int or not 2 <= base <= 10:
        raise ValueError(base)
    source = literal_power_number_source(family, level)
    offset = 2 if family == "mersenne" else 0
    target = source * source - offset
    modulus = base**6
    source_digits = tuple((source // base**index) % base for index in range(6))

    # Accumulate ordered digit products into full columns, then carry through
    # those columns. This is independent of the production source-residue and
    # coefficient-prefix calculation.
    columns = [0] * 6
    for left_index, left_digit in enumerate(source_digits):
        for right_index, right_digit in enumerate(source_digits):
            column = left_index + right_index
            if column < len(columns):
                columns[column] += left_digit * right_digit
    columns[0] -= offset
    carry = 0
    all_carries: list[int] = []
    for column_value in columns:
        carry, _ = divmod(column_value + carry, base)
        all_carries.append(carry)

    boundaries = (1, 2, 3, 5, 6)
    selected = tuple(all_carries[boundary - 1] for boundary in boundaries)
    borrows = tuple(
        int(target % (base**boundary) < source % (base**boundary))
        for boundary in boundaries
    )
    return LiteralRadixPort(
        source % modulus,
        target % modulus,
        selected,
        borrows,
        tuple(
            (value & 1) ^ borrow
            for value, borrow in zip(selected, borrows, strict=True)
        ),
    )


def literal_power_number_sparse_digits(
    family: str, level: int, base: int, positions: tuple[int, ...]
) -> tuple[int, ...]:
    source = literal_power_number_source(family, level)
    target = source * source - (2 if family == "mersenne" else 0)
    return tuple(int(target // (base**position) % base) for position in positions)
