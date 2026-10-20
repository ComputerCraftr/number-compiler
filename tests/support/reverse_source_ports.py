"""Small literal reference operations for reverse/add source-port tests."""

from __future__ import annotations

from number_compiler.arithmetic.contracts.scoped_handles import ExactSource


def source_digits(value: int, radix: int) -> tuple[int, ...]:
    result: list[int] = []
    while True:
        result.append(value % radix)
        value //= radix
        if not value:
            return tuple(result)


def source_from_value(value: int, radix: int) -> ExactSource:
    return ExactSource(source_digits(value, radix), radix, orbit="reverse-add")


def pair_sums(digits: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(digits[index] + digits[-1 - index] for index in range(len(digits)))


def carry_scan(pairs: tuple[int, ...], radix: int) -> tuple[int, ...]:
    carry = 0
    result = [0]
    for pair in pairs:
        carry = int(pair + carry >= radix)
        result.append(carry)
    return tuple(result)


def successor_digits(digits: tuple[int, ...], radix: int) -> tuple[int, ...]:
    pairs = pair_sums(digits)
    carries = carry_scan(pairs, radix)
    result = tuple((pair + carries[index]) % radix for index, pair in enumerate(pairs))
    return result + ((1,) if carries[-1] else ())
