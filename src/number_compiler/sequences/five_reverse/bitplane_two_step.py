"""Exact Boolean four-plane dense five-reversal executor.

This is a chronological broadword kernel, not a temporal skip. Work and
intermediate bit limits match the existing nibble executor. The plane
representation is lossless; normalization uses the authenticated first
sheet's cut, and publication alone decodes decimal digits.
"""

from __future__ import annotations

from collections.abc import Callable

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded

from .packed_two_step import (
    ExactBitBudget,
    PackedFiveWork,
    decimal_to_packed,
    packed_to_decimal,
    validate_packed_five_input,
)

Planes = tuple[int, int, int, int]
_TRANSLATE = tuple(
    bytes(48 + ((v - 48) >> bit & 1) if 48 <= v <= 57 else 48 for v in range(256))
    for bit in range(4)
)


def encode_planes(text: bytes) -> Planes:
    return (
        int(text.translate(_TRANSLATE[0]), 2),
        int(text.translate(_TRANSLATE[1]), 2),
        int(text.translate(_TRANSLATE[2]), 2),
        int(text.translate(_TRANSLATE[3]), 2),
    )


def add5(p: int, a: int, b: int, c: int) -> Planes:
    u = p & a
    v = u & b
    return p ^ a, b ^ u, p ^ c ^ v, p & (c | v)


def _decode(planes: Planes, *, reverse: bool = False) -> int:
    p, a, b, c = planes
    width = max(1, p.bit_length(), a.bit_length(), b.bit_length(), c.bit_length())
    rows = (format(v, f"0{width}b").encode() for v in planes)
    digits = bytes(
        48 + (x & 1) + 2 * (y & 1) + 4 * (z & 1) + 8 * (w & 1)
        for x, y, z, w in zip(*rows, strict=True)
    )
    return packed_to_decimal(int(digits[::-1] if reverse else digits, 16))


def _compare(planes: Planes, bound: Planes, *, reverse: bool) -> bool:
    """Lexicographic > on physical digit order without decoding a row."""
    p, a, b, c = planes
    bp, ba, bb, bc = bound
    unequal = (p ^ bp) | (a ^ ba) | (b ^ bb) | (c ^ bc)
    if not unequal:
        return False
    bit = (unequal & -unequal) if reverse else 1 << (unequal.bit_length() - 1)
    for x, y in ((c, bc), (b, bb), (a, ba), (p, bp)):
        if (x ^ y) & bit:
            return bool(x & bit)
    raise AssertionError("unreachable comparison")


class _PlaneBudget:
    def __init__(self, bits: int) -> None:
        self.width = ExactBitBudget(bits)
        self.forward: Planes | None = None
        self.backward: Planes | None = None

    def check(self, planes: Planes, width: int, *, reverse: bool = False) -> None:
        if not self.width.check_width(width):
            return
        limit = self.width.limit()
        if width < len(limit):
            return
        if width > len(limit):
            raise BlockContextBudgetExceeded(
                "five-reversal next state exceeds its admitted bit budget"
            )
        if reverse:
            if self.backward is None:
                self.backward = encode_planes(limit[::-1].encode())
            bound = self.backward
        else:
            if self.forward is None:
                self.forward = encode_planes(limit.encode())
            bound = self.forward
        if _compare(planes, bound, reverse=reverse):
            raise BlockContextBudgetExceeded(
                "five-reversal next state exceeds its admitted bit budget"
            )


def execute_bitplane_five(
    seed: int,
    steps: int,
    max_state_bits: int,
    work: PackedFiveWork,
    *,
    reserve_capacity: Callable[[int], None] | None = None,
) -> int:
    validate_packed_five_input(seed, steps, max_state_bits, work)
    if not steps:
        return seed
    capacity = max(8, (seed.bit_length() + 2) // 3 + 5)
    if reserve_capacity is not None:
        reserve_capacity(capacity)
    p, a, b, c = encode_planes(format(decimal_to_packed(seed), "x").encode())
    budget = _PlaneBudget(max_state_bits)
    support = p | a | b | c
    width = max(1, support.bit_length())
    complete_pairs = steps // 2
    for pair_index in range(complete_pairs + steps % 2):
        if width + 3 >= capacity:
            capacity = max(capacity * 2, width + 4)
            if reserve_capacity is not None:
                reserve_capacity(capacity)
        if support:
            low = support & -support
            first_width = width - (low.bit_length() - 1) + bool((a | b | c) & low)
        else:
            first_width = 1
        p, a, b, c = add5(p << 1, a, b, c)
        middle = p | a | b | c
        cut = (middle & -middle).bit_length() - 1 if middle else 0
        work.attempted += 1
        if first_width > budget.width.safe_width:
            budget.check(
                (p >> cut, a >> cut, b >> cut, c >> cut), first_width, reverse=True
            )
        work.digit_reads += width
        if pair_index == complete_pairs:
            normalized = p >> cut, a >> cut, b >> cut, c >> cut
            # Physical low zeros can be absent from the padded track.
            zero_count = first_width - max(1, (middle >> cut).bit_length())
            if zero_count < 0:
                raise AssertionError("physical width is smaller than the emitted word")
            return _decode(normalized, reverse=True) * int(10**zero_count)
        work.attempted += 1
        p, a, b, c = add5(p, a << 1, b << 1, c << 1)
        if cut:
            p, a, b, c = p >> cut, a >> cut, b >> cut, c >> cut
        support = p | a | b | c
        width = max(1, support.bit_length())
        work.executed_pairs += 1
        work.bitplane_pairs += 1
        if width > budget.width.safe_width:
            budget.check((p, a, b, c), width)
        work.digit_reads += first_width
    return _decode((p, a, b, c))
