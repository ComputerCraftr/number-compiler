"""Literal carry scans independent of compressed carry implementations."""

from collections.abc import Sequence


def decimal_pair_carries(pairs: Sequence[int]) -> tuple[list[int], int]:
    carry = 0
    outgoing: list[int] = []
    for pair in pairs:
        carry = int(pair + carry >= 10)
        outgoing.append(carry)
    return outgoing, carry
