"""Independent literal models for complete semantic interface tests."""

from __future__ import annotations

from collections.abc import Sequence

from number_compiler.arithmetic.contracts.block_effect import BlockEffect, BoundarySide
from number_compiler.arithmetic.fields.ordered_matrix import Matrix2
from number_compiler.hashlife.interfaces.semantic_structures import (
    COMPONENT_ROLES,
)


def literal_digit_matrix(digits_msd_first: str, modulus: int) -> Matrix2:
    """MSD-first continuants without the production matrix composition path."""
    a, b, c, d = 1, 0, 0, 1
    for char in digits_msd_first:
        coefficient = int(char) + 1
        a, b, c, d = (
            (a * coefficient + b) % modulus,
            a,
            (c * coefficient + d) % modulus,
            c,
        )
    return Matrix2((a, b, c, d), modulus)


def literal_band_trace(
    states: tuple[int, ...], width: int, modulus: int
) -> tuple[Matrix2, Matrix2, tuple[tuple[Matrix2, Matrix2], ...], int]:
    """Exact decimal windows and chronological products of supplied states."""
    lower_product = Matrix2.identity(modulus)
    upper_product = Matrix2.identity(modulus)
    trace: list[tuple[Matrix2, Matrix2]] = []
    reads = 0
    for value in states:
        digits = str(value)
        lower = literal_digit_matrix(digits[-width:].zfill(width), modulus)
        upper = literal_digit_matrix(digits[:width].ljust(width, "0"), modulus)
        lower_product = lower_product.then(lower)
        upper_product = upper_product.then(upper)
        trace.append((lower, upper))
        reads += 2 * min(width, len(digits))
    return lower_product, upper_product, tuple(trace), reads


def scan_ports(
    effect: BlockEffect, word: Sequence[int], left: object, right: object
) -> tuple[list[object], list[object], list[int]]:
    """Literal two-sided scans independent of compiled transfer construction."""
    ls, rs = [left], [right]
    for symbol in word:
        ls.append(effect.advance(BoundarySide.LEFT, ls[-1], symbol))
    for symbol in reversed(word):
        rs.append(effect.advance(BoundarySide.RIGHT, rs[-1], symbol))
    rs.reverse()
    return (
        ls,
        rs,
        [effect.emit(ls[i], symbol, rs[i + 1]) for i, symbol in enumerate(word)],
    )


def macro_oracle(
    effect: BlockEffect,
    word: tuple[int, ...],
    left: int,
    right: int,
    coordinate: int,
) -> dict[str, object]:
    ls, rs, output = scan_ports(effect, word, left, right)
    active = [i for i, symbol in enumerate(output) if symbol != effect.blank]
    source = [i for i, symbol in enumerate(word) if symbol != effect.blank]
    width = len(word)
    extent = active[-1] + 1 if active else 0
    return dict(
        zip(
            COMPONENT_ROLES,
            (
                ls[-1],
                rs[0],
                output[coordinate],
                int(bool(active)),
                active[0] if active else width,
                active[-1] if active else width,
                extent,
                output[0],
                output[-1],
                width + extent - (source[-1] + 1 if source else 0),
                int(not active),
                output[coordinate],
                coordinate,
            ),
            strict=True,
        )
    )
