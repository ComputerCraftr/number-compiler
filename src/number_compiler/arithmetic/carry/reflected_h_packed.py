"""Bounded broadword execution of a padded multiplier-two H action."""

from __future__ import annotations

from collections.abc import Callable

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import arithmetic_carry as keys


def _split_double(word: int, mask: int) -> tuple[int, int]:
    """Return the decimal residuals and carries in separate nibble lanes."""
    bit_zero = word & mask
    bit_one = (word >> 1) & mask
    bit_two = (word >> 2) & mask
    carry = ((word >> 3) & mask) | (bit_two & (bit_zero | bit_one))
    return (word << 1) - 10 * carry, carry


def packed_h2_step(word: int, mask: int) -> int:
    """Apply the two zero-padded carry sheets to LSD-first decimal lanes."""
    residual, carry = _split_double(word, mask)
    product = residual + (carry << 4)
    residual, carry = _split_double(product, mask)
    return carry + (residual << 4)


def publish_packed_h2(
    source: tuple[int, ...],
    steps: int,
    even: bool,
    *,
    ledger: ResourceLedger,
    scratch_owner: int,
    emit: Callable[[list[int], bool], int],
) -> int:
    """Execute an admitted padded source and emit its exact physical result."""
    width = 2 * len(source) + 2 * steps + 4
    limbs = (4 * width + 63) // 64
    charge = 20 * limbs + 2 * width
    with ledger.reservation(scratch_owner, entries=charge, nodes=charge):
        word = mask = residual = carry = 0
        cells: list[int] = []
        rows = operand_bits = 0
        try:
            word = int.from_bytes(
                bytes(((cell // 10) << 4) | (cell % 10) for cell in source),
                "little",
            )
            mask = ((1 << (4 * width)) - 1) // 15
            for _ in range(steps):
                operand_bits += 32 * (4 * width + 8)
                word = packed_h2_step(word, mask)
                rows += 1
            if word:
                word >>= 4 * (((word & -word).bit_length() - 1) // 4)
            residual, carry = _split_double(word, mask)
            word = residual + (carry << 4)
            if even:
                word = int(format(word, "x")[::-1], 16)
                residual, carry = _split_double(word, mask)
                word = residual + (carry << 4)
            cells = [
                10 * (cell >> 4) + (cell & 15)
                for cell in word.to_bytes(
                    max(1, (word.bit_length() + 7) // 8), "little"
                )
            ]
            return emit(cells, False)
        finally:
            ledger.bump(keys.REFLECTED_H_PACKED_ROW_EVALUATIONS, rows)
            ledger.bump(keys.REFLECTED_H_PACKED_ROW_OPERAND_BITS, operand_bits)
            word = mask = residual = carry = 0
            cells.clear()
