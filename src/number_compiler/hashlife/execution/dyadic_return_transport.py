"""Exact source-value and low-residue transport helpers."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.dyadic_return_images import (
        DyadicReturnImageWorkspace,
        _SourceNode,
    )


def _low_bits(value: int, width: int) -> int:
    """Return a low-bit slice without allocating a redundant wide mask."""
    if width == 0 or value == 0:
        return 0
    if value.bit_length() <= width:
        return value
    return value & ((1 << width) - 1)


def source_value(workspace: DyadicReturnImageWorkspace, source: _SourceNode) -> int:
    if source.lift == 0:
        return source.residue
    return source.residue + (1 << source.precision) * source.lift


def transport_low(
    workspace: DyadicReturnImageWorkspace,
    transfer: SkewTransfer[int],
    source_residue: int,
    after_width: int,
) -> int:
    """Transport only the demanded low residue through a skew."""
    if transfer.upper == 0:
        if transfer.offset % transfer.lower:
            raise ArithmeticError("dyadic return residue transport was not integral")
        value = transfer.offset // transfer.lower
        workspace._bump(
            "transport_operand_bits",
            max(
                1,
                source_residue.bit_length(),
                transfer.offset.bit_length(),
                transfer.lower.bit_length(),
                value.bit_length(),
            ),
        )
        return _low_bits(value, after_width)
    denominator_bits = transfer.lower.bit_length() - 1
    modulus_bits = denominator_bits + after_width
    if modulus_bits == 0:
        return 0
    modulus = 1 << modulus_bits
    reduced_source = _low_bits(source_residue, modulus_bits)
    reduced_upper = _low_bits(transfer.upper, modulus_bits)
    reduced_offset = transfer.offset % modulus
    residue_numerator = (reduced_upper * reduced_source + reduced_offset) % modulus
    if residue_numerator % transfer.lower:
        raise ArithmeticError("dyadic return residue transport was not integral")
    workspace._bump(
        "transport_operand_bits",
        max(
            1,
            modulus_bits,
            source_residue.bit_length(),
            transfer.upper.bit_length(),
            transfer.offset.bit_length(),
            transfer.lower.bit_length(),
        ),
    )
    return (residue_numerator // transfer.lower) & ((1 << after_width) - 1)
