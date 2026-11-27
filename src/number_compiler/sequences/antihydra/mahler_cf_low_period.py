"""Finite low-column responses of the physical decimal powers of five.

The operator is source independent. Its caller authenticates the physical
row, exponent and significant width before applying the suffix response.
"""

from __future__ import annotations

from collections.abc import Callable

from number_compiler.arithmetic.fields.ordered_matrix import (
    Matrix2,
    MatrixEntries,
    append_decimal_value,
)

# Each phase adds its most significant digit to an already shared suffix.
# For four columns, the settled cycle in exponent order starts at 0625.
_FINAL_5 = Matrix2.digit(6)
_FINAL_2 = Matrix2.digit(3)
SETTLED_TENS_ACTION = _FINAL_2.entries
_FINAL_25 = _FINAL_2.multiply(_FINAL_5)
_FINAL_125 = Matrix2.digit(2).multiply(_FINAL_25)


def _half_turn(matrix: MatrixEntries) -> MatrixEntries:
    a, b, c, d = matrix
    return a + 5 * c, b + 5 * d, c, d


_FINAL_625 = Matrix2(_half_turn(_FINAL_125.entries))
_FINAL_0625 = Matrix2.digit(1).multiply(_FINAL_625).entries
_FINAL_3125 = Matrix2.digit(4).multiply(_FINAL_125).entries
_SETTLED_ACTIONS = (
    (_FINAL_5.entries,),
    (_FINAL_25.entries,),
    (_FINAL_125.entries, _FINAL_625.entries),
    (
        _FINAL_0625,
        _FINAL_3125,
        _half_turn(_FINAL_0625),
        _half_turn(_FINAL_3125),
    ),
)


def settled_low_action(exponent: int, columns: int) -> MatrixEntries:
    """Select the immutable ordered action at a settled one-to-four digit cut."""
    if type(columns) is not int or type(exponent) is not int:
        raise TypeError("settled suffix needs integral width and exponent")
    if not 1 <= columns <= len(_SETTLED_ACTIONS) or exponent < columns:
        raise ValueError("unsettled low-column phase")
    actions = _SETTLED_ACTIONS[columns - 1]
    return actions[(exponent - columns) % len(actions)]


def low_suffix_response(
    exponent: int, columns: int, *, reserve_bits: Callable[[int], None]
) -> Matrix2:
    """Return the MSD-first CF action of a settled physical low suffix.

    For exponent n >= columns c, 5**n is divisible by 5**c. Its low
    decimal suffix is 5**c times 5**(n-c) reduced modulo 2**c.
    The latter has period 1 for c <= 2, otherwise 2**(c-2). The caller
    must bind this source-free response to its live physical row.
    """
    if type(exponent) is not int or type(columns) is not int:
        raise TypeError("low-column exponent and width must be integers")
    if not 1 <= columns <= 16 or exponent < columns:
        raise ValueError("low-column response needs a settled 1..16 digit suffix")
    if not callable(reserve_bits):
        raise TypeError("low-column response requires a scratch owner")
    reserve_bits(32 * (columns + exponent.bit_length() + 128))
    if columns <= len(_SETTLED_ACTIONS):
        return Matrix2(settled_low_action(exponent, columns))
    period = 1 << (columns - 2)
    phase = (exponent - columns) % period
    binary_residue = int.__pow__(5, phase, 1 << columns)
    value = 5**columns * binary_residue
    return Matrix2(append_decimal_value(value, 10 ** (columns - 1), (1, 0, 0, 1)))
