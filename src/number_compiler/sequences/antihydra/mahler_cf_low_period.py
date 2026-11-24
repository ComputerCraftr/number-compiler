"""Finite low-column responses of the physical decimal powers of five.

The operator is source independent. Its caller authenticates the physical
row, exponent and significant width before applying the suffix response.
"""

from __future__ import annotations

from collections.abc import Callable

from number_compiler.arithmetic.fields.ordered_matrix import Matrix2


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
    period = 1 if columns <= 2 else 1 << (columns - 2)
    phase = (exponent - columns) % period
    binary_residue = int.__pow__(5, phase, 1 << columns)
    value = 5**columns * binary_residue
    place = 10 ** (columns - 1)
    result = Matrix2.identity()
    while place:
        digit, value = divmod(value, place)
        result = result.multiply(Matrix2.digit(digit + 1))
        place //= 10
    return result
