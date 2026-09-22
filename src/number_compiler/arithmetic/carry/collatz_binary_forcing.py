"""Canonical binary carry forcing and its bounded radix-64 F5 observer.

The phase is a projection of carry forcing, not a successor identity. This
owner is shared by production consumers and the harmonic research tools.
"""

from number_compiler.arithmetic.carry.carry_normalization import (
    linear_normalization_fields,
)
from number_compiler.arithmetic.carry.collatz_carry_wires import (
    collatz_digit_carry_wires,
)
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.arithmetic.polynomials.primary_jet import primary_jet_from_digits

Jet = tuple[int, ...]


def binary_carry_birth(value: int, modulus: int = 32, incoming: int = 1) -> Jet:
    """Independent carry forcing for 3*value+incoming, from redundant bits."""
    if type(incoming) is not int or incoming not in (0, 1, 2):
        raise ValueError("Collatz incoming carry must be 0,1,2")
    if type(value) is not int or value < 0:
        raise ValueError("binary forcing source must be nonnegative and exact")
    bits = digits_lsd(value, 2) + (0, 0)
    raw = tuple(bit + (bits[i - 1] if i else 0) for i, bit in enumerate(bits))
    _digits, carries = linear_normalization_fields(raw, base=2, boundary_in=incoming)
    assert carries[-1] == 0
    forcing = tuple(carries[i] - 2 * carries[i + 1] for i in range(len(raw)))
    return primary_jet_from_digits(forcing, degree=5, modulus=modulus).jet


def radix64_phi5(digit: int) -> int:
    """y_bit^2 coefficient of the digit's binary forcing birth at carry one."""
    collatz_digit_carry_wires(digit, base=64)  # Validate the radix-64 digit.
    return binary_carry_birth(digit, modulus=5, incoming=1)[2]
