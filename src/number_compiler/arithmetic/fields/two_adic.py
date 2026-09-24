"""Shared exact 2-adic valuation helpers.

Production and research modules previously carried several byte-for-byte copies
of the same positive/nonzero valuation primitive.  Keep one implementation so
2-adic normalization semantics cannot silently drift between Collatz,
cyclotomic, and special-number research paths.
"""

from __future__ import annotations


def v2_positive(value: int) -> int:
    """Return ``v_2(value)`` for a strictly positive integer."""
    value = int(value)
    if value <= 0:
        raise ValueError(value)
    return (value & -value).bit_length() - 1


def v2_nonzero(value: int) -> int:
    """Return ``v_2(value)`` for any nonzero signed integer."""
    value = abs(int(value))
    if value == 0:
        raise ValueError(value)
    return (value & -value).bit_length() - 1


def inverse_dyadic_parity_word(
    word: int,
    width: int,
    *,
    gains: tuple[int, int],
    offsets: tuple[int, int],
) -> int:
    """Invert a finite parity word for ``x -> (g_b*x+c_b)/2`` modulo ``2**w``.

    The selected branch bit is ``b=x mod 2``. Both gains must be odd units;
    the offsets make the selected numerator even. For bits ``b_0,...,b_j``
    the contribution from ``c_(b_j)`` to the source is

        -2**j * c_(b_j) * product(g_(b_i)**-1 for i=0..j).

    This only inverts a supplied finite itinerary. It does not establish that
    an arbitrary physical-time cursor or source occurrence was admitted.
    """
    if type(word) is not int or type(width) is not int or width < 0:
        raise ValueError("finite parity inverse requires natural word and width")
    if word < 0 or word.bit_length() > width:
        raise ValueError("parity word exceeds its width")
    if (
        type(gains) is not tuple
        or type(offsets) is not tuple
        or len(gains) != 2
        or len(offsets) != 2
        or any(type(value) is not int for value in (*gains, *offsets))
    ):
        raise TypeError("dyadic parity inverse requires two exact branch laws")
    if any(gain <= 0 or gain % 2 == 0 for gain in gains):
        raise ValueError("dyadic parity gains must be positive odd units")
    if offsets[0] % 2 or (gains[1] + offsets[1]) % 2:
        raise ValueError("dyadic parity branch numerators must be even")
    if width == 0:
        return 0
    modulus = 1 << width
    inverse_even = 1 if gains[0] == 1 else pow(gains[0], -1, modulus)
    inverse_odd = (
        inverse_even
        if gains[1] == gains[0]
        else 1
        if gains[1] == 1
        else pow(gains[1], -1, modulus)
    )
    inverse_gains = (inverse_even, inverse_odd)
    unit = 1
    residue = 0
    # Repeatedly shifting the whole supplied word copies a shrinking big
    # integer at each position. Decode bounded bytes once instead.
    packed = word.to_bytes((width + 7) // 8, "little")
    for position in range(width):
        bit = (packed[position // 8] >> (position % 8)) & 1
        if inverse_gains[bit] != 1:
            unit = (unit * inverse_gains[bit]) % modulus
        if offsets[bit]:
            residue = (residue - ((offsets[bit] * unit) << position)) % modulus
    return residue


__all__ = ["inverse_dyadic_parity_word", "v2_nonzero", "v2_positive"]
