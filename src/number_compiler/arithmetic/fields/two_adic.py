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


__all__ = ["v2_nonzero", "v2_positive"]
