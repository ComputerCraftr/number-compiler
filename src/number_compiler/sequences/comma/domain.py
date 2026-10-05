"""Canonical domains for decimal comma boundary states.

The finite round arithmetic intentionally admits the coarse range ``x <= 98``
for every leading sector.  Published Entry charts have a smaller sector
specific domain: ``x <= 89 + f``.  Keep these predicates in one owner so a
constructor/cache guard cannot silently confuse the two contracts. These are
coordinate envelopes, not certificates of source reachability or authority.
"""

from __future__ import annotations


def coarse_entry_coordinate(leading: int, coordinate: int) -> bool:
    """Return whether ``(leading, coordinate)`` is in the round domain.

    This is the legacy arithmetic admission rule.  It is deliberately wider
    than the canonical Entry publication domain and must not be used as a
    semantic chart/cache key validator.
    """

    return (
        type(leading) is int
        and type(coordinate) is int
        and 1 <= leading <= 9
        and 0 <= coordinate <= 98
    )


def canonical_entry_limit(leading: int) -> int:
    """Return the largest coordinate of a canonical Entry in sector ``leading``."""

    if type(leading) is not int or not 1 <= leading <= 9:
        raise ValueError("comma Entry leading sector must be 1 through 9")
    return 89 + leading


def canonical_entry_coordinate(leading: int, coordinate: int) -> bool:
    """Test the necessary coordinate envelope for a canonical sector Entry.

    The boundary is sector dependent: sector 1 ends at 90, sector 2 at 91,
    and sector 9 at 98.  Invalid types and negative coordinates fail closed.
    """

    return (
        type(leading) is int
        and type(coordinate) is int
        and 1 <= leading <= 9
        and 0 <= coordinate <= 89 + leading
    )


def decade_root_coordinate(leading: int, coordinate: int) -> bool:
    """Return whether a canonical decade root has sector 1 and ``x <= 90``."""

    return leading == 1 and canonical_entry_coordinate(leading, coordinate)


def canonical_offset_orbit(coordinate: int) -> int:
    """Return the canonical 46-fiber orbit of a decade-root coordinate."""
    if type(coordinate) is not int or not 0 <= coordinate <= 90:
        raise ValueError("comma offset orbit requires a canonical root coordinate")
    digit = coordinate % 10
    return (coordinate - (5 * digit * digit - 4 * digit)) % 460 // 10


__all__ = [
    "canonical_entry_coordinate",
    "canonical_entry_limit",
    "canonical_offset_orbit",
    "coarse_entry_coordinate",
    "decade_root_coordinate",
]
