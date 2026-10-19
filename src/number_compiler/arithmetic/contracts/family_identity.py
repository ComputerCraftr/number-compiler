"""Canonical family identifiers shared by API and execution contracts."""

from __future__ import annotations

from enum import StrEnum


class FamilyId(StrEnum):
    """Stable family identity; serialized values are CLI and packet spellings."""

    REVERSE_ADD = "reverse-add"
    DOUBLE_REVERSE = "2rev10"
    COLLATZ = "collatz"
    ANTIHYDRA = "antihydra"
    A367620 = "a367620"
    PRIME = "prime"
    FERMAT = "fermat"
    MERSENNE = "mersenne"


def family_id(value: str | FamilyId) -> FamilyId:
    """Parse a family spelling at a CLI or other external-input boundary."""
    if type(value) is FamilyId:
        return value
    if type(value) is not str:
        raise ValueError(f"unknown family: {value}")
    try:
        return FamilyId(value)
    except ValueError as error:
        raise ValueError(f"unknown family: {value}") from error


__all__ = ["FamilyId", "family_id"]
