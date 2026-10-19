"""Structural identity for an exact ordered Mahler odd-return motif."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final

from number_compiler.arithmetic.contracts.family_identity import FamilyId
from number_compiler.hashlife.interfaces.border_macros import (
    BorderMacroIdentity,
    BorderMacroKind,
    BorderWireValue,
)
from number_compiler.sequences.antihydra.mahler_source_actions import (
    MAX_MAHLER_SOURCE_EXTENT,
)

_MAHLER_ODD_RUN_MOTIF_WIRE_TAG: Final[str] = "mahler-odd-run-motif-v1"


@dataclass(frozen=True, slots=True)
class MahlerOddMotifSignature:
    """Source-independent ordered exponent word; it grants no repeat authority."""

    exponents: tuple[int, ...]

    def __post_init__(self) -> None:
        if (
            type(self.exponents) is not tuple
            or not 1 <= len(self.exponents) <= 8
            or any(
                type(exponent) is not int or exponent < 1 for exponent in self.exponents
            )
        ):
            raise ValueError("a Mahler motif must contain 1..8 positive exponents")
        if sum(self.exponents) > MAX_MAHLER_SOURCE_EXTENT:
            raise ValueError("Mahler motif exceeds the source-width bound")

    @property
    def family(self) -> FamilyId:
        return FamilyId.ANTIHYDRA

    def wire_value(self) -> BorderWireValue:
        return _MAHLER_ODD_RUN_MOTIF_WIRE_TAG, self.exponents

    @property
    def identity(self) -> BorderMacroIdentity:
        """Return the structural path identity, separate from source admission."""
        return BorderMacroIdentity(
            self.family,
            BorderMacroKind.PATH,
            self,
        )


def checked_mahler_odd_motif(
    identity: BorderMacroIdentity,
) -> MahlerOddMotifSignature:
    """Validate and recover the exact family-owned motif from shared metadata."""
    if type(identity) is not BorderMacroIdentity:
        raise TypeError("a Mahler ring requires a shared border macro identity")
    if (
        identity.family is not FamilyId.ANTIHYDRA
        or identity.kind is not BorderMacroKind.PATH
    ):
        raise ValueError("border identity is not an Antihydra odd-return path")
    signature = identity.checked_signature()
    if type(signature) is not MahlerOddMotifSignature:
        raise TypeError("border identity does not contain a Mahler motif signature")
    return signature


__all__ = ("MahlerOddMotifSignature", "checked_mahler_odd_motif")
