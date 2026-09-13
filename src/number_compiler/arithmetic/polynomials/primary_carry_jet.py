"""Exact first primary carry jet; support decoding remains unproved.

The fixed module is (Z/16)[z]/(z+1)^2. Its seam observation is an output,
never a temporal successor identity or an admitted primality certificate.
"""

from __future__ import annotations

from dataclasses import dataclass
from collections.abc import Sequence

from number_compiler.arithmetic.polynomials.primary_jet import PrimaryJetBlock
from number_compiler.arithmetic.polynomials.cyclotomic_carry import (
    CarryCyclotomicTransducer,
)


@dataclass(frozen=True, slots=True)
class PrimaryCarryJet:
    value: int
    derivative: int

    def __post_init__(self) -> None:
        if type(self.value) is not int or type(self.derivative) is not int:
            raise TypeError("primary jet coordinates require exact integers")
        object.__setattr__(self, "value", self.value % 16)
        object.__setattr__(self, "derivative", self.derivative % 16)

    @property
    def harmonic_mod2(self) -> tuple[int, int]:
        return ((self.value + self.derivative) % 2, self.derivative % 2)

    @property
    def marker_parities(self) -> tuple[int, int]:
        """Carry sum and one-based first moment, modulo two."""
        return (self.value % 2, (self.value + self.derivative) % 2)

    def normalization_defect(
        self, *, length: int, incoming: int, outgoing: int
    ) -> PrimaryCarryJet:
        """A-R = (2-z)Q - c_in + c_out*z^L, in the y=z+1 basis."""
        if type(length) is not int or length < 0:
            raise ValueError("length must be nonnegative")
        sign = (-1) ** length
        return PrimaryCarryJet(
            3 * self.value - incoming + outgoing * sign,
            3 * self.derivative - self.value - outgoing * length * sign,
        )

    @classmethod
    def from_normalization_defect(
        cls, defect: PrimaryCarryJet, *, length: int, incoming: int, outgoing: int
    ) -> PrimaryCarryJet:
        if type(length) is not int or length < 0:
            raise ValueError("length must be nonnegative")
        sign = (-1) ** length
        # (3-y)^-1 = 11 + 9*y modulo (16,y^2).
        a = defect.value + incoming - outgoing * sign
        b = defect.derivative + outgoing * length * sign
        return cls(11 * a, 11 * b + 9 * a)


@dataclass(frozen=True, slots=True)
class EtalePrimaryCarryJetKey:
    deck_branch: int
    seam_carry: int
    jet: PrimaryCarryJet

    def __post_init__(self) -> None:
        if type(self.deck_branch) is not int or self.deck_branch not in (0, 1):
            raise ValueError("deck branch must be a bit")
        if type(self.seam_carry) is not int or type(self.jet) is not PrimaryCarryJet:
            raise TypeError("invalid primary seam observation")


@dataclass(frozen=True, slots=True)
class PrimaryEtaleCarryJetTransducer:
    """Whole incoming-carry response with the existing composition owner."""

    transducer: CarryCyclotomicTransducer

    def __post_init__(self) -> None:
        t = self.transducer
        if (t.action.base, t.order, t.modulus, t.power, t.factor) != (
            2,
            2,
            16,
            2,
            None,
        ):
            raise ValueError("primary carry module must be binary (16,(z+1)^2)")

    @classmethod
    def from_coefficients(
        cls, coefficients: Sequence[int], *, incoming_min: int, incoming_max: int
    ) -> PrimaryEtaleCarryJetTransducer:
        return cls(
            CarryCyclotomicTransducer.from_coefficients(
                coefficients,
                base=2,
                incoming_min=incoming_min,
                incoming_max=incoming_max,
                order=2,
                modulus=16,
                power=2,
            )
        )

    def response(self, incoming: int) -> tuple[int, PrimaryCarryJet]:
        emission = self.transducer.emission(incoming)
        a, b = emission.residue  # z-basis to y=z+1 basis
        return self.transducer.action.apply(incoming), PrimaryCarryJet(a - b, b)

    def seam_key(
        self,
        *,
        deck_branch: int,
        seam_carry: int,
        boundary_sign: int = 1,
        exceptional_minus_one: bool = False,
    ) -> EtalePrimaryCarryJetKey:
        if type(boundary_sign) is not int or boundary_sign not in (-1, 1):
            raise ValueError("boundary sign must be cyclic +1 or negacyclic -1")
        if type(deck_branch) is not int or deck_branch not in (0, 1):
            raise ValueError("deck branch must be a bit")
        if type(exceptional_minus_one) is not bool:
            raise TypeError("exceptional_minus_one must be a Boolean")
        outgoing, jet = self.response(seam_carry)
        if exceptional_minus_one:
            # The signed -1 negacyclic payload replaces an ordinary all-ones
            # payload. A unit jump at the next incoming port certifies that
            # all-ones remainder without recovering the coefficient word.
            if boundary_sign != -1 or self.transducer.action.length == 0:
                raise ValueError("signed-minus-one deck requires a negacyclic block")
            following = self.transducer.action.apply(seam_carry + 1)
            if following != outgoing + 1 or following != -seam_carry:
                raise ValueError("response does not certify the signed-minus-one deck")
            correction = (
                PrimaryJetBlock.digit(1, degree=2, modulus=16)
                .power_block(self.transducer.action.length)
                .jet
            )
            jet = PrimaryCarryJet(
                jet.value + correction[0], jet.derivative + correction[1]
            )
        elif outgoing != boundary_sign * seam_carry:
            raise ValueError("seam carry is not a signed fixed point of this response")
        return EtalePrimaryCarryJetKey(deck_branch, seam_carry, jet)

    def then(
        self, after: PrimaryEtaleCarryJetTransducer
    ) -> PrimaryEtaleCarryJetTransducer:
        return PrimaryEtaleCarryJetTransducer(self.transducer.then(after.transducer))

    def power_block(self, exponent: int) -> PrimaryEtaleCarryJetTransducer:
        return PrimaryEtaleCarryJetTransducer(self.transducer.power_block(exponent))
