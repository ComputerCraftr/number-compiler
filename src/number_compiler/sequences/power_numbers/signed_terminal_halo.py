"""Exact signed-fold carry-birth projection into the NC14 halo algebra.

This is a *consumer* of an already authenticated cyclic/negacyclic folded
coefficient SLP.  It deliberately cannot manufacture a source certificate from
an unwrapped 3^(2^t) low-radix/CRT packet, and never returns a prime label.

The mod-16 primary tangent is formed from adjacent *observed* signed-fold
birth jets, not by guessing the quadratic forcing from a small digit window.
This allows proof producers to connect to the existing four-birth consumer
without hiding the still-open source-to-global-fold morphism.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.carry.signed_weighted_carry import WideSignedCarryAction
from number_compiler.arithmetic.fields.walsh import WalshH5
from number_compiler.arithmetic.polynomials.primary_jet import (
    PrimaryJetAffineMorphism,
    primary_jet_from_digits,
)
from number_compiler.sequences.power_numbers.source_halo import (
    HALO_BOUNDARIES,
    compose_last_four_source_tangents,
)


@dataclass(frozen=True, slots=True)
class SignedFoldBirthWindow:
    """An exact *spatial* birth window, not a source-authenticated prime proof."""

    sign: int
    width: int
    start: int
    birth_parity_mask: int
    carry_parity_mask: int
    carries: tuple[int, ...]
    digits: tuple[int, ...]
    births: tuple[int, ...]

    def __post_init__(self) -> None:
        if self.sign not in (-1, 1) or self.width < 1:
            raise ValueError("invalid signed-fold birth window")
        if self.start < 0 or self.start + len(self.births) > self.width:
            raise ValueError("invalid signed-fold window range")
        if not 1 <= len(self.births) <= 64:
            raise ValueError("only finite 1..64-cell windows are admitted")
        if (len(self.digits), len(self.carries)) != (
            len(self.births),
            len(self.births) + 1,
        ):
            raise ValueError("incomplete signed-fold birth witnesses")
        mask = (1 << len(self.births)) - 1
        if self.birth_parity_mask & ~mask or self.carry_parity_mask & ~mask:
            raise ValueError("signed-fold parity mask exceeds demand")
        for i, birth in enumerate(self.births):
            if birth != self.carries[i] - 2 * self.carries[i + 1]:
                raise ValueError("unauthenticated carry-cochain birth")
            if birth & 1 != (self.birth_parity_mask >> i) & 1:
                raise ValueError("incorrect signed-fold birth parity")
            if self.carries[i] & 1 != (self.carry_parity_mask >> i) & 1:
                raise ValueError("incorrect signed-fold carry parity")
        if self.birth_parity_mask != self.carry_parity_mask:
            raise ValueError("binary carry-birth parity identity failed")

    @property
    def h5(self) -> WalshH5:
        """Exact finite projection, derived only when the consumer requests it."""
        return WalshH5.from_mask(self.birth_parity_mask, len(self.births))

    @property
    def first_halo_carries(self) -> tuple[int, ...]:
        """Only the carry boundaries covered by the requested window."""
        return tuple(
            self.carries[position - self.start]
            for position in HALO_BOUNDARIES
            if self.start <= position <= self.start + len(self.births)
        )


def demand_signed_birth_window(
    action: WideSignedCarryAction, *, start: int = 0, length: int = 64
) -> SignedFoldBirthWindow:
    """Project exact carry parity and H5 from a signed-fold SLP.

    ``WideSignedCarryAction`` verifies the signed cyclic seam.  This routine
    additionally checks every demanded cochain identity, but does *not*
    certify that its input coefficients came from the Fermat/Mersenne power.
    """
    if type(action) is not WideSignedCarryAction:
        raise TypeError("signed-fold demand requires the exact carry action")
    if type(start) is not int or type(length) is not int:
        raise TypeError("signed-fold demand geometry must be exact integers")
    if not 0 <= start < action.width or not 1 <= length <= 64:
        raise ValueError("invalid signed-fold window geometry")
    if start + length > action.width:
        raise ValueError("signed-fold window exceeds authenticated fold width")
    if not action.verify_cochain():
        raise ArithmeticError("signed-fold cochain or seam verification failed")
    demanded = action.demand(tuple(range(start, start + length)))
    carries = tuple(carry for _position, _digit, carry in demanded) + (
        action.carry_at(start + length),
    )
    digits = tuple(digit for _position, digit, _carry in demanded)
    births = tuple(carries[i] - 2 * carries[i + 1] for i in range(length))
    mask = sum((birth & 1) << i for i, birth in enumerate(births))
    return SignedFoldBirthWindow(
        action.sign,
        action.width,
        start,
        mask,
        sum((carry & 1) << i for i, carry in enumerate(carries[:-1])),
        carries,
        digits,
        births,
    )


@dataclass(frozen=True, slots=True)
class FourBirthPrimaryObservation:
    """A proven affine *observation* over five exact consecutive fold sources.

    The forcing B_t is computed from the *actual next birth jet*, not inferred
    from unwrapped low-port masks.  This demonstrates the connection to the
    nilpotent consumer while exposing exactly what an efficient source
    publisher still needs to construct.
    """

    result: PrimaryJetAffineMorphism
    endpoint_birth_jet: tuple[int, int]
    forcing_offsets: tuple[tuple[int, int], ...]
    demanded_birth_packets: tuple[WalshH5, ...]
    source_authenticated: bool = False

    def __post_init__(self) -> None:
        if not self.result.source_annihilated or self.result.steps != 4:
            raise ValueError("four-birth affine action did not annihilate old jet")
        if self.result.offset != self.endpoint_birth_jet:
            raise ValueError("four-birth affine action disagrees with endpoint")
        if len(self.forcing_offsets) != 4 or len(self.demanded_birth_packets) != 5:
            raise ValueError("four-birth proof is missing a required source")
        if self.source_authenticated:
            raise ValueError("source authentication belongs to an independent proof")


def compose_four_exact_birth_observations(
    actions: tuple[WideSignedCarryAction, ...],
) -> FourBirthPrimaryObservation:
    """Compose four chronological mod-16 tangents using five *real* fold rows.

    This operation consumes authenticated-in-their-own-right signed carry rows
    and verifies the affine algebra.  It is intentionally incapable of
    deciding whether those rows are the correct power-sequence sources.
    """
    if type(actions) is not tuple or len(actions) != 5:
        raise ValueError("five exact consecutive signed-fold sources are required")
    if any(type(action) is not WideSignedCarryAction for action in actions):
        raise TypeError("every source must be an exact signed-fold action")
    sign = actions[0].sign
    width = actions[0].width
    if any(action.sign != sign or action.width != width for action in actions):
        raise ValueError("source sign/width mismatch")
    birth_jets: list[tuple[int, ...]] = []
    base_jets: list[tuple[int, ...]] = []
    harmonics: list[WalshH5] = []
    for action in actions:
        # Computing a full degree-two primary jet by walking the coefficient
        # SLP is source-output work, not a claimed constant-time prime query.
        # Explicitly cap the proof cone to independently checked small widths.
        if width > 64:
            raise ValueError("five-fold full-primary observation exceeds 64 cells")
        window = demand_signed_birth_window(action, length=width)
        birth_jets.append(
            primary_jet_from_digits(window.births, degree=2, modulus=16).jet
        )
        base_jets.append(
            primary_jet_from_digits(window.digits, degree=2, modulus=16).jet
        )
        harmonics.append(window.h5)
    tangents: list[PrimaryJetAffineMorphism] = []
    forcing: list[tuple[int, int]] = []
    for i in range(4):
        twice_base = (2 * base_jets[i][0] % 16, 2 * base_jets[i][1] % 16)
        product = (
            twice_base[0] * birth_jets[i][0] % 16,
            (twice_base[0] * birth_jets[i][1] + twice_base[1] * birth_jets[i][0]) % 16,
        )
        offset = (
            (birth_jets[i + 1][0] - product[0]) % 16,
            (birth_jets[i + 1][1] - product[1]) % 16,
        )
        forcing.append(offset)
        tangents.append(
            PrimaryJetAffineMorphism.square_tangent(
                base_jets[i], offset, degree=2, modulus=16
            )
        )
    result = compose_last_four_source_tangents(tuple(tangents))
    endpoint = birth_jets[-1]
    if len(endpoint) != 2:
        raise ArithmeticError("degree-two birth jet has the wrong dimension")
    endpoint_birth_jet = (endpoint[0], endpoint[1])
    return FourBirthPrimaryObservation(
        result, endpoint_birth_jet, tuple(forcing), tuple(harmonics)
    )


__all__ = [
    "FourBirthPrimaryObservation",
    "SignedFoldBirthWindow",
    "compose_four_exact_birth_observations",
    "demand_signed_birth_window",
]
