"""Canonical two-primary successor-image filtration for special numbers.

This module owns the semantic object shared by Fermat and Mersenne certificate
construction.  It deliberately separates three facts which older code mixed:

* the *finite candidate-derived filtration* (exact but currently bounded);
* the closed pure-two-primary theorem (scalable once purity is established);
* the higher-2^k character reader needed to establish the same filtration
  without enumerating the finite carrier.

The third item is not faked.  Only the outer quadratic character is currently a
scalable ring-safe query.  Deeper character levels raise
:class:`HigherTwoPowerCharacterUnavailable` rather than falling back to a raw
Pépin/Lucas--Lehmer recurrence, factorization, or a prime label.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.functions.finite_unary import (
    UnaryQuotientMachine,
    unary_target_distance_machine,
)
from number_compiler.sequences.prime.set import jacobi_symbol


class HigherTwoPowerCharacterUnavailable(RuntimeError):
    """Raised when a requested scalable character level is not implemented."""


@dataclass(frozen=True, slots=True)
class PureTwoPrimaryClockShape:
    """Constant-storage target clock implied by an already-proved pure shape.

    This object is a conditional dynamics theorem.  Constructing it does not
    prove that a candidate is prime or has the pure two-primary carrier.  It is
    safe for production certificate metadata only after a separate terminal or
    classical proof has established that premise.
    """

    family: str
    parameter: int
    modulus_bits: int
    observer_offset: int
    active_exponent: int
    target_depth: int
    target_horizon: int

    @property
    def quotient_classes(self) -> int:
        return self.target_depth + 2

    @property
    def image_depth_classes(self) -> int:
        return self.quotient_classes

    @property
    def stable_image_states(self) -> int:
        return 2 if self.family == "fermat" else 1 << (self.parameter - 2)

    @property
    def source_action_state(self) -> int:
        return self.target_depth + 1

    def action_after_clock_steps(self, steps: int) -> int:
        """Jump the pulled target-distance action without a transition table."""
        steps = int(steps)
        if steps < 0:
            raise ValueError(steps)
        return max(0, self.source_action_state - steps)

    def target_after_clock_steps(self, steps: int) -> bool:
        return self.action_after_clock_steps(steps) == 1


def pure_two_primary_clock_shape(
    family: str, parameter: int
) -> PureTwoPrimaryClockShape:
    """Return O(1) metadata for the conditional pure two-primary clock."""
    family, parameter = str(family), int(parameter)
    if family == "fermat":
        if parameter < 2:
            raise ValueError((family, parameter))
        width = 1 << parameter
        offset = parameter + 1
        active = width - offset
        return PureTwoPrimaryClockShape(
            family,
            parameter,
            width + 1,
            offset,
            active,
            active - 1,
            width - 1,
        )
    if family == "mersenne":
        if parameter < 3 or not parameter & 1:
            raise ValueError((family, parameter))
        active = parameter - 1
        return PureTwoPrimaryClockShape(
            family,
            parameter,
            parameter,
            0,
            active,
            active - 1,
            parameter - 2,
        )
    raise ValueError(family)


@dataclass(frozen=True, slots=True)
class TwoPrimaryCharacterProbe:
    """One exact candidate-derived image-membership character query.

    ``membership`` is ``False`` only when the query proves that the canonical
    source has no predecessor at this image level.  ``None`` means the deeper
    higher-2^k character is not yet available scalably; it never means a guessed
    answer.
    """

    family: str
    parameter: int
    level: int
    membership: bool | None
    method: str
    reciprocity_descents: int = 0
    gcd_witness: int | None = None

    @property
    def decided(self) -> bool:
        return self.membership is not None


@dataclass(frozen=True, slots=True)
class TwoPrimaryImageFiltration:
    """Exact successor-image/stable-residual descriptor.

    For a finite candidate-derived proof, ``image_ranks`` is the exact nested
    image sequence through the repeated fixed rank.  ``depth_strata`` counts the
    states at finite image depths and ``stable_image_states`` is the eventual
    fixed image.  The Moore partition is compared with image depth explicitly:
    composite candidates such as M11 are therefore represented honestly rather
    than being forced into the prime depth formula.

    For a pure theorem instance, the same fields are produced algebraically and
    ``carrier_states_enumerated`` is zero.
    """

    family: str
    parameter: int
    modulus_bits: int
    observer_offset: int
    image_ranks: tuple[int, ...]
    depth_strata: tuple[int, ...]
    stable_image_states: int
    source_image_depth: int
    target_image_depths: tuple[int, ...]
    moore_classes: int
    image_depth_classes: int
    moore_equals_image_depth: bool
    source_target_hitting_time: int | None
    expected_target_step: int
    target_at_expected_step: bool
    pure_two_primary_shape: bool
    construction_method: str
    carrier_states_enumerated: int = 0
    construction_raw_squarings: int = 0
    character_queries: int = 0
    reciprocity_descents: int = 0
    gcd_witnesses: int = 0
    scalable_construction: bool = False
    machine: UnaryQuotientMachine | None = None
    source_class: int | None = None

    def __post_init__(self) -> None:
        if self.family not in ("fermat", "mersenne"):
            raise ValueError(self.family)
        if self.parameter < 0 or self.modulus_bits <= 0 or self.observer_offset < 0:
            raise ValueError((self.parameter, self.modulus_bits, self.observer_offset))
        if not self.image_ranks or self.image_ranks[-1] != self.stable_image_states:
            raise ValueError((self.image_ranks, self.stable_image_states))
        if self.image_depth_classes != len(self.depth_strata) + 1:
            raise ValueError((self.image_depth_classes, self.depth_strata))
        if self.pure_two_primary_shape and not self.moore_equals_image_depth:
            raise ValueError("pure two-primary shape must be Moore/image-depth exact")
        if self.carrier_states_enumerated < 0 or self.construction_raw_squarings < 0:
            raise ValueError(
                (self.carrier_states_enumerated, self.construction_raw_squarings)
            )

    @property
    def decided(self) -> bool:
        """Whether the expected special-number target predicate was proved."""
        return True

    @property
    def status(self) -> str:
        return "prime" if self.target_at_expected_step else "composite"

    @property
    def target_image_depth(self) -> int | None:
        if len(self.target_image_depths) != 1:
            return None
        return self.target_image_depths[0]

    @property
    def active_two_group_exponent(self) -> int:
        return len(self.depth_strata)

    @property
    def quotient_classes(self) -> int:
        return self.moore_classes

    @property
    def target_horizon(self) -> int:
        return self.expected_target_step

    def image_ranks_through_stability(self) -> tuple[int, ...]:
        return self.image_ranks

    def target_distance_from_depth(self, depth: int) -> int | None:
        """Use the depth timestamp only when the candidate proves that theorem."""
        if not self.pure_two_primary_shape:
            raise ValueError(
                "target distance is not a function of image depth on this candidate"
            )
        target_depth = self.target_image_depth
        if target_depth is None:
            raise ValueError(self.target_image_depths)
        depth = int(depth)
        if depth == -1:
            return None
        if not 0 <= depth <= target_depth:
            raise ValueError((depth, target_depth))
        return target_depth - depth


def pure_two_primary_image_filtration(
    family: str,
    parameter: int,
) -> TwoPrimaryImageFiltration:
    """Closed pure-two-primary filtration theorem, with zero carrier work.

    This is a dynamics theorem only.  It must not be used as a classifier unless
    the candidate-derived construction has independently established the pure
    shape.
    """
    family = str(family)
    parameter = int(parameter)
    shape = pure_two_primary_clock_shape(family, parameter)
    if family == "fermat":
        n = parameter
        width = 1 << n
        modulus = (1 << width) + 1
        if jacobi_symbol(3, modulus) != -1:
            raise AssertionError((family, n, "outer-character"))
        stable = shape.stable_image_states
        ranks = tuple(
            stable
            if level >= shape.active_exponent
            else 1 + (1 << (shape.active_exponent - level))
            for level in range(shape.active_exponent + 1)
        ) + (stable,)
        strata = tuple(
            ranks[level] - ranks[level + 1] for level in range(shape.active_exponent)
        )
    elif family == "mersenne":
        p = parameter
        modulus = (1 << p) - 1
        outer = tuple(sorted((jacobi_symbol(6, modulus), jacobi_symbol(-2, modulus))))
        if outer != (-1, -1):
            raise AssertionError((family, p, outer))
        stable = shape.stable_image_states
        ranks = tuple(
            stable
            if level >= shape.active_exponent
            else stable + (1 << (shape.active_exponent - 1 - level))
            for level in range(shape.active_exponent + 1)
        ) + (stable,)
        strata = tuple(
            ranks[level] - ranks[level + 1] for level in range(shape.active_exponent)
        )
    else:
        raise ValueError(family)
    target_depths = (shape.target_depth,)
    classes = shape.quotient_classes
    machine = unary_target_distance_machine(shape.target_depth)
    return TwoPrimaryImageFiltration(
        family,
        parameter,
        shape.modulus_bits,
        shape.observer_offset,
        ranks,
        strata,
        stable,
        0,
        target_depths,
        classes,
        classes,
        True,
        shape.target_horizon,
        shape.target_horizon,
        True,
        True,
        "pure-two-primary-theorem",
        0,
        0,
        1,
        1,
        0,
        True,
        machine,
        shape.source_action_state,
    )


def outer_source_character(family: str, parameter: int) -> TwoPrimaryCharacterProbe:
    """The currently available scalable ring-safe outer image character.

    It proves the canonical source has image depth zero.  It does *not* prove
    the rest of the image tower or primality of the candidate.
    """
    family = str(family)
    parameter = int(parameter)
    if family == "fermat":
        width = 1 << parameter
        modulus = (1 << width) + 1
        symbol = jacobi_symbol(3, modulus)
        return TwoPrimaryCharacterProbe(
            family,
            parameter,
            1,
            False if symbol == -1 else None,
            "jacobi-source-square-boundary",
            1,
        )
    if family == "mersenne":
        modulus = (1 << parameter) - 1
        pair = tuple(sorted((jacobi_symbol(6, modulus), jacobi_symbol(-2, modulus))))
        return TwoPrimaryCharacterProbe(
            family,
            parameter,
            1,
            False if pair == (-1, -1) else None,
            "jacobi-trace-preimage-boundary",
            2,
        )
    raise ValueError(family)


def higher_two_power_character(
    family: str,
    parameter: int,
    level: int,
) -> TwoPrimaryCharacterProbe:
    """Query the canonical source's nested image character.

    Level one is the exact scalable outer character above.  Higher levels are
    deliberately unavailable until a reciprocity construction is proved.  A
    caller cannot silently substitute repeated squaring or carrier enumeration.
    """
    level = int(level)
    if level < 1:
        raise ValueError(level)
    if level == 1:
        return outer_source_character(family, parameter)
    raise HigherTwoPowerCharacterUnavailable((family, int(parameter), level))


__all__ = [
    "HigherTwoPowerCharacterUnavailable",
    "PureTwoPrimaryClockShape",
    "TwoPrimaryCharacterProbe",
    "TwoPrimaryImageFiltration",
    "higher_two_power_character",
    "outer_source_character",
    "pure_two_primary_clock_shape",
    "pure_two_primary_image_filtration",
]
