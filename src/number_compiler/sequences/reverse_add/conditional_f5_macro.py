"""Exact conditional F5 actions on source-certified reverse/add border returns.

The Q19 border producer can certify a finite closed outer trace without
certifying that the interior Q19 source repeats.  This module turns exactly
that finite trace into an affine F5 action.  Repeating the action is exposed
as conditional algebra only: callers must supply the forcing word and accept
the hypothesis that both the carry ports and forcing word repeat.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.fields.morphism_core import binary_power

from .border_carry_safety import ConditionalBorderCycle, conditional_return_from_trace

if TYPE_CHECKING:
    from .q19_border_control import CertifiedBorderGrowth
    from .q19_occurrence import ReversePairOutputOccurrence

_F5 = 5


@dataclass(frozen=True, slots=True)
class F5AffineAction:
    """The exact map ``x ↦ multiplier*x + offset`` over F5."""

    multiplier: int
    offset: int

    def __post_init__(self) -> None:
        if type(self.multiplier) is not int or not 0 <= self.multiplier < _F5:
            raise ValueError("F5 multiplier must be a canonical residue")
        if type(self.offset) is not int or not 0 <= self.offset < _F5:
            raise ValueError("F5 offset must be a canonical residue")

    def then(self, later: F5AffineAction) -> F5AffineAction:
        """Compose chronological actions, applying ``self`` before ``later``."""
        if type(later) is not F5AffineAction:
            raise TypeError("later action must be an F5 affine action")
        return F5AffineAction(
            later.multiplier * self.multiplier % _F5,
            (later.multiplier * self.offset + later.offset) % _F5,
        )

    def repeat(self, count: int) -> F5AffineAction:
        """Power an affine action by squaring in logarithmic composition work."""
        if type(count) is not int:
            raise TypeError("repeat count must be an exact integer")
        if count < 0:
            raise ValueError("repeat count must be a nonnegative integer")
        return binary_power(
            self,
            count,
            identity=F5AffineAction(1, 0),
            compose=lambda first, second: first.then(second),
        ).value

    def apply(self, value: int) -> int:
        if type(value) is not int:
            raise TypeError("F5 input must be an integer")
        return (self.multiplier * (value % _F5) + self.offset) % _F5


@dataclass(frozen=True, slots=True)
class SourceCertifiedF5Macro:
    """A finite conditional F5 program derived from a live Q19 border return.

    ``forcing_weights[i]`` multiplies the source-specific correction inserted
    at physical tick ``i``.  A zero weight proves that unknown input is
    irrelevant; a nonzero weight must remain supplied by the consumer.
    ``growth_word`` and the border cycle are authenticated only over the
    certificate's finite slice.  The type carries no future-source authority.
    """

    certificate: CertifiedBorderGrowth
    start: int
    cycle: ConditionalBorderCycle
    z: int
    multipliers: tuple[int, ...]
    forcing_weights: tuple[int, ...]
    homogeneous_multiplier: int

    def __post_init__(self) -> None:
        self.validate()

    @classmethod
    def from_certificate(
        cls,
        certificate: CertifiedBorderGrowth,
        *,
        start: int = 0,
        steps: int | None = None,
        z: int = 2,
    ) -> SourceCertifiedF5Macro:
        """Build an F5 action only from a complete, certified border slice."""
        certificate.validate(certificate.owner, certificate.source)
        if type(start) is not int or start < 0:
            raise ValueError("macro start must be a nonnegative physical tick")
        if type(z) is not int or not 0 <= z < _F5:
            raise ValueError("F5 evaluation point must be in 0..4")
        duration = len(certificate.growth_word) - start if steps is None else steps
        if type(duration) is not int or duration < 1:
            raise ValueError("macro duration must be a positive integer")
        end = start + duration
        if end > len(certificate.growth_word):
            raise ValueError("macro exceeds its certified growth horizon")
        if len(certificate.outer_pairs) != len(certificate.growth_word) + 1:
            raise ValueError("certificate has no complete outer-border trace")
        outer = certificate.outer_pairs[start : end + 1]
        growth = certificate.growth_word[start:end]
        if any(pair is None for pair in outer):
            raise ValueError("macro contains an unresolved border phase")
        exact_outer = tuple(pair for pair in outer if pair is not None)
        try:
            cycle = conditional_return_from_trace(exact_outer, growth)
        except ValueError as exc:
            raise ValueError(
                "certified slice is not a closed conditional return"
            ) from exc
        multipliers = tuple((1 + z) % _F5 if bit else 2 for bit in growth)
        weights = [0] * duration
        suffix = 1
        for index in range(duration - 1, -1, -1):
            weights[index] = suffix
            suffix = suffix * multipliers[index] % _F5
        return cls(
            certificate,
            start,
            cycle,
            z,
            multipliers,
            tuple(weights),
            suffix,
        )

    @property
    def duration(self) -> int:
        return len(self.multipliers)

    @property
    def source(self) -> ReversePairOutputOccurrence:
        return self.certificate.source

    @property
    def conditional_only(self) -> bool:
        return True

    def validate(self) -> None:
        certificate = self.certificate
        certificate.validate(certificate.owner, certificate.source)
        if (
            type(self.start) is not int
            or self.start < 0
            or type(self.z) is not int
            or not 0 <= self.z < _F5
            or type(self.cycle) is not ConditionalBorderCycle
            or type(self.multipliers) is not tuple
            or type(self.forcing_weights) is not tuple
            or len(self.multipliers) != len(self.forcing_weights)
            or not self.multipliers
            or any(
                type(value) is not int or not 0 <= value < _F5
                for value in self.multipliers
            )
            or any(
                type(value) is not int or not 0 <= value < _F5
                for value in self.forcing_weights
            )
            or type(self.homogeneous_multiplier) is not int
            or not 0 <= self.homogeneous_multiplier < _F5
        ):
            raise ValueError("invalid source-certified F5 macro")
        end = self.start + self.duration
        if end > len(certificate.growth_word):
            raise ValueError("macro exceeds its source certificate")
        outer = certificate.outer_pairs[self.start : end + 1]
        growth = certificate.growth_word[self.start : end]
        if (
            len(outer) != self.duration + 1
            or any(pair is None for pair in outer)
            or tuple(self.cycle.growth) != growth
        ):
            raise ValueError("macro does not match its certified source slice")
        exact_outer = tuple(pair for pair in outer if pair is not None)
        expected_cycle = conditional_return_from_trace(exact_outer, growth)
        expected_multipliers = tuple((1 + self.z) % _F5 if bit else 2 for bit in growth)
        expected_weights = [0] * self.duration
        suffix = 1
        for index in range(self.duration - 1, -1, -1):
            expected_weights[index] = suffix
            suffix = suffix * expected_multipliers[index] % _F5
        if (
            self.cycle != expected_cycle
            or self.multipliers != expected_multipliers
            or self.forcing_weights != tuple(expected_weights)
            or self.homogeneous_multiplier != suffix
        ):
            raise ValueError("F5 action differs from its authenticated border slice")

    def affine_action(self, forcing: tuple[int | None, ...]) -> F5AffineAction | None:
        """Return the exact affine map when every live forcing port is known."""
        self.validate()
        if type(forcing) is not tuple or len(forcing) != self.duration:
            raise ValueError("one optional correction is required per physical tick")
        if any(value is not None and type(value) is not int for value in forcing):
            raise TypeError("F5 corrections must be exact integers or unknown")
        offset = 0
        for weight, correction in zip(self.forcing_weights, forcing, strict=True):
            if weight == 0:
                continue
            if type(correction) is not int:
                return None
            offset = (offset + weight * (correction % _F5)) % _F5
        return F5AffineAction(self.homogeneous_multiplier, offset)

    def apply(
        self,
        initial: int | None,
        forcing: tuple[int | None, ...],
    ) -> int | None:
        """Evaluate one certified return, preserving every unknown live port."""
        if initial is not None and type(initial) is not int:
            raise TypeError("initial F5 input must be an exact integer or unknown")
        action = self.affine_action(forcing)
        if action is None:
            return None
        if action.multiplier and type(initial) is not int:
            return None
        return action.apply(0 if initial is None else initial)

    def conditional_repeat(
        self,
        count: int,
        initial: int | None,
        forcing: tuple[int | None, ...],
    ) -> int | None:
        """Power under an explicit repeated-cycle/forcing assumption.

        The Q19 certificate authorizes one finite return.  This method only
        composes its affine F5 action algebraically; it does not validate a
        second source return or establish that future forcing repeats.
        """
        self.validate()
        if type(count) is not int or count < 0:
            raise ValueError("conditional repeat count must be nonnegative")
        if initial is not None and type(initial) is not int:
            raise TypeError("initial F5 input must be an exact integer or unknown")
        if count == 0:
            if type(initial) is not int:
                return None
            return initial % _F5
        action = self.affine_action(forcing)
        if action is None:
            return None
        if action.multiplier and type(initial) is not int:
            return None
        return action.repeat(count).apply(0 if initial is None else initial)


__all__ = ["F5AffineAction", "SourceCertifiedF5Macro"]
