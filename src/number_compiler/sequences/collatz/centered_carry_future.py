"""Source-bound, finite carry observations on an all-odd Collatz suffix."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import Literal

from number_compiler.arithmetic.carry.carry_normalization import RadixCarryBlock
from number_compiler.arithmetic.fields.dyadic_unit_phase import DyadicUnitPhase


@dataclass(frozen=True, slots=True)
class GuardedCenteredValuationBellman:
    """Remaining valuation for admitted two-odd returns."""

    initial_guaranteed_v2: int

    def __post_init__(self) -> None:
        if (
            type(self.initial_guaranteed_v2) is not int
            or self.initial_guaranteed_v2 < 0
        ):
            raise ValueError("centered valuation must be nonnegative")

    def after_returns(self, returns: int) -> int | None:
        if type(returns) is not int or returns < 0:
            raise ValueError("return count must be nonnegative")
        remaining = self.initial_guaranteed_v2 - 2 * returns
        return remaining if remaining >= 0 else None


@dataclass(frozen=True, slots=True)
class CarryEventHits:
    homogeneous: int | None = None
    corrected: int | None = None


@dataclass(frozen=True, slots=True)
class CenteredCarryFuture:
    """Carry columns of the centered source over an admitted all-odd span."""

    centered: int
    precision: int
    headroom: int
    period: int

    @classmethod
    def from_normalized_source(cls, source: int, precision: int) -> CenteredCarryFuture:
        if type(source) is not int or source < 1 or not source & 1:
            raise ValueError("centered carry future requires a positive odd source")
        if type(precision) is not int or precision < 1:
            raise ValueError("centered carry precision must be positive")
        centered = source + 1
        headroom = (centered & -centered).bit_length() - 1
        active = max(1, precision - headroom)
        bases: tuple[Literal[3, 5, 15], ...] = (3, 5, 15)
        period = max(
            DyadicUnitPhase.from_exponent(base, 0, active).order for base in bases
        )
        return cls(centered, precision, headroom, period)

    def first_same_time_even(
        self,
        cuts: tuple[int, ...],
        *,
        horizon: int,
        max_phase_states: int,
        reserve_bits: Callable[[int], None],
        include_correction: bool,
    ) -> CarryEventHits:
        if horizon > self.headroom:
            raise ValueError("future carry horizon exceeds certified odd headroom")
        if horizon == 0:
            return CarryEventHits()
        reserve_bits(
            8 * (self.precision + self.centered.bit_length() + len(cuts) * 65 + 64)
        )
        boundaries = sorted(set(cuts))
        segments: list[tuple[int, int, bool]] = []
        previous = 0
        for cut in boundaries:
            span = cut - previous
            digits = (self.centered >> previous) & ((1 << span) - 1)
            # The low bits of -2**tick cross exactly the cuts above the
            # source valuation throughout the admitted interval.
            segments.append((span, digits, cut > self.headroom))
            previous = cut
        mask = (1 << self.precision) - 1
        multiplier3 = multiplier5 = 1
        homogeneous = corrected = None
        limit = min(horizon, self.period, max_phase_states)
        for tick in range(1, limit + 1):
            multiplier3 = multiplier3 * 3 & mask
            multiplier5 = multiplier5 * 5 & mask
            plain_match = homogeneous is None
            corrected_match = include_correction and corrected is None
            carry = 0
            for span, digits, correction in segments:
                carry = RadixCarryBlock(2, span, multiplier3 * digits).outgoing_carry(
                    carry
                )
                parity = carry & 1
                plain_match = plain_match and parity == 0
                corrected_match = corrected_match and parity == correction
                if not (plain_match or corrected_match):
                    break
            if (
                (plain_match or corrected_match)
                and _even_carry_row(multiplier5, segments)
                and _even_carry_row(multiplier3 * multiplier5 & mask, segments)
            ):
                if plain_match:
                    homogeneous = tick
                if corrected_match:
                    corrected = tick
                if homogeneous is not None and (
                    not include_correction or corrected is not None
                ):
                    return CarryEventHits(homogeneous, corrected)
        if limit < min(horizon, self.period):
            raise ValueError("future carry phase budget exceeded")
        return CarryEventHits(homogeneous, corrected)


def _even_carry_row(multiplier: int, segments: list[tuple[int, int, bool]]) -> bool:
    carry = 0
    for span, digits, _correction in segments:
        carry = RadixCarryBlock(2, span, multiplier * digits).outgoing_carry(carry)
        if carry & 1:
            return False
    return True
