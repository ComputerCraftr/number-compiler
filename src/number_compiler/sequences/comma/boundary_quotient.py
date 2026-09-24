"""Exact symbolic comma transitions between decimal fork boundaries.

This is a constructor for *one* boundary macro.  It does not decide which
fork child has an infinite continuation.  The finite quotient and its
lifting theorem are separate admission obligations.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd
from collections.abc import Callable
from typing import Literal

from number_compiler.arithmetic.fields.consumer_pullback import ExactRational
from number_compiler.sequences.comma.arithmetic import (
    _decimal_sector_from_scale,
    _large_sector_children,
    cycle_transfer,
    decimal_sector,
)

PERIOD = 924
Q = ExactRational


@dataclass(frozen=True, slots=True)
class BoundaryState:
    kind: Literal["N", "Z"]
    a: int
    exponent_residue: int

    def __post_init__(self) -> None:
        if (
            self.kind not in ("N", "Z")
            or type(self.a) is not int
            or not 2 <= self.a <= 9
        ):
            raise ValueError("invalid comma boundary constructor")
        if (
            type(self.exponent_residue) is not int
            or not 0 <= self.exponent_residue < PERIOD
        ):
            raise ValueError("invalid comma exponent residue")

    def value(
        self, exponent: int, *, charge_bits: Callable[[int], None] | None = None
    ) -> int:
        if (
            type(exponent) is not int
            or exponent < 5
            or exponent % PERIOD != self.exponent_residue
        ):
            raise ValueError("exponent does not belong to boundary quotient state")
        if charge_bits is not None:
            charge_bits(4 * exponent + 1)
        scale = int(pow(10, exponent))
        if charge_bits is not None:
            charge_bits(scale.bit_length() + self.a.bit_length())
        return self.a * scale - (self.kind == "N")


@dataclass(frozen=True, slots=True)
class AffineWeight:
    """Exact (A*10**p+B)/D, normalized using the shared rational owner."""

    numerator_scale: int
    numerator_offset: int
    denominator: int

    def __post_init__(self) -> None:
        if (
            any(
                type(part) is not int
                for part in (
                    self.numerator_scale,
                    self.numerator_offset,
                    self.denominator,
                )
            )
            or self.denominator <= 0
        ):
            raise ValueError("invalid comma affine weight")
        divisor = gcd(
            gcd(abs(self.numerator_scale), abs(self.numerator_offset)),
            self.denominator,
        )
        object.__setattr__(self, "numerator_scale", self.numerator_scale // divisor)
        object.__setattr__(self, "numerator_offset", self.numerator_offset // divisor)
        object.__setattr__(self, "denominator", self.denominator // divisor)

    def evaluate(
        self, exponent: int, *, charge_bits: Callable[[int], None] | None = None
    ) -> int:
        if type(exponent) is not int or exponent < 0:
            raise ValueError("invalid comma weight exponent")
        if charge_bits is not None:
            charge_bits(4 * exponent + 1)
        return self.evaluate_at_scale(int(pow(10, exponent)), charge_bits=charge_bits)

    def evaluate_at_scale(
        self,
        scale: int,
        *,
        charge_bits: Callable[[int], None] | None = None,
    ) -> int:
        if type(scale) is not int or scale <= 0:
            raise ValueError("invalid comma affine input scale")
        if charge_bits is not None:
            charge_bits(
                self.numerator_scale.bit_length()
                + scale.bit_length()
                + self.numerator_offset.bit_length()
                + self.denominator.bit_length()
            )
        numerator = self.numerator_scale * scale + self.numerator_offset
        value, remainder = divmod(numerator, self.denominator)
        if remainder:
            raise ValueError("comma weight is not integral at this exponent")
        return value


@dataclass(frozen=True, slots=True)
class SectorFragment:
    leading: int
    entering_digit: int
    complete_cycles: AffineWeight
    period: int
    displacement: int
    maximum_guard: int
    literal_steps: int
    literal_increment: int


@dataclass(frozen=True, slots=True)
class MacroTemplate:
    source: BoundaryState
    outcome: Literal["fork", "landmine"]
    exponent_delta: int
    destination_a: int | None
    weight: AffineWeight
    endpoint: AffineWeight
    ordered_children: tuple[BoundaryState, ...]
    sector_fragments: tuple[SectorFragment, ...]
    prefix_weights: tuple[AffineWeight, ...]
    prefix_displacements: tuple[AffineWeight, ...]

    def point(
        self,
        exponent: int,
        transitions: int,
        *,
        charge: Callable[[int], None] | None = None,
        charge_bits: Callable[[int], None] | None = None,
        validate_read: Callable[[str, int], None] | None = None,
    ) -> int:
        """Select an exact term inside this macro by weighted fragment descent.

        A binary search locates the fragment.  Only the final partial phase
        uses literal arithmetic, bounded by its period of at most ten.
        The fork-choice transition is excluded from this macro.
        """
        if (
            type(exponent) is not int
            or exponent < 5
            or exponent % PERIOD != self.source.exponent_residue
        ):
            raise ValueError("exponent does not belong to boundary quotient state")
        if type(transitions) is not int or transitions < 0:
            raise ValueError("comma macro transition offset must be nonnegative")
        if charge is not None:
            charge(1)
        if charge_bits is not None:
            charge_bits(4 * exponent + 1)
        scale = int(pow(10, exponent))
        if charge_bits is not None:
            charge_bits(scale.bit_length() + self.source.a.bit_length())
        source_value = self.source.a * scale - (self.source.kind == "N")
        total = self.weight.evaluate_at_scale(scale, charge_bits=charge_bits)
        if transitions > total:
            raise ValueError("comma macro transition offset exceeds endpoint")
        if transitions == 0:
            return source_value
        if transitions == total:
            return self.endpoint.evaluate_at_scale(scale, charge_bits=charge_bits)
        low, high = 1, len(self.prefix_weights) - 1
        while low < high:
            if charge is not None:
                charge(1)
            middle = (low + high) // 2
            if validate_read is not None:
                validate_read("weight", middle)
            if (
                self.prefix_weights[middle].evaluate_at_scale(
                    scale, charge_bits=charge_bits
                )
                >= transitions
            ):
                high = middle
            else:
                low = middle + 1
        fragment_index = low - 1
        if validate_read is not None:
            validate_read("fragment", fragment_index)
            validate_read("weight", fragment_index)
            validate_read("displacement", fragment_index)
        fragment = self.sector_fragments[fragment_index]
        before = self.prefix_weights[fragment_index].evaluate_at_scale(
            scale, charge_bits=charge_bits
        )
        value = source_value + self.prefix_displacements[
            fragment_index
        ].evaluate_at_scale(scale, charge_bits=charge_bits)
        remaining = transitions - before
        if fragment.period:
            cycles, tail = divmod(remaining, fragment.period)
            if cycles > fragment.complete_cycles.evaluate_at_scale(
                scale, charge_bits=charge_bits
            ):
                raise AssertionError("partial comma macro exceeds admitted cycles")
            value += cycles * fragment.displacement
            for _ in range(tail):
                if charge is not None:
                    charge(1)
                if charge_bits is not None:
                    charge_bits(value.bit_length())
                children = _large_sector_children(value, decimal_sector(value))
                if len(children) != 1:
                    raise AssertionError("partial comma cycle crossed a seam")
                value = children[0]
            return value
        if remaining != 1 or fragment.literal_steps != 1:
            raise AssertionError("partial comma seam is not a single transition")
        return value + fragment.literal_increment


@dataclass(frozen=True, slots=True)
class _Affine:
    slope: Q
    offset: Q

    def at_scale(self, scale: int) -> int:
        value = self.slope * Q(scale) + self.offset
        quotient, remainder = divmod(value.numerator, value.denominator)
        if remainder:
            raise ValueError("nonintegral symbolic comma occurrence")
        return quotient

    def plus(self, other: _Affine) -> _Affine:
        return _Affine(self.slope + other.slope, self.offset + other.offset)

    def times(self, value: int) -> _Affine:
        return _Affine(self.slope * Q(value), self.offset * Q(value))

    def weight(self) -> AffineWeight:
        denominator = self.slope.denominator * self.offset.denominator
        return AffineWeight(
            self.slope.numerator * self.offset.denominator,
            self.offset.numerator * self.slope.denominator,
            denominator,
        )


def _constant(value: int) -> _Affine:
    return _Affine(Q(0), Q(value))


def _from_weight(weight: AffineWeight) -> _Affine:
    return _Affine(
        Q(weight.numerator_scale, weight.denominator),
        Q(weight.numerator_offset, weight.denominator),
    )


def _indexed_macro(
    source: BoundaryState,
    outcome: Literal["fork", "landmine"],
    delta: int,
    destination_a: int | None,
    weight: _Affine,
    endpoint: _Affine,
    children: tuple[BoundaryState, ...],
    fragments: list[SectorFragment],
    charge: Callable[[int], None] | None,
) -> MacroTemplate:
    prefix_weights = [_constant(0).weight()]
    prefix_displacements = [_constant(0).weight()]
    total_weight = _constant(0)
    total_displacement = _constant(0)
    for fragment in fragments:
        if charge is not None:
            charge(1)
        cycles = _from_weight(fragment.complete_cycles)
        total_weight = total_weight.plus(
            cycles.times(fragment.period).plus(_constant(fragment.literal_steps))
        )
        total_displacement = total_displacement.plus(
            cycles.times(fragment.displacement).plus(
                _constant(fragment.literal_increment)
            )
        )
        prefix_weights.append(total_weight.weight())
        prefix_displacements.append(total_displacement.weight())
    if total_weight != weight:
        raise AssertionError("comma indexed macro weight differs from construction")
    source_value = _Affine(Q(source.a), Q(-1 if source.kind == "N" else 0))
    if source_value.plus(total_displacement) != endpoint:
        raise AssertionError("comma indexed macro endpoint differs from construction")
    return MacroTemplate(
        source,
        outcome,
        delta,
        destination_a,
        weight.weight(),
        endpoint.weight(),
        children,
        tuple(fragments),
        tuple(prefix_weights),
        tuple(prefix_displacements),
    )


def _sample_exponent(residue: int) -> int:
    return residue if residue >= 5 else residue + PERIOD


def construct_macro(
    source: BoundaryState,
    *,
    charge: Callable[[int], None] | None = None,
    charge_bits: Callable[[int], None] | None = None,
) -> MacroTemplate:
    """Build a symbolic transition to the next fork or landmine.

    Sample evaluation selects only finite phase/seam predicates.  All long
    cycle counts, endpoint values and literal weights are derived by exact
    affine arithmetic and a residue-fixed floor remainder.  This routine is
    a research constructor until periodic lifting and finite classification
    are checked; production must consume admitted templates instead.
    """

    exponent = _sample_exponent(source.exponent_residue)
    if charge_bits is not None:
        charge_bits(4 * exponent + 1)
    sample_scale = int(pow(10, exponent))
    sample_sector_scale = sample_scale
    sector_exponent = exponent
    value = _Affine(Q(source.a), Q(-1 if source.kind == "N" else 0))
    weight = _constant(0)
    fragments: list[SectorFragment] = []
    for _ in range(4096):
        if charge is not None:
            charge(1)
        if charge_bits is not None:
            charge_bits(
                sample_scale.bit_length()
                + value.slope.numerator.bit_length()
                + value.offset.numerator.bit_length()
            )
        sample = value.at_scale(sample_scale)
        while sample >= 10 * sample_sector_scale:
            sample_sector_scale *= 10
            sector_exponent += 1
        sector = _decimal_sector_from_scale(
            sample, sample_sector_scale, sector_exponent
        )
        children = _large_sector_children(sample, sector)
        if len(children) != 1:
            delta = sector.exponent - exponent
            if len(children) == 2:
                a = sector.leading + 1
                boundary = a * 10**sector.exponent
                if children != (boundary - 1, boundary):
                    raise AssertionError("fork violates boundary normal form")
                choices: tuple[BoundaryState, ...] = (
                    BoundaryState("N", a, (source.exponent_residue + delta) % PERIOD),
                    BoundaryState("Z", a, (source.exponent_residue + delta) % PERIOD),
                )
                outcome: Literal["fork", "landmine"] = "fork"
            elif not children:
                a = None
                choices = ()
                outcome = "landmine"
            else:
                raise AssertionError("more than two comma children")
            return _indexed_macro(
                source,
                outcome,
                delta,
                a,
                weight,
                value,
                choices,
                fragments,
                charge,
            )

        transfer = cycle_transfer(sector.leading, sector.digit)
        # The strict guard is H - j*P > M for every complete cycle.  Its
        # maximum safe count is floor((H-1-M)/P)+1 when positive.
        relative_exponent = sector.exponent - exponent
        if relative_exponent < 0:
            raise ValueError("comma macro moved below its source scale")
        if charge_bits is not None:
            charge_bits(4 * relative_exponent + 1)
        relative_scale = 10**relative_exponent
        boundary = _Affine(Q((sector.leading + 1) * relative_scale), Q(0))
        headroom = boundary.plus(value.times(-1))
        margin = headroom.plus(_constant(-1 - transfer.maximum_guard))
        margin_sample = margin.at_scale(sample_scale)
        if margin_sample >= 0:
            remainder = margin_sample % transfer.displacement
            count = margin.plus(_constant(-remainder)).times(1)
            count = _Affine(
                count.slope / Q(transfer.displacement),
                count.offset / Q(transfer.displacement),
            ).plus(_constant(1))
            if count.at_scale(sample_scale) <= 0:
                raise AssertionError("positive cycle margin produced no cycle")
            value = value.plus(count.times(transfer.displacement))
            weight = weight.plus(count.times(transfer.period))
            fragments.append(
                SectorFragment(
                    sector.leading,
                    sector.digit,
                    count.weight(),
                    transfer.period,
                    transfer.displacement,
                    transfer.maximum_guard,
                    0,
                    0,
                )
            )
            continue

        value = value.plus(_constant(children[0] - sample))
        weight = weight.plus(_constant(1))
        fragments.append(
            SectorFragment(
                sector.leading,
                sector.digit,
                AffineWeight(0, 0, 1),
                0,
                0,
                0,
                1,
                children[0] - sample,
            )
        )
    raise ValueError("comma boundary macro exceeded its finite seam bound")


__all__ = [
    "AffineWeight",
    "BoundaryState",
    "MacroTemplate",
    "PERIOD",
    "SectorFragment",
    "construct_macro",
]
