"""Exact symbolic comma transitions between decimal fork boundaries.

This is a constructor for *one* boundary macro.  It does not decide which
fork child has an infinite continuation.  The finite quotient and its
lifting theorem are separate admission obligations.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from math import gcd
from typing import Literal

from number_compiler.arithmetic.fields.consumer_pullback import (
    ONE as _Q_ONE,
)
from number_compiler.arithmetic.fields.consumer_pullback import (
    ZERO as _Q_ZERO,
)
from number_compiler.arithmetic.fields.consumer_pullback import (
    ExactRational,
)
from number_compiler.sequences.comma.arithmetic import (
    _sector_child_increments,
    phase_prefix_displacement,
)
from number_compiler.sequences.comma.boundary_chart import (
    PERIOD,
    ZERO_WEIGHT,
    chart_moves,
)

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
        if self.numerator_scale == 0:
            # Constant weights arise at every seam and in identity prefixes.
            # Their value is independent of the receiving decimal exponent;
            # constructing its scale here would turn a small observation into
            # an allocation proportional to an unrelated endpoint.
            return self.evaluate_at_scale(1, charge_bits=charge_bits)
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


_ZERO_WEIGHT = AffineWeight(0, 0, 1)


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

        A binary search locates the fragment. The final partial phase uses
        small residue arithmetic, bounded by its period of at most ten.
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
            if charge is not None:
                charge(tail + 1)
            if charge_bits is not None:
                charge_bits(
                    value.bit_length()
                    + cycles.bit_length()
                    + fragment.displacement.bit_length()
                    + 32 * tail
                )
            return (
                value
                + cycles * fragment.displacement
                + phase_prefix_displacement(
                    fragment.leading, fragment.entering_digit, tail
                )
            )
        if not 1 <= remaining <= fragment.literal_steps:
            raise AssertionError("partial comma run exceeds its admitted length")
        if remaining == fragment.literal_steps:
            return value + fragment.literal_increment
        # A multi-edge literal fragment contains only forced same-sector
        # Near moves. A crossing is always a separate singleton fragment.
        period = 10 // gcd(fragment.leading, 10)
        cycles, tail = divmod(remaining, period)
        phase_work = tail + (period if cycles else 0)
        if charge is not None:
            charge(phase_work + 1)
        if charge_bits is not None:
            charge_bits(value.bit_length() + cycles.bit_length() + 32 * phase_work)
        return value + phase_prefix_displacement(
            fragment.leading, fragment.entering_digit, remaining
        )


@dataclass(frozen=True, slots=True)
class _Affine:
    slope: Q
    offset: Q

    def plus(self, other: _Affine) -> _Affine:
        if other.is_zero:
            return self
        if self.is_zero:
            return other
        if self.slope.numerator == 0 and other.slope.numerator == 0:
            return _Affine(_Q_ZERO, self.offset + other.offset)
        return _Affine(self.slope + other.slope, self.offset + other.offset)

    def times(self, value: int) -> _Affine:
        if type(value) is not int:
            raise TypeError("exact rational components must be integers")
        if value == 0 or self.is_zero:
            return _ZERO_AFFINE
        if value == 1:
            return self
        return _Affine(
            _scale_rational(self.slope, value),
            _scale_rational(self.offset, value),
        )

    @property
    def is_zero(self) -> bool:
        return self.slope.numerator == 0 and self.offset.numerator == 0

    def weight(self) -> AffineWeight:
        if self.is_zero:
            return _ZERO_WEIGHT
        if self.slope.numerator == 0:
            return AffineWeight(0, self.offset.numerator, self.offset.denominator)
        if self.offset.numerator == 0:
            return AffineWeight(self.slope.numerator, 0, self.slope.denominator)
        denominator = self.slope.denominator * self.offset.denominator
        return AffineWeight(
            self.slope.numerator * self.offset.denominator,
            self.offset.numerator * self.slope.denominator,
            denominator,
        )


_ZERO_AFFINE = _Affine(_Q_ZERO, _Q_ZERO)


def _integer_rational(value: int) -> Q:
    if type(value) is not int:
        raise TypeError("exact rational components must be integers")
    if value == 0:
        return _Q_ZERO
    if value == 1:
        return _Q_ONE
    return Q(value)


def _scale_rational(value: Q, factor: int) -> Q:
    if type(factor) is not int:
        raise TypeError("exact rational components must be integers")
    if factor == 0 or value.numerator == 0:
        return _Q_ZERO
    if factor == 1:
        return value
    if value.denominator == 1:
        return _integer_rational(value.numerator * factor)
    return Q(value.numerator * factor, value.denominator)


def _constant(value: int) -> _Affine:
    if type(value) is not int:
        raise TypeError("exact rational components must be integers")
    if value == 0:
        return _ZERO_AFFINE
    return _Affine(_Q_ZERO, _integer_rational(value))


def _from_weight(weight: AffineWeight) -> _Affine:
    if any(
        type(part) is not int
        for part in (
            weight.numerator_scale,
            weight.numerator_offset,
            weight.denominator,
        )
    ):
        raise TypeError("exact rational components must be integers")
    if weight.denominator == 0:
        raise ValueError("exact rational denominator cannot be zero")
    if weight.numerator_scale == 0 and weight.numerator_offset == 0:
        return _ZERO_AFFINE
    if weight.denominator == 1:
        return _Affine(
            _integer_rational(weight.numerator_scale),
            _integer_rational(weight.numerator_offset),
        )
    return _Affine(
        _Q_ZERO
        if weight.numerator_scale == 0
        else Q(weight.numerator_scale, weight.denominator),
        _Q_ZERO
        if weight.numerator_offset == 0
        else Q(weight.numerator_offset, weight.denominator),
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
    charge_bits: Callable[[int], None] | None,
) -> MacroTemplate:
    prefix_weights = [_ZERO_WEIGHT]
    prefix_displacements = [_ZERO_WEIGHT]
    total_weight = _ZERO_AFFINE
    total_displacement = _ZERO_AFFINE
    for fragment in fragments:
        if charge is not None:
            charge(1)
        if charge_bits is not None:
            charge_bits(
                sum(
                    part.bit_length()
                    for part in (
                        total_weight.slope.numerator,
                        total_weight.slope.denominator,
                        total_weight.offset.numerator,
                        total_weight.offset.denominator,
                        total_displacement.slope.numerator,
                        total_displacement.slope.denominator,
                        total_displacement.offset.numerator,
                        total_displacement.offset.denominator,
                        fragment.complete_cycles.numerator_scale,
                        fragment.complete_cycles.numerator_offset,
                        fragment.complete_cycles.denominator,
                        fragment.period,
                        fragment.displacement,
                        fragment.literal_increment,
                    )
                )
            )
        complete_cycles = fragment.complete_cycles
        if (
            complete_cycles.numerator_scale == 0
            and complete_cycles.numerator_offset == 0
        ):
            # Literal fragments have a true zero cycle weight, so skip both
            # zero affine actions without assuming anything from period alone.
            cycle_weight = _ZERO_AFFINE
            cycle_displacement = _ZERO_AFFINE
        else:
            cycles = _from_weight(complete_cycles)
            cycle_weight = cycles.times(fragment.period)
            cycle_displacement = cycles.times(fragment.displacement)
        total_weight = total_weight.plus(cycle_weight).plus(
            _constant(fragment.literal_steps)
        )
        total_displacement = total_displacement.plus(cycle_displacement).plus(
            _constant(fragment.literal_increment)
        )
        prefix_weights.append(total_weight.weight())
        prefix_displacements.append(total_displacement.weight())
    if total_weight != weight:
        raise AssertionError("comma indexed macro weight differs from construction")
    source_value = _Affine(
        _integer_rational(source.a),
        _integer_rational(-1 if source.kind == "N" else 0),
    )
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


def construct_macro(
    source: BoundaryState,
    *,
    charge: Callable[[int], None] | None = None,
    charge_bits: Callable[[int], None] | None = None,
    grouped_near: bool = False,
) -> MacroTemplate:
    """Accumulate exact weights over the bounded Entry/Near chart machine.

    Entry consumes complete interior cycles; Near consumes bounded seam
    edges and reports all terminal alternatives. The optional grouped Near
    classifier is an exact validation view, not the default executor: its
    present catalog construction costs more than the bounded edge scan.
    No representative endpoint or sampled branch is constructed. The global
    winning-cycle and literal lifting proofs remain admission obligations.
    """
    weight = _constant(0)
    fragments: list[SectorFragment] = []
    relative_scale = 1
    previous_delta = 0
    near_run: tuple[int, int, int, int] | None = None

    def flush_near() -> None:
        nonlocal near_run, weight
        if near_run is not None:
            leading, digit, steps, increment = near_run
            weight = weight.plus(_constant(steps))
            fragments.append(
                SectorFragment(
                    leading, digit, AffineWeight(0, 0, 1), 0, 0, 0, steps, increment
                )
            )
            near_run = None

    for chart, move in chart_moves(
        source.kind,
        source.a,
        source.exponent_residue,
        charge=charge,
        charge_bits=charge_bits,
        grouped_near=grouped_near,
    ):
        if charge_bits is not None:
            charge_bits(
                relative_scale.bit_length()
                + weight.slope.numerator.bit_length()
                + weight.slope.denominator.bit_length()
                + weight.offset.numerator.bit_length()
                + weight.offset.denominator.bit_length()
                + 32
            )
        # Delta changes only by one at a power-of-ten crossing. This is the
        # symbolic affine coefficient 10**delta, never the actual 10**p.
        if chart.delta != previous_delta:
            if chart.delta != previous_delta + 1:
                raise AssertionError("comma chart skipped an exponent seam")
            relative_scale *= 10
            previous_delta = chart.delta
        f, x = chart.leading, chart.coordinate
        if move.next_chart is None:
            flush_near()
            if chart.kind != "near" or move.terminal_chart != chart:
                raise AssertionError("comma terminal move lost its chart")
            if move.weight != ZERO_WEIGHT:
                raise AssertionError("comma terminal move has nonzero weight")
            if charge is not None:
                charge(1)
            digit = (-x) % 10
            if charge_bits is not None:
                charge_bits(f.bit_length() + x.bit_length() + digit.bit_length())
            terminal_increments = _sector_child_increments(f, digit, x)
            if len(terminal_increments) == 2:
                if move.fork_a != f + 1:
                    raise AssertionError(
                        "comma terminal alternatives disagree with chart"
                    )
            elif terminal_increments or move.fork_a is not None:
                raise AssertionError("comma terminal alternatives disagree with chart")
            endpoint = _Affine(Q((f + 1) * relative_scale), Q(-x))
            a = move.fork_a
            children = (
                ()
                if a is None
                else (
                    BoundaryState(
                        "N", a, (source.exponent_residue + chart.delta) % PERIOD
                    ),
                    BoundaryState(
                        "Z", a, (source.exponent_residue + chart.delta) % PERIOD
                    ),
                )
            )
            return _indexed_macro(
                source,
                "landmine" if a is None else "fork",
                chart.delta,
                a,
                weight,
                endpoint,
                children,
                fragments,
                charge,
                charge_bits,
            )
        emitted = move.weight
        if emitted.scale and emitted.exponent_delta != chart.delta:
            raise AssertionError("comma weight has a foreign exponent chart")
        if move.cycle is None and move.next_chart.kind == "near":
            if (
                emitted.scale != 0
                or emitted.exponent_delta != 0
                or emitted.denominator != 1
                or emitted.offset <= 0
                or move.next_chart.leading != f
                or move.next_chart.delta != chart.delta
                or move.literal_increment != x - move.next_chart.coordinate
            ):
                raise AssertionError("comma Near run lost its constant physical weight")
            digit = (-x) % 10
            steps_added = emitted.offset
            if charge is not None:
                charge(steps_added % (10 // gcd(f, 10)) + 1)
            if charge_bits is not None:
                charge_bits(
                    steps_added.bit_length() + move.literal_increment.bit_length() + 32
                )
            if phase_prefix_displacement(
                f, digit, steps_added
            ) != move.literal_increment or x <= move.literal_increment + int(f < 9):
                raise AssertionError(
                    "comma Near run weight differs from phase semantics"
                )
            if near_run is None:
                near_run = (f, digit, steps_added, move.literal_increment)
            else:
                leading, entering_digit, steps, increment = near_run
                if leading != f or (entering_digit + steps * f) % 10 != digit:
                    raise AssertionError("comma Near run lost its phase binding")
                near_run = (
                    leading,
                    entering_digit,
                    steps + steps_added,
                    increment + move.literal_increment,
                )
            continue
        flush_near()
        step_weight = _Affine(
            Q(emitted.scale * relative_scale, emitted.denominator),
            Q(emitted.offset, emitted.denominator),
        )
        weight = weight.plus(step_weight)
        if move.cycle is not None:
            transfer = move.cycle
            count = _Affine(
                step_weight.slope / Q(transfer.period),
                step_weight.offset / Q(transfer.period),
            )
            fragments.append(
                SectorFragment(
                    f,
                    x % 10,
                    count.weight(),
                    transfer.period,
                    transfer.displacement,
                    transfer.maximum_guard,
                    0,
                    0,
                )
            )
        else:
            digit = (-x) % 10
            fragments.append(
                SectorFragment(
                    f, digit, AffineWeight(0, 0, 1), 0, 0, 0, 1, move.literal_increment
                )
            )
    raise AssertionError("comma chart returned without a terminal outcome")


__all__ = [
    "PERIOD",
    "AffineWeight",
    "BoundaryState",
    "MacroTemplate",
    "SectorFragment",
    "construct_macro",
]
