"""Bounded C1 and higher-wire projections for admitted comma chart paths.

The C1 recurrence owns exact lower-two-digit powering, and the boundary chart
owns Entry/Near transitions. This module joins those existing owners for a
single fixed-sector segment. It never selects a fork or landmine, crosses a
leading-sector seam, or issues future/source authority. A caller must start
the next segment from its separately admitted chart occurrence.

The modulo-924 exponent phase is source occurrence data. Physical transition
steps do not advance that exponent selector. Returned carry formulas are
arithmetic projections only; they are not proof IDs or branch certificates.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from .arithmetic import classify_near_port
from .boundary_chart import (
    PERIOD,
    BoundaryChart,
    ChartWeight,
    chart_step,
    near_chart_target,
    validate_chart,
)
from .carry_generator import BitsCharge, C1Phase, C1Return, WorkCharge


def _charge(
    charge_work: WorkCharge | None,
    charge_bits: BitsCharge | None,
    work: int,
    *operands: int,
    extra_bits: int = 0,
) -> None:
    if charge_work is not None:
        charge_work(work)
    if charge_bits is not None:
        charge_bits(sum(abs(value).bit_length() for value in operands) + extra_bits)


def _decimal_power_at_least(
    exponent: int,
    threshold: int,
    *,
    charge_work: WorkCharge | None,
    charge_bits: BitsCharge | None,
) -> bool:
    """Compare ``10**exponent >= threshold`` without a large unused power."""
    if type(exponent) is not int or exponent < 0 or type(threshold) is not int:
        raise ValueError("invalid decimal clock comparison")
    if threshold <= 1:
        return True
    # 10**e > 2**(3e); when 3e reaches the threshold bit length, the answer
    # is already known without constructing a scale proportional to e.
    if 3 * exponent >= threshold.bit_length():
        return True
    _charge(charge_work, charge_bits, 1, exponent, threshold, extra_bits=4 * exponent)
    return int(10**exponent) >= threshold


def _decimal_power_greater_than(
    exponent: int,
    threshold: int,
    *,
    charge_work: WorkCharge | None,
    charge_bits: BitsCharge | None,
) -> bool:
    """Compare ``10**exponent > threshold`` without an oversized scale."""
    if type(exponent) is not int or exponent < 0 or type(threshold) is not int:
        raise ValueError("invalid decimal boundary comparison")
    if threshold <= 0:
        return True
    # A positive threshold has at least one bit. This bound is strict because
    # 10**e > 2**(3e) and threshold < 2**bit_length.
    if 3 * exponent >= threshold.bit_length():
        return True
    _charge(charge_work, charge_bits, 1, exponent, threshold, extra_bits=4 * exponent)
    return int(10**exponent) > threshold


def _duration_at_least(
    weight: ChartWeight,
    exponent: int,
    steps: int,
    *,
    charge_work: WorkCharge | None,
    charge_bits: BitsCharge | None,
) -> bool:
    """Test an affine chart duration against ``steps`` exactly and boundedly."""
    if (
        type(weight) is not ChartWeight
        or any(
            type(value) is not int
            for value in (
                weight.scale,
                weight.exponent_delta,
                weight.offset,
                weight.denominator,
                exponent,
                steps,
            )
        )
        or weight.scale < 0
        or weight.denominator <= 0
        or exponent < 0
        or steps < 0
    ):
        raise ValueError("invalid affine chart-duration comparison")
    # Charge the compact operands first. Do not charge a decimal-width-sized
    # intermediate until the comparison below actually has to materialize
    # one: zero/small durations and large symbolic exponents are resolved by
    # the bounded comparison in ``_decimal_power_at_least``.
    _charge(
        charge_work,
        charge_bits,
        1,
        weight.scale,
        weight.exponent_delta,
        weight.offset,
        weight.denominator,
        exponent,
        steps,
    )
    if weight.scale == 0:
        return weight.offset >= weight.denominator * steps
    power = exponent + weight.exponent_delta
    if power < 0:
        raise ValueError("chart duration is outside its exponent domain")
    needed_numerator = weight.denominator * steps - weight.offset
    if needed_numerator <= 0:
        return True
    required_scale = (needed_numerator + weight.scale - 1) // weight.scale
    return _decimal_power_at_least(
        power,
        required_scale,
        charge_work=charge_work,
        charge_bits=charge_bits,
    )


_GUARDED_POWER_SEAL = object()


def _chart_clock_signature(chart: BoundaryChart) -> tuple[str, int, int, int]:
    if type(chart) is not BoundaryChart:
        raise ValueError("comma carry chart changed after construction")
    if (
        type(chart.kind) is not str
        or chart.kind not in ("entry", "near")
        or any(
            type(value) is not int
            for value in (chart.leading, chart.delta, chart.coordinate)
        )
    ):
        raise ValueError("comma carry chart has malformed snapshot fields")
    return chart.kind, chart.leading, chart.delta, chart.coordinate


def _chart_weight_signature(weight: ChartWeight) -> tuple[int, int, int, int]:
    if type(weight) is not ChartWeight or any(
        type(value) is not int
        for value in (
            weight.scale,
            weight.exponent_delta,
            weight.offset,
            weight.denominator,
        )
    ):
        raise ValueError("comma carry weight changed after construction")
    return weight.scale, weight.exponent_delta, weight.offset, weight.denominator


@dataclass(frozen=True, slots=True, init=False)
class GuardedC1ChartPower:
    """Exact C1 power contained in one admitted chart segment.

    Instances can only be issued by ``powered_chart_carry``, which checks the
    first-event duration and sector/port guards before publication. The sealed
    result is an arithmetic projection, not an authenticated source handle;
    applications that need source authority must retain and validate their
    original ``BoundaryOccurrence``.
    """

    _chart: BoundaryChart
    _exponent: int
    _exponent_phase: int
    _action: C1Return
    _headroom_weight: ChartWeight
    _witness: tuple[object, ...] = field(repr=False, compare=False)
    _seal: object = field(repr=False, compare=False)

    def __init__(self) -> None:
        raise TypeError("GuardedC1ChartPower is issued by powered_chart_carry")

    @classmethod
    def from_admitted_segment(
        cls,
        exponent_phase: int,
        chart: BoundaryChart,
        exponent: int,
        steps: int,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> GuardedC1ChartPower:
        """Check and publish one bounded Entry/Near chart segment."""
        if type(exponent_phase) is not int or not 0 <= exponent_phase < PERIOD:
            raise ValueError("invalid comma exponent clock")
        if type(chart) is not BoundaryChart:
            raise TypeError("power requires a canonical BoundaryChart")
        validate_chart(exponent_phase, chart)
        if (
            type(exponent) is not int
            or exponent < 5
            or exponent % PERIOD != exponent_phase
        ):
            raise ValueError("chart exponent and external clock disagree")
        if type(steps) is not int or steps < 0:
            raise ValueError("chart power requires a nonnegative duration")
        _charge(charge_work, charge_bits, 1, exponent, exponent_phase, steps)

        if chart.kind == "entry":
            first_move = chart_step(exponent_phase, chart, charge_bits=charge_bits)
            if first_move.next_chart is None or first_move.cycle is None:
                raise ArithmeticError("Entry source has no canonical Near event")
            if not _duration_at_least(
                first_move.weight,
                exponent,
                steps,
                charge_work=charge_work,
                charge_bits=charge_bits,
            ):
                raise ValueError("powered C1 exceeds the first Entry/Near event")
        elif steps:
            if near_chart_target(chart).next_chart is None:
                raise ValueError("powered C1 exceeds the first Near terminal event")
            immediate_border = int(chart.leading < 9)
            if chart.coordinate <= immediate_border:
                raise ValueError("powered C1 exceeds the immediate Near event")
            near_port = classify_near_port(
                chart.leading,
                chart.coordinate,
                charge_work=charge_work,
                charge_bits=charge_bits,
            )
            if steps > near_port.physical_steps:
                raise ValueError("powered C1 exceeds the first Near port")

        phase = C1Phase.from_suffix(
            chart.leading,
            chart.coordinate if chart.kind == "entry" else (-chart.coordinate) % 100,
        )
        action = C1Return(
            phase,
            steps,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )
        displacement = action.displacement(
            charge_work=charge_work,
            charge_bits=charge_bits,
        )
        extra = int(chart.leading < 9)
        if chart.kind == "entry":
            # N=f*10**width+x; keep headroom_after>extra to exclude the next
            # leading-sector transition from this segment.
            if steps and not _decimal_power_greater_than(
                exponent + chart.delta,
                chart.coordinate + displacement + extra,
                charge_work=charge_work,
                charge_bits=charge_bits,
            ):
                raise ValueError("powered C1 crosses its Entry sector guard")
            headroom = ChartWeight(
                1, chart.delta, -(chart.coordinate + displacement), 1
            )
        else:
            headroom_after = chart.coordinate - displacement
            if steps and headroom_after <= extra:
                raise ValueError("powered C1 crosses its Near sector guard")
            headroom = ChartWeight(0, 0, headroom_after, 1)
        return cls._issue(chart, exponent, exponent_phase, action, headroom)

    @classmethod
    def _issue(
        cls,
        chart: BoundaryChart,
        exponent: int,
        exponent_phase: int,
        action: C1Return,
        headroom_weight: ChartWeight,
    ) -> GuardedC1ChartPower:
        result = object.__new__(cls)
        object.__setattr__(result, "_chart", chart)
        object.__setattr__(result, "_exponent", exponent)
        object.__setattr__(result, "_exponent_phase", exponent_phase)
        object.__setattr__(result, "_action", action)
        object.__setattr__(result, "_headroom_weight", headroom_weight)
        witness = result._current_signature()
        object.__setattr__(result, "_witness", witness)
        object.__setattr__(result, "_seal", _GUARDED_POWER_SEAL)
        return result

    def _current_signature(self) -> tuple[object, ...]:
        if (
            type(self._chart) is not BoundaryChart
            or type(self._action) is not C1Return
            or type(self._headroom_weight) is not ChartWeight
            or type(self._exponent) is not int
            or self._exponent < 5
            or type(self._exponent_phase) is not int
            or not 0 <= self._exponent_phase < PERIOD
            or self._exponent % PERIOD != self._exponent_phase
        ):
            raise ValueError("invalid guarded comma C1 chart power")
        start, target, steps, count = self._action.structural_snapshot()
        return (
            id(self._chart),
            _chart_clock_signature(self._chart),
            self._exponent,
            self._exponent_phase,
            id(self._action),
            (start.sector, start.mod4, start.mod25),
            (target.sector, target.mod4, target.mod25),
            steps,
            count,
            id(self._headroom_weight),
            _chart_weight_signature(self._headroom_weight),
        )

    def validate(self) -> None:
        if getattr(self, "_seal", None) is not _GUARDED_POWER_SEAL:
            raise ValueError("invalid or uninitialized comma C1 chart power")
        if getattr(self, "_witness", None) != self._current_signature():
            raise ValueError("comma C1 chart power differs from its snapshot")

    @property
    def chart(self) -> BoundaryChart:
        self.validate()
        return self._chart

    @property
    def exponent(self) -> int:
        self.validate()
        return self._exponent

    @property
    def exponent_phase(self) -> int:
        self.validate()
        return self._exponent_phase

    @property
    def action(self) -> C1Return:
        self.validate()
        return self._action

    @property
    def headroom_weight(self) -> ChartWeight:
        self.validate()
        return self._headroom_weight

    @property
    def leading(self) -> int:
        """Leading digit while this source-bound segment remains in-sector."""
        self.validate()
        return self._chart.leading

    @property
    def width(self) -> int:
        """Physical decimal exponent of the exact receiving chart."""
        self.validate()
        return self._exponent + self._chart.delta

    @property
    def selected_exponent_phase(self) -> int:
        """Modulo-924 phase of this chart; physical steps do not advance it."""
        self.validate()
        return (self._exponent_phase + self._chart.delta) % PERIOD

    @property
    def suffix(self) -> int:
        self.validate()
        return self._action.target.suffix

    @property
    def carry_count(self) -> int:
        self.validate()
        return self._action.count

    @property
    def duration(self) -> int:
        self.validate()
        return self._action.steps

    @property
    def displacement(self) -> int:
        self.validate()
        return self._action.displacement()

    def wire_total(
        self,
        wire: int,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> int:
        """Project exact carry totals without visiting intermediate digits.

        Wire zero counts ones-to-tens carries; wire one is the C1 count. For
        Entry, higher initial prefixes are aligned to decimal powers. For Near,
        the admitted prefix leaves fewer than ten C1 carries, so no higher
        wire can fire before its first terminal Near event.
        """
        if type(wire) is not int or wire < 0:
            raise ValueError("carry wire must be a nonnegative integer")
        self.validate()
        width = self._exponent + self._chart.delta
        _charge(
            charge_work,
            charge_bits,
            1,
            wire,
            width,
            self._action.count,
            self._action.steps,
        )
        if wire == 0:
            return (
                self._action.start.ones + self._action.steps * self._chart.leading
            ) // 10
        if wire == 1:
            return self._action.count
        if self._chart.kind == "near" or wire >= width - 1:
            return 0
        return _quotient_by_10_power(
            self._action.count,
            wire - 1,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )


def _quotient_by_10_power(
    value: int,
    exponent: int,
    *,
    charge_work: WorkCharge | None = None,
    charge_bits: BitsCharge | None = None,
) -> int:
    """Compute exact floor(value/10**exponent), avoiding unused large scales."""
    if type(value) is not int or value < 0 or type(exponent) is not int or exponent < 0:
        raise ValueError("invalid decimal carry-clock quotient")
    if exponent == 0:
        return value
    if 3 * exponent >= value.bit_length():
        _charge(charge_work, charge_bits, 1, value, exponent)
        return 0
    _charge(
        charge_work,
        charge_bits,
        1,
        value,
        exponent,
        extra_bits=4 * exponent,
    )
    return value // int(10**exponent)


@dataclass(frozen=True, slots=True)
class WidthCarryFormula:
    """Symbolic carry count ``10**(p + shift) - subtract`` or zero."""

    shift: int
    subtract: int
    is_zero: bool = False

    def __post_init__(self) -> None:
        if (
            type(self.shift) is not int
            or type(self.subtract) is not int
            or self.subtract < 0
            or type(self.is_zero) is not bool
        ):
            raise ValueError("invalid width carry formula")


_SYMBOLIC_ENTRY_CLOCK_SEAL = object()


@dataclass(frozen=True, slots=True, init=False)
class SymbolicEntryCarryClock:
    """Factory-issued source-phase Entry return with a symbolic wire tower."""

    _chart: BoundaryChart
    _exponent: int
    _exponent_phase: int
    _destination: BoundaryChart
    _duration: ChartWeight
    _witness: tuple[object, ...] = field(repr=False, compare=False)
    _seal: object = field(repr=False, compare=False)

    def __init__(self) -> None:
        raise TypeError(
            "SymbolicEntryCarryClock is issued by symbolic_entry_carry_clock"
        )

    @classmethod
    def from_entry(
        cls,
        exponent_phase: int,
        chart: BoundaryChart,
        exponent: int,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> SymbolicEntryCarryClock:
        """Check and publish the chart's canonical first Entry return."""
        if type(exponent_phase) is not int or not 0 <= exponent_phase < PERIOD:
            raise ValueError("invalid comma exponent clock")
        if type(chart) is not BoundaryChart:
            raise TypeError("entry clock requires a canonical BoundaryChart")
        validate_chart(exponent_phase, chart)
        if chart.kind != "entry":
            raise ValueError("symbolic Entry clock requires an Entry chart")
        if (
            type(exponent) is not int
            or exponent < 5
            or exponent % PERIOD != exponent_phase
        ):
            raise ValueError("Entry exponent and external clock disagree")
        if charge_work is not None:
            charge_work(1)
        move = chart_step(exponent_phase, chart, charge_bits=charge_bits)
        target = move.next_chart
        if target is None or target.kind != "near" or move.cycle is None:
            raise ArithmeticError("Entry did not provide an admitted Near return")
        beta = (target.coordinate + 99) // 100
        if not 1 <= beta <= 6:
            raise ArithmeticError("Entry Near headroom is outside its carry quotient")
        if move.weight.scale <= 0 or move.weight.denominator <= 0:
            raise ArithmeticError("Entry chart produced a nonpositive duration")
        return cls._issue(chart, exponent, exponent_phase, target, move.weight)

    @classmethod
    def _issue(
        cls,
        chart: BoundaryChart,
        exponent: int,
        exponent_phase: int,
        destination: BoundaryChart,
        duration: ChartWeight,
    ) -> SymbolicEntryCarryClock:
        result = object.__new__(cls)
        object.__setattr__(result, "_chart", chart)
        object.__setattr__(result, "_exponent", exponent)
        object.__setattr__(result, "_exponent_phase", exponent_phase)
        object.__setattr__(result, "_destination", destination)
        object.__setattr__(result, "_duration", duration)
        witness = result._current_signature()
        object.__setattr__(result, "_witness", witness)
        object.__setattr__(result, "_seal", _SYMBOLIC_ENTRY_CLOCK_SEAL)
        return result

    def _current_signature(self) -> tuple[object, ...]:
        if (
            type(self._chart) is not BoundaryChart
            or self._chart.kind != "entry"
            or type(self._destination) is not BoundaryChart
            or self._destination.kind != "near"
            or type(self._duration) is not ChartWeight
            or type(self._exponent) is not int
            or self._exponent < 5
            or type(self._exponent_phase) is not int
            or not 0 <= self._exponent_phase < PERIOD
            or self._exponent % PERIOD != self._exponent_phase
            or self._destination.leading != self._chart.leading
            or self._destination.delta != self._chart.delta
        ):
            raise ValueError("invalid symbolic Entry carry clock")
        if (
            type(self._chart.kind) is not str
            or type(self._destination.kind) is not str
            or type(self._destination.leading) is not int
            or type(self._destination.delta) is not int
            or type(self._destination.coordinate) is not int
            or type(self._duration.scale) is not int
            or type(self._duration.exponent_delta) is not int
            or type(self._duration.offset) is not int
            or type(self._duration.denominator) is not int
            or self._duration.scale <= 0
            or self._duration.exponent_delta != self._chart.delta
            or self._duration.denominator <= 0
        ):
            raise ValueError("Entry carry clock has malformed snapshot fields")
        return (
            id(self._chart),
            _chart_clock_signature(self._chart),
            self._exponent,
            self._exponent_phase,
            id(self._destination),
            _chart_clock_signature(self._destination),
            id(self._duration),
            _chart_weight_signature(self._duration),
        )

    def validate(self) -> None:
        if getattr(self, "_seal", None) is not _SYMBOLIC_ENTRY_CLOCK_SEAL:
            raise ValueError("invalid or uninitialized symbolic Entry carry clock")
        if getattr(self, "_witness", None) != self._current_signature():
            raise ValueError("symbolic Entry carry clock differs from its snapshot")

    @property
    def chart(self) -> BoundaryChart:
        self.validate()
        return self._chart

    @property
    def exponent(self) -> int:
        self.validate()
        return self._exponent

    @property
    def exponent_phase(self) -> int:
        self.validate()
        return self._exponent_phase

    @property
    def destination(self) -> BoundaryChart:
        self.validate()
        return self._destination

    @property
    def duration(self) -> ChartWeight:
        self.validate()
        return self._duration

    @property
    def width(self) -> int:
        self.validate()
        return self._exponent + self._chart.delta

    @property
    def beta(self) -> int:
        self.validate()
        return (self._destination.coordinate + 99) // 100

    @property
    def target_suffix(self) -> int:
        self.validate()
        return (-self._destination.coordinate) % 100

    @property
    def target_leading(self) -> int:
        self.validate()
        return self._chart.leading

    @property
    def selected_exponent_phase(self) -> int:
        self.validate()
        return (self._exponent_phase + self._chart.delta) % PERIOD

    def c0_weight(self) -> ChartWeight:
        """Closed affine total of ones-to-tens carries for this Entry return."""
        self.validate()
        duration = self._duration
        leading = self._chart.leading
        initial_ones = self._chart.coordinate % 10
        target_ones = (-self._destination.coordinate) % 10
        return ChartWeight(
            leading * duration.scale,
            duration.exponent_delta,
            leading * duration.offset
            + duration.denominator * (initial_ones - target_ones),
            10 * duration.denominator,
        )

    def wire_formula(
        self,
        wire: int,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> WidthCarryFormula:
        """Return a higher-wire formula for this complete Entry return."""
        self.validate()
        if type(wire) is not int or wire < 1:
            raise ValueError("symbolic carry wire must be positive")
        _charge(
            charge_work,
            charge_bits,
            1,
            wire,
            self._exponent + self._chart.delta,
            (self._destination.coordinate + 99) // 100,
        )
        beta = (self._destination.coordinate + 99) // 100
        if beta < 1 or beta > 6:
            raise ValueError("Entry carry clock has an invalid Near quotient")
        if wire >= self._exponent + self._chart.delta:
            return WidthCarryFormula(0, 0, is_zero=True)
        if wire == 1:
            return WidthCarryFormula(self._chart.delta - 2, beta)
        return WidthCarryFormula(self._chart.delta - wire - 1, 1)


def symbolic_entry_carry_clock(
    exponent_phase: int,
    chart: BoundaryChart,
    exponent: int,
    *,
    charge_work: WorkCharge | None = None,
    charge_bits: BitsCharge | None = None,
) -> SymbolicEntryCarryClock:
    """Derive the symbolic first Entry return using the checked class factory."""
    return SymbolicEntryCarryClock.from_entry(
        exponent_phase,
        chart,
        exponent,
        charge_work=charge_work,
        charge_bits=charge_bits,
    )


def powered_chart_carry(
    exponent_phase: int,
    chart: BoundaryChart,
    exponent: int,
    steps: int,
    *,
    charge_work: WorkCharge | None = None,
    charge_bits: BitsCharge | None = None,
) -> GuardedC1ChartPower:
    """Check and power one bounded segment using the checked class factory."""
    return GuardedC1ChartPower.from_admitted_segment(
        exponent_phase,
        chart,
        exponent,
        steps,
        charge_work=charge_work,
        charge_bits=charge_bits,
    )


__all__ = [
    "GuardedC1ChartPower",
    "SymbolicEntryCarryClock",
    "WidthCarryFormula",
    "powered_chart_carry",
    "symbolic_entry_carry_clock",
]
