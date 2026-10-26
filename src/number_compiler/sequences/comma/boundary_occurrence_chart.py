"""Exact C1 arithmetic for source-bound comma chart occurrences.

This module evaluates the finite chart segments already sealed into a macro
template. It does not select a future branch or issue repetition authority.
"""

from __future__ import annotations

from typing import Protocol

from .arithmetic import comma_children
from .boundary_carry_clock import powered_chart_carry
from .boundary_chart import (
    BoundaryChart,
    ChartWeight,
    initial_chart,
    validate_chart,
)
from .boundary_quotient import (
    BoundaryState,
    MacroTemplate,
    boundary_state_signature,
    validate_macro_component_read,
)
from .carry_generator import BitsCharge, WorkCharge, charge_carry_work


class BoundaryOccurrenceSource(Protocol):
    """Minimal exact source contract needed by the chart evaluator."""

    @property
    def state(self) -> BoundaryState: ...

    @property
    def exponent(self) -> int: ...

    def value(
        self,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> int: ...


def source_coordinates(
    source: BoundaryOccurrenceSource,
    *,
    charge_work: WorkCharge | None,
    charge_bits: BitsCharge | None,
) -> tuple[int, int, int, int]:
    """Return transient ``value, scale, high, low`` projections."""
    value = source.value(charge_work=charge_work, charge_bits=charge_bits)
    charge_carry_work(charge_work, charge_bits, 1, value, source.state.a, extra_bits=1)
    scaled_value = value + int(source.state.kind == "N")
    scale, remainder = divmod(scaled_value, source.state.a)
    if remainder or scale <= 0:
        raise AssertionError("boundary occurrence has no exact decimal scale")
    return value, scale, value // 100, value % 100


def chart_value(
    chart: BoundaryChart,
    scale: int,
    *,
    charge_work: WorkCharge | None,
    charge_bits: BitsCharge | None,
) -> int:
    """Evaluate one chart at an already materialized decimal scale."""
    if (
        type(chart) is not BoundaryChart
        or type(scale) is not int
        or scale <= 0
        or type(chart.leading) is not int
        or not 1 <= chart.leading <= 9
        or chart.kind not in ("entry", "near")
        or type(chart.delta) is not int
        or chart.delta < 0
        or type(chart.coordinate) is not int
        or chart.coordinate < 0
    ):
        raise ValueError("invalid comma occurrence chart projection")
    charge_carry_work(
        charge_work, charge_bits, 1, chart.leading, chart.coordinate, scale
    )
    return (
        chart.leading * scale + chart.coordinate
        if chart.kind == "entry"
        else (chart.leading + 1) * scale - chart.coordinate
    )


def weighted_chart_value(
    weight: ChartWeight,
    scale: int,
    chart_delta: int,
    *,
    charge_work: WorkCharge | None,
    charge_bits: BitsCharge | None,
) -> int:
    """Evaluate a chart-affine weight at its current absolute scale."""
    if type(weight) is not ChartWeight or type(scale) is not int or scale <= 0:
        raise ValueError("invalid comma chart weight projection")
    if (
        type(chart_delta) is not int
        or chart_delta < 0
        or (weight.scale and weight.exponent_delta != chart_delta)
    ):
        raise ValueError("comma chart weight uses another physical exponent")
    charge_carry_work(
        charge_work,
        charge_bits,
        1,
        weight.scale,
        scale,
        weight.offset,
        weight.denominator,
    )
    numerator = weight.scale * scale + weight.offset
    value, remainder = divmod(numerator, weight.denominator)
    if remainder:
        raise ValueError("comma chart weight is not integral at its occurrence")
    return value


def next_fragment_value(
    value: int,
    source_chart: BoundaryChart,
    entering_digit: int,
    increment: int,
    scale: int,
    *,
    charge_work: WorkCharge | None,
    charge_bits: BitsCharge | None,
) -> tuple[int, int]:
    """Authenticate and apply one literal chart edge, including its C1 carry."""
    exact_source = chart_value(
        source_chart,
        scale,
        charge_work=charge_work,
        charge_bits=charge_bits,
    )
    if exact_source != value or source_chart.kind != "near":
        raise ValueError("literal macro seam has another physical source chart")
    if (-source_chart.coordinate) % 10 != entering_digit:
        raise ValueError("literal macro seam has another physical source phase")
    if type(increment) is not int or increment <= 0:
        raise ValueError("literal macro seam needs a positive increment")
    target = value + increment
    charge_carry_work(charge_work, charge_bits, 1, target, value, extra_bits=1)
    if comma_children(value) != (target,):
        raise ValueError("literal macro seam is not the unique comma child")
    carry = target // 100 - value // 100
    if carry not in (0, 1):
        raise AssertionError("one literal comma edge has an invalid c1 carry")
    return target, carry


def sum_exact(
    left: int,
    right: int,
    charge_work: WorkCharge | None,
    charge_bits: BitsCharge | None,
) -> int:
    charge_carry_work(charge_work, charge_bits, 1, left, right, extra_bits=1)
    return left + right


def macro_prefix_arithmetic(
    source: BoundaryOccurrenceSource,
    template: MacroTemplate,
    component_seal: tuple[object, ...],
    *,
    check_endpoint: bool,
    charge_work: WorkCharge | None,
    charge_bits: BitsCharge | None,
) -> tuple[int, int, int, int, int]:
    """Accumulate exact fixed-sector returns and literal chart seams."""
    value, source_scale, source_high, _source_low = source_coordinates(
        source, charge_work=charge_work, charge_bits=charge_bits
    )
    if boundary_state_signature(template.source) != boundary_state_signature(
        source.state
    ):
        raise ValueError("macro template is bound to another boundary occurrence")

    chart = initial_chart(source.state.kind, source.state.a)
    scale = source_scale
    if (
        chart_value(chart, scale, charge_work=charge_work, charge_bits=charge_bits)
        != value
    ):
        raise AssertionError("source chart does not denote the exact occurrence")
    total_steps = 0
    total_c1 = 0
    for index, (fragment, segment) in enumerate(
        zip(template.sector_fragments, template.chart_segments, strict=True)
    ):
        entry_target_checked = False
        validate_macro_component_read(
            template,
            component_seal,
            "fragment",
            index,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )
        validate_macro_component_read(
            template,
            component_seal,
            "chart_segment",
            index,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )
        if type(fragment.period) is not int or fragment.period < 0:
            raise ValueError("macro fragment has an invalid C1 period")
        if segment.source != chart:
            raise ValueError("macro chart segment is not adjacent to its occurrence")
        validate_chart(source.state.exponent_residue, segment.source)
        validate_chart(source.state.exponent_residue, segment.target)
        if (
            chart_value(chart, scale, charge_work=charge_work, charge_bits=charge_bits)
            != value
        ):
            raise ValueError("macro chart segment is not bound to its exact source")
        steps = weighted_chart_value(
            segment.duration,
            scale,
            chart.delta,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )
        displacement = weighted_chart_value(
            segment.displacement,
            scale,
            chart.delta,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )
        if steps <= 0 or displacement < 0:
            raise ValueError("macro chart segment has an invalid physical action")
        if chart.kind == "entry":
            cycles = fragment.complete_cycles.evaluate_at_scale(
                source_scale, charge_bits=charge_bits
            )
            if (
                fragment.leading != chart.leading
                or fragment.entering_digit != chart.coordinate % 10
                or fragment.period <= 0
                or cycles < 0
                or steps != cycles * fragment.period
                or displacement != cycles * fragment.displacement
            ):
                raise AssertionError(
                    "entry chart action differs from its indexed fragment"
                )
        elif (
            fragment.leading != chart.leading
            or fragment.entering_digit != (-chart.coordinate) % 10
            or fragment.period != 0
            or steps != fragment.literal_steps
            or displacement != fragment.literal_increment
        ):
            raise AssertionError("Near chart action differs from its indexed fragment")
        if segment.target.kind == "entry":
            if fragment.literal_steps != 1 or fragment.period != 0:
                raise ValueError("sector seam does not have a literal edge fragment")
            value, carry = next_fragment_value(
                value,
                segment.source,
                fragment.entering_digit,
                fragment.literal_increment,
                scale,
                charge_work=charge_work,
                charge_bits=charge_bits,
            )
            if steps != 1 or displacement != fragment.literal_increment:
                raise AssertionError("sector seam differs from its chart action")
            total_c1 = sum_exact(total_c1, carry, charge_work, charge_bits)
        elif chart.kind == "entry":
            # The sealed Entry -> Near chart action has a closed C1 count.
            # For a canonical Entry coordinate x<100 and scale divisible by
            # 100, the source high prefix is f*scale/100. At the target Near
            # headroom h, it is (f+1)*scale/100-ceil(h/100). Consume that
            # already-issued segment directly instead of rebuilding its C1
            # recurrence through powered_chart_carry.
            headroom = segment.target.coordinate
            if (
                segment.target.kind != "near"
                or segment.target.leading != chart.leading
                or segment.target.delta != chart.delta
                or type(headroom) is not int
                or not 1 <= headroom <= 540
                or scale % 100 != 0
            ):
                raise ValueError("Entry carry segment has an invalid Near target")
            charge_carry_work(
                charge_work,
                charge_bits,
                1,
                scale,
                headroom,
                value,
                displacement,
                extra_bits=8,
            )
            beta = (headroom + 99) // 100
            carry_count = scale // 100 - beta
            if carry_count < 0:
                raise ValueError("Entry carry count is outside its width")
            target_value = chart_value(
                segment.target,
                scale,
                charge_work=charge_work,
                charge_bits=charge_bits,
            )
            if (
                target_value - value != displacement
                or target_value % 100 != (-headroom) % 100
                or target_value // 100 - value // 100 != carry_count
            ):
                raise AssertionError(
                    "closed Entry carry differs from its exact chart endpoint"
                )
            value = target_value
            entry_target_checked = True
            total_c1 = sum_exact(total_c1, carry_count, charge_work, charge_bits)
        else:
            powered = powered_chart_carry(
                source.state.exponent_residue,
                segment.source,
                source.exponent,
                steps,
                charge_work=charge_work,
                charge_bits=charge_bits,
            )
            if powered.displacement != displacement:
                raise AssertionError(
                    "powered C1 return differs from chart displacement"
                )
            if powered.headroom_weight.scale:
                target_headroom = weighted_chart_value(
                    powered.headroom_weight,
                    scale,
                    chart.delta,
                    charge_work=charge_work,
                    charge_bits=charge_bits,
                )
            else:
                target_headroom = powered.headroom_weight.offset
            if target_headroom != segment.target.coordinate:
                raise AssertionError("powered C1 return differs from target headroom")
            total_c1 = sum_exact(
                total_c1, powered.carry_count, charge_work, charge_bits
            )
            value += displacement
        target_delta = segment.target.delta - segment.source.delta
        if target_delta not in (0, 1):
            raise ValueError("macro chart changed exponent by an invalid seam")
        if target_delta:
            charge_carry_work(charge_work, charge_bits, 1, scale, extra_bits=4)
            scale *= 10
        if not entry_target_checked and (
            chart_value(
                segment.target,
                scale,
                charge_work=charge_work,
                charge_bits=charge_bits,
            )
            != value
        ):
            raise AssertionError("macro chart action differs from its exact target")
        chart = segment.target
        total_steps = sum_exact(total_steps, steps, charge_work, charge_bits)

    expected_steps = template.weight.evaluate_at_scale(
        source_scale, charge_bits=charge_bits
    )
    if total_steps != expected_steps:
        raise AssertionError("powered occurrence prefix differs from its exact weight")
    if check_endpoint:
        expected_endpoint = template.endpoint.evaluate_at_scale(
            source_scale, charge_bits=charge_bits
        )
        if value != expected_endpoint:
            raise AssertionError("occurrence prefix differs from its chart endpoint")

    terminal_chart = template.terminal_chart
    if terminal_chart != chart or terminal_chart.delta != template.exponent_delta:
        raise AssertionError("macro terminal chart differs from its occurrence")
    validate_chart(source.state.exponent_residue, terminal_chart)
    charge_carry_work(charge_work, charge_bits, 1, value, source.exponent)
    if (
        chart_value(
            terminal_chart,
            scale,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )
        != value
    ):
        raise AssertionError("exact terminal integer differs from its chart")
    width_delta = terminal_chart.delta
    if width_delta < 0:
        raise AssertionError("exact terminal exponent differs from chart width")
    if value // 100 != source_high + total_c1:
        raise AssertionError("C1 count does not bind source and terminal high prefixes")
    return value, total_steps, total_c1, width_delta, terminal_chart.leading
