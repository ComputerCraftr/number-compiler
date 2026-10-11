"""Canonical producer for exact completed comma boundary returns.

The indexed public constructor and the compact audit projection share this
single chart walk. The compact publisher discards fragment storage while the
walk is in progress; it does not implement a second recurrence.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from math import gcd
from typing import Literal, Protocol, TypeVar, cast

from number_compiler.arithmetic.fields.consumer_pullback import (
    ONE as _Q_ONE,
)
from number_compiler.arithmetic.fields.consumer_pullback import (
    ZERO as _Q_ZERO,
)
from number_compiler.arithmetic.fields.consumer_pullback import ExactRational
from number_compiler.resources.immutable_signature import (
    ScalarSignature,
    matches_scalar_signature,
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
from number_compiler.sequences.comma.boundary_quotient import (
    _ZERO_WEIGHT,
    AffineWeight,
    BoundaryState,
    CompletedMacroReturn,
    MacroTemplate,
    SectorFragment,
    _affine_component_signature,
    _boundary_state_signature,
    _macro_template_header,
    _sector_fragment_signature,
)

Q = ExactRational


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
    fragment_signatures: list[tuple[object, ...]] = []
    weight_signatures = [_affine_component_signature(_ZERO_WEIGHT)]
    displacement_signatures = [_affine_component_signature(_ZERO_WEIGHT)]
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
        fragment_signature = _sector_fragment_signature(fragment)
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
        next_weight = total_weight.weight()
        next_displacement = total_displacement.weight()
        prefix_weights.append(next_weight)
        prefix_displacements.append(next_displacement)
        fragment_signatures.append(fragment_signature)
        weight_signatures.append(_affine_component_signature(next_weight))
        displacement_signatures.append(_affine_component_signature(next_displacement))
        if charge_bits is not None:
            charge_bits(
                sum(
                    max(1, value.bit_length())
                    for value in (
                        fragment.leading,
                        fragment.entering_digit,
                        fragment.complete_cycles.numerator_scale,
                        fragment.complete_cycles.numerator_offset,
                        fragment.complete_cycles.denominator,
                        fragment.period,
                        fragment.displacement,
                        fragment.maximum_guard,
                        fragment.literal_steps,
                        fragment.literal_increment,
                        next_weight.numerator_scale,
                        next_weight.numerator_offset,
                        next_weight.denominator,
                        next_displacement.numerator_scale,
                        next_displacement.numerator_offset,
                        next_displacement.denominator,
                    )
                )
            )
    if total_weight != weight:
        raise AssertionError("comma indexed macro weight differs from construction")
    source_value = _Affine(
        _integer_rational(source.a),
        _integer_rational(-1 if source.kind == "N" else 0),
    )
    if source_value.plus(total_displacement) != endpoint:
        raise AssertionError("comma indexed macro endpoint differs from construction")
    template = MacroTemplate(
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
    seal = (
        _macro_template_header(template),
        tuple(fragment_signatures),
        tuple(weight_signatures),
        tuple(displacement_signatures),
    )
    object.__setattr__(template, "_component_seal", seal)
    return template


_MacroResult_co = TypeVar("_MacroResult_co", covariant=True)


class _MacroPublisher(Protocol[_MacroResult_co]):
    retain_fragments: bool

    def publish(
        self,
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
    ) -> _MacroResult_co: ...


def _completed_return_header(
    completed: CompletedMacroReturn,
) -> tuple[object, ...]:
    if type(completed) is not CompletedMacroReturn:
        raise ValueError("comma completed return publication was altered")
    source = _boundary_state_signature(completed.source)
    children = completed.ordered_children
    outcome = completed.outcome
    destination = completed.destination_a
    if (
        type(outcome) is not str
        or outcome not in ("fork", "landmine")
        or type(completed.exponent_delta) is not int
        or completed.exponent_delta < 0
        or (destination is not None and type(destination) is not int)
        or type(children) is not tuple
    ):
        raise ValueError("comma completed return has a malformed header")
    child_signatures: list[object] = []
    child_fields: list[tuple[str, int]] = []
    for child in children:
        signature = _boundary_state_signature(child)
        child_signatures.extend((id(child), *signature))
        child_fields.append((signature[0], signature[1]))
    if outcome == "landmine":
        if destination is not None or children:
            raise ValueError("comma landmine return carries fork payload")
    elif (
        destination is None
        or not 2 <= destination <= 9
        or len(children) != 2
        or tuple(fields[0] for fields in child_fields) != ("N", "Z")
        or any(fields[1] != destination for fields in child_fields)
    ):
        raise ValueError("comma fork return has malformed ordered children")
    return (
        id(completed),
        id(completed.source),
        *source,
        outcome,
        completed.exponent_delta,
        destination,
        *_affine_component_signature(completed.weight),
        *_affine_component_signature(completed.endpoint),
        id(children),
        len(children),
        *child_signatures,
    )


def _completed_macro_return_component_seal(
    completed: CompletedMacroReturn,
) -> tuple[object, ...]:
    seal = completed._component_seal
    if type(seal) is not tuple or len(seal) != 1:
        raise ValueError("comma completed return has no component seal")
    header = _completed_return_header(completed)
    expected = seal[0]
    if (
        type(expected) is not tuple
        or len(expected) != len(header)
        or any(type(value) not in (str, int, type(None)) for value in expected)
        or not matches_scalar_signature(header, cast(ScalarSignature, expected))
    ):
        raise ValueError("comma completed return was altered (snapshot mismatch)")
    return seal


def _publish_completed_return(
    source: BoundaryState,
    outcome: Literal["fork", "landmine"],
    delta: int,
    destination_a: int | None,
    weight: _Affine,
    endpoint: _Affine,
    children: tuple[BoundaryState, ...],
) -> CompletedMacroReturn:
    completed = CompletedMacroReturn(
        source,
        outcome,
        delta,
        destination_a,
        weight.weight(),
        endpoint.weight(),
        children,
    )
    object.__setattr__(
        completed,
        "_component_seal",
        (_completed_return_header(completed),),
    )
    return completed


class _IndexedMacroPublisher:
    retain_fragments = True

    def publish(
        self,
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
        return _indexed_macro(
            source,
            outcome,
            delta,
            destination_a,
            weight,
            endpoint,
            children,
            fragments,
            charge,
            charge_bits,
        )


class _CompletedReturnPublisher:
    retain_fragments = False

    def publish(
        self,
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
    ) -> CompletedMacroReturn:
        if fragments:
            raise AssertionError("compact macro publication retained path fragments")
        return _publish_completed_return(
            source, outcome, delta, destination_a, weight, endpoint, children
        )


def _construct_macro_with_publisher(
    source: BoundaryState,
    publisher: _MacroPublisher[_MacroResult_co],
    *,
    charge: Callable[[int], None] | None = None,
    charge_bits: Callable[[int], None] | None = None,
    grouped_near: bool = False,
) -> _MacroResult_co:
    """Accumulate exact weights over the bounded Entry/Near chart machine.

    Entry consumes complete interior cycles; Near consumes bounded seam
    edges and reports all terminal alternatives. The optional grouped Near
    classifier is an exact validation view, not the default executor: its
    present catalog construction costs more than the bounded edge scan.
    No representative endpoint or sampled branch is constructed. The global
    winning-cycle and literal lifting proofs remain admission obligations.
    """
    if type(publisher.retain_fragments) is not bool:
        raise TypeError("comma macro publisher has an invalid storage mode")
    weight = _constant(0)
    displacement = _ZERO_AFFINE
    fragments: list[SectorFragment] = []
    relative_scale = 1
    previous_delta = 0
    near_run: tuple[int, int, int, int] | None = None

    def flush_near() -> None:
        nonlocal near_run, weight, displacement
        if near_run is not None:
            leading, digit, steps, increment = near_run
            weight = weight.plus(_constant(steps))
            displacement = displacement.plus(_constant(increment))
            if publisher.retain_fragments:
                fragments.append(
                    SectorFragment(
                        leading,
                        digit,
                        AffineWeight(0, 0, 1),
                        0,
                        0,
                        0,
                        steps,
                        increment,
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
            endpoint_displacement = _Affine(
                Q(source.a), Q(-1 if source.kind == "N" else 0)
            ).plus(displacement)
            if endpoint_displacement != endpoint:
                raise AssertionError("comma macro endpoint differs from construction")
            return publisher.publish(
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
            displacement = displacement.plus(count.times(transfer.displacement))
            if publisher.retain_fragments:
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
            displacement = displacement.plus(_constant(move.literal_increment))
            if publisher.retain_fragments:
                fragments.append(
                    SectorFragment(
                        f,
                        digit,
                        AffineWeight(0, 0, 1),
                        0,
                        0,
                        0,
                        1,
                        move.literal_increment,
                    )
                )
    raise AssertionError("comma chart returned without a terminal outcome")


def construct_macro(
    source: BoundaryState,
    *,
    charge: Callable[[int], None] | None = None,
    charge_bits: Callable[[int], None] | None = None,
    grouped_near: bool = False,
) -> MacroTemplate:
    """Accumulate the indexed public macro from the canonical chart walk."""
    return _construct_macro_with_publisher(
        source,
        _IndexedMacroPublisher(),
        charge=charge,
        charge_bits=charge_bits,
        grouped_near=grouped_near,
    )


def construct_completed_return(
    source: BoundaryState,
    *,
    charge: Callable[[int], None] | None = None,
    charge_bits: Callable[[int], None] | None = None,
    grouped_near: bool = False,
) -> CompletedMacroReturn:
    """Build a sealed terminal return without fragment/prefix indexing."""
    return _construct_macro_with_publisher(
        source,
        _CompletedReturnPublisher(),
        charge=charge,
        charge_bits=charge_bits,
        grouped_near=grouped_near,
    )


__all__ = [
    "_completed_macro_return_component_seal",
    "construct_completed_return",
    "construct_macro",
]
