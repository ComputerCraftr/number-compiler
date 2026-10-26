"""Exact symbolic comma transitions between decimal fork boundaries.

This is a constructor for *one* boundary macro.  It does not decide which
fork child has an infinite continuation.  The finite quotient and its
lifting theorem are separate admission obligations.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, field
from math import gcd
from typing import Literal, cast

from number_compiler.arithmetic.contracts.input_validation import is_exact_object_tuple
from number_compiler.resources.immutable_signature import (
    ScalarSignature,
    matches_scalar_signature,
)
from number_compiler.sequences.comma.arithmetic import phase_prefix_displacement
from number_compiler.sequences.comma.boundary_chart import (
    PERIOD,
    BoundaryChart,
    ChartSegment,
    ChartWeight,
    validate_chart,
)

_TEMPLATE_PUBLICATION_ERROR = (
    "comma boundary template publication was altered (snapshot mismatch)"
)


@dataclass(frozen=True, slots=True)
class BoundaryState:
    kind: Literal["N", "Z"]
    a: int
    exponent_residue: int

    def __post_init__(self) -> None:
        if (
            type(self.kind) is not str
            or self.kind not in ("N", "Z")
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


def boundary_source_index(source: BoundaryState) -> int:
    if (
        type(source) is not BoundaryState
        or type(source.kind) is not str
        or source.kind not in ("N", "Z")
        or type(source.a) is not int
        or not 2 <= source.a <= 9
        or type(source.exponent_residue) is not int
        or not 0 <= source.exponent_residue < PERIOD
    ):
        raise ValueError("malformed comma boundary source state")
    kind_offset = 0 if source.kind == "N" else 8 * PERIOD
    return kind_offset + (source.a - 2) * PERIOD + source.exponent_residue


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


def boundary_state_signature(state: BoundaryState) -> tuple[str, int, int]:
    """Return exact canonical state scalars without invoking custom equality."""
    if type(state) is not BoundaryState:
        raise ValueError("comma boundary state changed after construction")
    kind = state.kind
    a = state.a
    residue = state.exponent_residue
    if (
        type(kind) is not str
        or kind not in ("N", "Z")
        or type(a) is not int
        or not 2 <= a <= 9
        or type(residue) is not int
        or not 0 <= residue < PERIOD
    ):
        raise ValueError("comma boundary state has noncanonical scalar fields")
    return kind, a, residue


def affine_weight_signature(weight: AffineWeight) -> tuple[int, int, int]:
    """Return exact affine scalars from the value type's owning module."""
    if type(weight) is not AffineWeight:
        raise ValueError("macro affine descriptor changed after construction")
    scale = weight.numerator_scale
    offset = weight.numerator_offset
    denominator = weight.denominator
    if (
        type(scale) is not int
        or type(offset) is not int
        or type(denominator) is not int
        or denominator <= 0
    ):
        raise ValueError("macro affine descriptor has noncanonical scalars")
    return scale, offset, denominator


ZERO_AFFINE_WEIGHT = AffineWeight(0, 0, 1)


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
    chart_segments: tuple[ChartSegment, ...]
    terminal_chart: BoundaryChart
    _component_seal: tuple[object, ...] | None = field(
        init=False,
        default=None,
        repr=False,
        compare=False,
        hash=False,
    )

    def owns_component_seal(self, expected: object) -> bool:
        """Check seal identity without exposing the issuer-owned tuple."""
        return type(self._component_seal) is tuple and self._component_seal is expected

    def component_seal_snapshot(
        self,
        *,
        charge_work: Callable[[int], None] | None = None,
        charge_bits: Callable[[int], None] | None = None,
    ) -> tuple[object, ...]:
        """Return the immutable component facts after authenticating their owner."""
        seal = self._component_seal
        if seal is None:
            raise ValueError("comma boundary template has no component seal")
        validate_macro_component_header(
            self,
            seal,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )
        return seal

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
        seal = self._component_seal
        if seal is not None:
            if charge is not None:
                charge(1)
            validate_macro_component_header(self, seal, charge_bits=charge_bits)

        def read_component(kind: str, index: int, *, precharged: bool = False) -> None:
            if validate_read is not None:
                validate_read(kind, index)
            elif charge is not None and not precharged:
                charge(1)
            if seal is not None:
                validate_macro_component_read(
                    self,
                    seal,
                    kind,
                    index,
                    charge_bits=charge_bits,
                )

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
            if validate_read is not None or seal is not None:
                read_component("weight", middle, precharged=True)
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
        if validate_read is not None or seal is not None:
            if validate_read is None and charge is not None:
                charge(1)
            precharged = validate_read is None
            read_component("fragment", fragment_index, precharged=precharged)
            read_component("weight", fragment_index, precharged=precharged)
            read_component("displacement", fragment_index, precharged=precharged)
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


def affine_component_signature(weight: AffineWeight) -> tuple[int, int, int, int]:
    return (id(weight), *affine_weight_signature(weight))


def sector_fragment_signature(fragment: SectorFragment) -> tuple[int, ...]:
    if type(fragment) is not SectorFragment:
        raise ValueError("macro sector fragment changed after construction")
    scalars = (
        fragment.leading,
        fragment.entering_digit,
        fragment.period,
        fragment.displacement,
        fragment.maximum_guard,
        fragment.literal_steps,
        fragment.literal_increment,
    )
    if any(type(value) is not int for value in scalars):
        raise ValueError("macro sector fragment has noncanonical scalar fields")
    return (
        id(fragment),
        fragment.leading,
        fragment.entering_digit,
        *affine_component_signature(fragment.complete_cycles),
        fragment.period,
        fragment.displacement,
        fragment.maximum_guard,
        fragment.literal_steps,
        fragment.literal_increment,
    )


def _chart_signature(chart: BoundaryChart) -> tuple[str, int, int, int]:
    if (
        type(chart) is not BoundaryChart
        or type(chart.kind) is not str
        or chart.kind not in ("entry", "near")
    ):
        raise ValueError("macro chart has a malformed kind")
    if (
        type(chart.leading) is not int
        or not 1 <= chart.leading <= 9
        or type(chart.delta) is not int
        or chart.delta < 0
        or type(chart.coordinate) is not int
        or chart.coordinate < 0
    ):
        raise ValueError("macro chart has noncanonical coordinates")
    return chart.kind, chart.leading, chart.delta, chart.coordinate


def _chart_weight_signature(weight: ChartWeight) -> tuple[int, int, int, int]:
    if type(weight) is not ChartWeight:
        raise ValueError("macro chart segment has a malformed weight")
    fields = (weight.scale, weight.exponent_delta, weight.offset, weight.denominator)
    if (
        any(type(value) is not int for value in fields)
        or weight.scale < 0
        or weight.exponent_delta < 0
        or weight.denominator <= 0
    ):
        raise ValueError("macro chart segment has noncanonical weight fields")
    return fields


def chart_segment_signature(segment: ChartSegment) -> tuple[object, ...]:
    """Snapshot one exact chart edge aligned with a stored macro fragment."""
    if type(segment) is not ChartSegment:
        raise ValueError("macro chart segment changed after construction")

    return (
        id(segment),
        id(segment.source),
        *_chart_signature(segment.source),
        id(segment.target),
        *_chart_signature(segment.target),
        id(segment.duration),
        *_chart_weight_signature(segment.duration),
        id(segment.displacement),
        *_chart_weight_signature(segment.displacement),
    )


def macro_template_header(template: MacroTemplate) -> tuple[object, ...]:
    if type(template) is not MacroTemplate:
        raise ValueError(_TEMPLATE_PUBLICATION_ERROR)
    source = boundary_state_signature(template.source)
    children = template.ordered_children
    fragments = template.sector_fragments
    weights = template.prefix_weights
    displacements = template.prefix_displacements
    chart_segments = template.chart_segments
    terminal_chart = template.terminal_chart
    if (
        type(template.outcome) is not str
        or template.outcome not in ("fork", "landmine")
        or type(template.exponent_delta) is not int
        or template.exponent_delta < 0
        or (
            template.destination_a is not None
            and type(template.destination_a) is not int
        )
        or type(children) is not tuple
        or type(fragments) is not tuple
        or type(weights) is not tuple
        or type(displacements) is not tuple
        or type(chart_segments) is not tuple
        or type(terminal_chart) is not BoundaryChart
        or len(weights) != len(fragments) + 1
        or len(displacements) != len(fragments) + 1
        or len(chart_segments) != len(fragments)
    ):
        raise ValueError(_TEMPLATE_PUBLICATION_ERROR)
    if (template.outcome == "fork" and len(children) != 2) or (
        template.outcome == "landmine" and children
    ):
        raise ValueError(_TEMPLATE_PUBLICATION_ERROR)
    expected_child_residue = (
        template.source.exponent_residue + template.exponent_delta
    ) % PERIOD
    if any(child.exponent_residue != expected_child_residue for child in children):
        raise ValueError(_TEMPLATE_PUBLICATION_ERROR)
    child_signatures: list[object] = []
    for child in children:
        child_signatures.extend((id(child), *boundary_state_signature(child)))
    if terminal_chart.kind != "near" or terminal_chart.delta != template.exponent_delta:
        raise ValueError(_TEMPLATE_PUBLICATION_ERROR)
    # The issuer authenticates the terminal classification once when it
    # creates the template. Header snapshots validate the sealed descriptor,
    # but do not replay the terminal chart transition on every warm read.
    validate_chart(template.source.exponent_residue, terminal_chart)
    return (
        id(template),
        id(template.source),
        *source,
        template.outcome,
        template.exponent_delta,
        template.destination_a,
        *affine_component_signature(template.weight),
        *affine_component_signature(template.endpoint),
        id(children),
        len(children),
        *child_signatures,
        id(fragments),
        id(weights),
        id(displacements),
        id(chart_segments),
        id(terminal_chart),
        *_chart_signature(terminal_chart),
    )


def macro_template_retained_components(template: MacroTemplate) -> tuple[object, ...]:
    """Enumerate one template's owned object graph once by identity.

    ChartSegment objects are shallow records: their source/target charts and
    duration/displacement weights are separately retained nodes. Several
    adjacent segments may share chart objects, and the last target may alias
    ``terminal_chart``; identity de-duplication keeps the ledger from charging
    those shared nodes twice while preserving deterministic publication order.
    """
    if (
        type(template) is not MacroTemplate
        or type(template.sector_fragments) is not tuple
        or type(template.prefix_weights) is not tuple
        or type(template.prefix_displacements) is not tuple
        or type(template.chart_segments) is not tuple
        or type(template.terminal_chart) is not BoundaryChart
    ):
        raise ValueError(_TEMPLATE_PUBLICATION_ERROR)

    if (
        any(
            type(fragment) is not SectorFragment
            for fragment in template.sector_fragments
        )
        or any(type(weight) is not AffineWeight for weight in template.prefix_weights)
        or any(
            type(weight) is not AffineWeight for weight in template.prefix_displacements
        )
    ):
        raise ValueError(_TEMPLATE_PUBLICATION_ERROR)

    candidates: list[object] = [
        template,
        *template.sector_fragments,
        *template.prefix_weights,
        *template.prefix_displacements,
    ]
    for segment in template.chart_segments:
        if (
            type(segment) is not ChartSegment
            or type(segment.source) is not BoundaryChart
            or type(segment.target) is not BoundaryChart
            or type(segment.duration) is not ChartWeight
            or type(segment.displacement) is not ChartWeight
        ):
            raise ValueError(_TEMPLATE_PUBLICATION_ERROR)
        candidates.extend(
            (
                segment,
                segment.source,
                segment.target,
                segment.duration,
                segment.displacement,
            )
        )
    candidates.append(template.terminal_chart)

    seen: set[int] = set()
    components: list[object] = []
    for candidate in candidates:
        identity = id(candidate)
        if identity not in seen:
            seen.add(identity)
            components.append(candidate)
    return tuple(components)


def validate_macro_component_header(
    template: MacroTemplate,
    seal: tuple[object, ...],
    *,
    charge_work: Callable[[int], None] | None = None,
    charge_bits: Callable[[int], None] | None = None,
) -> None:
    if type(seal) is not tuple or len(seal) != 5:
        raise ValueError(_TEMPLATE_PUBLICATION_ERROR)
    if type(template) is not MacroTemplate:
        raise ValueError(_TEMPLATE_PUBLICATION_ERROR)
    if (
        type(template.sector_fragments) is not tuple
        or type(template.prefix_weights) is not tuple
        or type(template.prefix_displacements) is not tuple
        or type(template.chart_segments) is not tuple
    ):
        raise ValueError(_TEMPLATE_PUBLICATION_ERROR)
    if charge_work is not None:
        charge_work(
            1
            + 2 * len(template.sector_fragments)
            + 2 * len(template.chart_segments)
            + len(template.prefix_weights)
            + len(template.prefix_displacements)
        )
    current_header = macro_template_header(template)
    expected_header = seal[0]
    if (
        not is_exact_object_tuple(expected_header)
        or len(expected_header) != len(current_header)
        or any(type(value) not in (str, int, type(None)) for value in expected_header)
    ):
        raise ValueError(_TEMPLATE_PUBLICATION_ERROR)
    if charge_bits is not None:
        charge_bits(
            _component_signature_bits(current_header)
            + _component_signature_bits(expected_header)
        )
    if any(
        not is_exact_object_tuple(rows) for rows in seal[1:]
    ) or not matches_scalar_signature(
        current_header, cast(ScalarSignature, expected_header)
    ):
        raise ValueError(_TEMPLATE_PUBLICATION_ERROR)
    fragment_rows = cast(tuple[object, ...], seal[1])
    weight_rows = cast(tuple[object, ...], seal[2])
    displacement_rows = cast(tuple[object, ...], seal[3])
    chart_rows = cast(tuple[object, ...], seal[4])
    if (
        len(fragment_rows) != len(template.sector_fragments)
        or len(weight_rows) != len(template.prefix_weights)
        or len(displacement_rows) != len(template.prefix_displacements)
        or len(chart_rows) != len(template.chart_segments)
    ):
        raise ValueError(_TEMPLATE_PUBLICATION_ERROR)


def validate_macro_component_read(
    template: MacroTemplate,
    seal: tuple[object, ...],
    kind: str,
    index: int,
    *,
    charge_work: Callable[[int], None] | None = None,
    charge_bits: Callable[[int], None] | None = None,
) -> None:
    if type(index) is not int or index < 0:
        raise ValueError("comma boundary component index is invalid")
    if kind == "fragment":
        rows = seal[1]
    elif kind == "weight":
        rows = seal[2]
    elif kind == "displacement":
        rows = seal[3]
    elif kind == "chart_segment":
        rows = seal[4]
    else:
        raise ValueError("unknown comma boundary component")
    if not is_exact_object_tuple(rows):
        raise ValueError("comma boundary component seal is malformed")
    if charge_work is not None:
        charge_work(1)
    sealed_rows = rows
    if index >= len(sealed_rows):
        raise ValueError("comma boundary component index is outside its seal")
    current: ScalarSignature
    if kind == "fragment":
        fragments = template.sector_fragments
        if index >= len(fragments):
            raise ValueError("comma boundary component index is outside its seal")
        current = sector_fragment_signature(fragments[index])
    elif kind == "weight":
        weights = template.prefix_weights
        if index >= len(weights):
            raise ValueError("comma boundary component index is outside its seal")
        current = affine_component_signature(weights[index])
    elif kind == "displacement":
        displacements = template.prefix_displacements
        if index >= len(displacements):
            raise ValueError("comma boundary component index is outside its seal")
        current = affine_component_signature(displacements[index])
    else:
        segments = template.chart_segments
        if index >= len(segments):
            raise ValueError("comma boundary component index is outside its seal")
        current = cast(ScalarSignature, chart_segment_signature(segments[index]))
    expected = sealed_rows[index]
    if (
        not is_exact_object_tuple(expected)
        or len(expected) != len(current)
        or any(type(value) not in (str, int, type(None)) for value in expected)
    ):
        raise ValueError(_TEMPLATE_PUBLICATION_ERROR)
    if charge_bits is not None:
        charge_bits(
            _component_signature_bits(current) + _component_signature_bits(expected)
        )
    if not matches_scalar_signature(current, cast(ScalarSignature, expected)):
        raise ValueError(_TEMPLATE_PUBLICATION_ERROR)


def _component_signature_bits(value: object) -> int:
    stack: list[object] = [value]
    bits = 0
    while stack:
        item = stack.pop()
        if type(item) is int:
            bits += max(1, item.bit_length())
        elif is_exact_object_tuple(item):
            stack.extend(item)
        elif type(item) is str or item is None:
            continue
        else:
            raise ValueError("comma boundary component signature is malformed")
    return bits


def macro_template_component_seal(
    template: MacroTemplate,
    *,
    charge_work: Callable[[int], None] | None = None,
    charge_bits: Callable[[int], None] | None = None,
) -> tuple[object, ...]:
    return template.component_seal_snapshot(
        charge_work=charge_work,
        charge_bits=charge_bits,
    )


@dataclass(frozen=True, slots=True)
class CompletedMacroReturn:
    """Sealed terminal header without fragment or prefix-index storage."""

    source: BoundaryState
    outcome: Literal["fork", "landmine"]
    exponent_delta: int
    destination_a: int | None
    weight: AffineWeight
    endpoint: AffineWeight
    ordered_children: tuple[BoundaryState, ...]
    _component_seal: tuple[object, ...] | None = field(
        init=False,
        default=None,
        repr=False,
        compare=False,
        hash=False,
    )

    def validate_component_header(self, header: ScalarSignature) -> None:
        """Validate a compact return against its owner-held sealed header."""
        seal = self._component_seal
        if type(seal) is not tuple or len(seal) != 1:
            raise ValueError("comma completed return has no component seal")
        expected = seal[0]
        if (
            not is_exact_object_tuple(expected)
            or len(expected) != len(header)
            or any(type(value) not in (str, int, type(None)) for value in expected)
            or not matches_scalar_signature(header, cast(ScalarSignature, expected))
        ):
            raise ValueError("comma completed return was altered (snapshot mismatch)")


def construct_macro(
    source: BoundaryState,
    *,
    charge: Callable[[int], None] | None = None,
    charge_bits: Callable[[int], None] | None = None,
    grouped_near: bool = False,
) -> MacroTemplate:
    """Build the indexed public macro through the canonical chart producer."""
    from number_compiler.sequences.comma.boundary_return import construct_macro as build

    return build(
        source, charge=charge, charge_bits=charge_bits, grouped_near=grouped_near
    )


def construct_completed_return(
    source: BoundaryState,
    *,
    charge: Callable[[int], None] | None = None,
    charge_bits: Callable[[int], None] | None = None,
    grouped_near: bool = False,
) -> CompletedMacroReturn:
    """Build a compact sealed return without constructing indexed prefixes."""
    from number_compiler.sequences.comma.boundary_return import (
        construct_completed_return as build,
    )

    return build(
        source, charge=charge, charge_bits=charge_bits, grouped_near=grouped_near
    )


__all__ = [
    "PERIOD",
    "AffineWeight",
    "BoundaryState",
    "CompletedMacroReturn",
    "MacroTemplate",
    "SectorFragment",
    "ZERO_AFFINE_WEIGHT",
    "affine_component_signature",
    "affine_weight_signature",
    "construct_completed_return",
    "construct_macro",
    "macro_template_header",
    "sector_fragment_signature",
]
