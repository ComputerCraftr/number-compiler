"""Exact physical occurrence bindings for chart-derived comma prefixes.

This development layer binds the finite ``BoundaryState`` chart teacher to one
exact exponent and its literal value.  It powers the existing fixed-sector C1
returns across the teacher's fragments, then keeps the terminal and its
ordered fork children distinct.  It supplies no native future selector and
does not authenticate ``construct_macro`` as a native branch constructor.

Only ``(BoundaryState, physical exponent)`` is stored as a boundary
occurrence.  Its value, C1 phase, high prefix, and low suffix are derived from
that exact pair.  A prefix return stores its validated terminal integer and
additive C1/width data; terminal phase and decimal coordinates are projections
of that integer.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

from .arithmetic import comma_children, cycle_transfer, decimal_sector
from .boundary_chart import PERIOD
from .boundary_quotient import AffineWeight, BoundaryState, MacroTemplate
from .carry_generator import (
    BitsCharge,
    BoundC1Return,
    C1Phase,
    WorkCharge,
    source_bound_return,
)
from .weighted_return import WeightedBoundaryAction

_PREFIX_RETURN_SEAL = object()


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


@dataclass(frozen=True, slots=True)
class BoundaryOccurrence:
    """One N/Z boundary at an exact physical exponent.

    The literal integer is never accepted as separate caller authority.  It is
    reconstructed from the boundary constructor and exact exponent when
    requested.  Exponents below five are outside this boundary chart API.
    """

    state: BoundaryState
    exponent: int

    def __post_init__(self) -> None:
        if type(self.state) is not BoundaryState:
            raise TypeError("comma occurrence requires an exact boundary state")
        if (
            type(self.exponent) is not int
            or self.exponent < 5
            or self.exponent % PERIOD != self.state.exponent_residue
        ):
            raise ValueError("physical exponent does not represent boundary state")

    def value(
        self,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> int:
        """Derive the exact literal value from the authenticated occurrence."""
        _charge(charge_work, charge_bits, 1, self.exponent)
        return self.state.value(self.exponent, charge_bits=charge_bits)

    def c1_phase(
        self,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> C1Phase:
        _charge(charge_work, charge_bits, 1, self.state.a, self.exponent)
        sector = self.state.a - int(self.state.kind == "N")
        suffix = 99 if self.state.kind == "N" else 0
        return C1Phase.from_suffix(sector, suffix)

    def high_prefix(
        self,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> int:
        scale_exponent = self.exponent - 2
        _charge(
            charge_work,
            charge_bits,
            1,
            self.state.a,
            scale_exponent,
            extra_bits=4 * scale_exponent + 2,
        )
        scale = int(pow(10, scale_exponent))
        return self.state.a * scale - int(self.state.kind == "N")

    def low_suffix(
        self,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> int:
        _charge(charge_work, charge_bits, 1, self.state.a)
        return 99 if self.state.kind == "N" else 0


def _source_coordinates(
    source: BoundaryOccurrence,
    *,
    charge_work: WorkCharge | None,
    charge_bits: BitsCharge | None,
) -> tuple[int, int, int, int, C1Phase]:
    """Return transient ``value, scale, high, low, phase`` projections."""
    value = source.value(charge_work=charge_work, charge_bits=charge_bits)
    _charge(charge_work, charge_bits, 1, value, source.state.a, extra_bits=1)
    scaled_value = value + int(source.state.kind == "N")
    scale, remainder = divmod(scaled_value, source.state.a)
    if remainder or scale <= 0:
        raise AssertionError("boundary occurrence has no exact decimal scale")
    sector = source.state.a - int(source.state.kind == "N")
    phase = C1Phase.from_suffix(sector, value % 100)
    return value, scale, value // 100, value % 100, phase


def _next_fragment_value(
    value: int,
    fragment_leading: int,
    entering_digit: int,
    increment: int,
    *,
    charge_work: WorkCharge | None,
    charge_bits: BitsCharge | None,
) -> tuple[int, int]:
    """Authenticate and apply one literal chart edge, including its c1 carry."""
    _charge(charge_work, charge_bits, 1, value, increment, extra_bits=1)
    sector = decimal_sector(value)
    if sector.leading != fragment_leading or sector.digit != entering_digit:
        raise ValueError("literal macro seam has another physical source phase")
    if type(increment) is not int or increment <= 0:
        raise ValueError("literal macro seam needs a positive increment")
    target = value + increment
    _charge(charge_work, charge_bits, 1, target, value, extra_bits=1)
    if comma_children(value) != (target,):
        raise ValueError("literal macro seam is not the unique comma child")
    carry = target // 100 - value // 100
    if carry not in (0, 1):
        raise AssertionError("one literal comma edge has an invalid c1 carry")
    return target, carry


def _macro_prefix_arithmetic(
    source: BoundaryOccurrence,
    template: MacroTemplate,
    *,
    check_endpoint: bool,
    charge_work: WorkCharge | None,
    charge_bits: BitsCharge | None,
) -> tuple[int, int, int, int, int]:
    """Accumulate exact fixed-sector returns and literal chart seams."""
    value, scale, source_high, _source_low, _source_phase = _source_coordinates(
        source, charge_work=charge_work, charge_bits=charge_bits
    )
    if template.source != source.state:
        raise ValueError("macro template is bound to another boundary occurrence")

    total_steps = 0
    total_c1 = 0
    for fragment in template.sector_fragments:
        if type(fragment.period) is not int or fragment.period < 0:
            raise ValueError("macro fragment has an invalid C1 period")
        _charge(charge_work, charge_bits, 1, value, scale)
        physical_sector = decimal_sector(value)
        if (
            physical_sector.leading != fragment.leading
            or physical_sector.digit != fragment.entering_digit
        ):
            raise ValueError("macro fragment is not bound to its physical phase")

        phase = C1Phase.from_suffix(fragment.leading, value % 100)
        if fragment.period:
            transfer = cycle_transfer(fragment.leading, fragment.entering_digit)
            if (
                fragment.period != transfer.period
                or fragment.displacement != transfer.displacement
                or fragment.maximum_guard != transfer.maximum_guard
            ):
                raise AssertionError("macro cycle fragment differs from its owner")
            cycles = fragment.complete_cycles.evaluate_at_scale(
                scale, charge_bits=charge_bits
            )
            if cycles < 0:
                raise AssertionError("macro cycle fragment has negative duration")
            _charge(
                charge_work,
                charge_bits,
                1,
                cycles,
                transfer.period,
                extra_bits=1,
            )
            steps = cycles * transfer.period
            bound = source_bound_return(
                value,
                phase,
                steps,
                charge_work=charge_work,
                charge_bits=charge_bits,
            )
            displacement = bound.action.displacement(
                charge_work=charge_work,
                charge_bits=charge_bits,
            )
            _charge(
                charge_work,
                charge_bits,
                1,
                cycles,
                transfer.displacement,
                extra_bits=1,
            )
            if displacement != cycles * transfer.displacement:
                raise AssertionError("powered C1 return changed its cycle displacement")
            value = _bound_target_value(bound, charge_work, charge_bits)
            total_c1 = _sum_exact(total_c1, bound.count, charge_work, charge_bits)
        elif fragment.literal_steps > 1:
            if fragment.literal_increment < 0:
                raise AssertionError("literal macro fragment has negative displacement")
            bound = source_bound_return(
                value,
                phase,
                fragment.literal_steps,
                charge_work=charge_work,
                charge_bits=charge_bits,
            )
            displacement = bound.action.displacement(
                charge_work=charge_work,
                charge_bits=charge_bits,
            )
            if displacement != fragment.literal_increment:
                raise AssertionError("powered Near fragment changed its displacement")
            value = _bound_target_value(bound, charge_work, charge_bits)
            total_c1 = _sum_exact(total_c1, bound.count, charge_work, charge_bits)
            steps = fragment.literal_steps
        elif fragment.literal_steps == 1:
            value, carry = _next_fragment_value(
                value,
                fragment.leading,
                fragment.entering_digit,
                fragment.literal_increment,
                charge_work=charge_work,
                charge_bits=charge_bits,
            )
            total_c1 = _sum_exact(total_c1, carry, charge_work, charge_bits)
            steps = 1
        else:
            raise AssertionError("macro fragment has no physical transitions")
        total_steps = _sum_exact(total_steps, steps, charge_work, charge_bits)

    expected_steps = template.weight.evaluate_at_scale(scale, charge_bits=charge_bits)
    if total_steps != expected_steps:
        raise AssertionError("powered occurrence prefix differs from its exact weight")
    if check_endpoint:
        expected_endpoint = template.endpoint.evaluate_at_scale(
            scale, charge_bits=charge_bits
        )
        if value != expected_endpoint:
            raise AssertionError("occurrence prefix differs from its chart endpoint")

    _charge(charge_work, charge_bits, 1, value, source.exponent)
    terminal_sector = decimal_sector(value)
    width_delta = terminal_sector.exponent - source.exponent
    if width_delta < 0 or width_delta != template.exponent_delta:
        raise AssertionError("exact terminal exponent differs from chart width")
    if value // 100 != source_high + total_c1:
        raise AssertionError("C1 count does not bind source and terminal high prefixes")
    return value, total_steps, total_c1, width_delta, terminal_sector.leading


def _bound_target_value(
    result: BoundC1Return,
    charge_work: WorkCharge | None,
    charge_bits: BitsCharge | None,
) -> int:
    high = result.target_high
    low = result.target.suffix
    _charge(charge_work, charge_bits, 1, high, low, extra_bits=7)
    return 100 * high + low


def _sum_exact(
    left: int,
    right: int,
    charge_work: WorkCharge | None,
    charge_bits: BitsCharge | None,
) -> int:
    _charge(charge_work, charge_bits, 1, left, right, extra_bits=1)
    return left + right


def _prefix_signature(
    source: BoundaryOccurrence,
    template: MacroTemplate,
    terminal_value: int,
    transition_count: int,
    c1_count: int,
    width_delta: int,
    terminal_leading: int,
) -> tuple[object, ...]:
    return (
        _template_signature(template),
        source.state.kind,
        source.state.a,
        source.state.exponent_residue,
        source.exponent,
        terminal_value,
        transition_count,
        c1_count,
        width_delta,
        terminal_leading,
    )


def _template_signature(template: MacroTemplate) -> tuple[object, ...]:
    """Snapshot only the shallow macro fields consumed after publication."""
    if type(template.source) is not BoundaryState:
        raise ValueError("macro template source changed after construction")
    if type(template.weight) is not AffineWeight:
        raise ValueError("macro template weight changed after construction")
    children: list[tuple[str, int, int]] = []
    for child in template.ordered_children:
        if type(child) is not BoundaryState:
            raise ValueError("macro template child changed after construction")
        children.append((child.kind, child.a, child.exponent_residue))
    weight = template.weight
    return (
        id(template),
        (template.source.kind, template.source.a, template.source.exponent_residue),
        template.outcome,
        template.exponent_delta,
        template.destination_a,
        tuple(children),
        (
            weight.numerator_scale,
            weight.numerator_offset,
            weight.denominator,
        ),
    )


@dataclass(frozen=True, slots=True, init=False)
class OccurrencePrefixReturn:
    """C1/high/low and exact-width return through one chart prefix.

    The return stops at the exact terminal integer.  If that terminal is a
    fork, its two literal children are a separate subsequent transition and
    are exposed only by :meth:`child` or :meth:`ordered_children`.
    """

    _source: BoundaryOccurrence
    _template: MacroTemplate
    _terminal_value: int
    _transition_count: int
    _c1_count: int
    _width_delta: int
    _terminal_leading: int
    _witness: tuple[object, ...]
    _seal: object

    def __init__(
        self,
        source: BoundaryOccurrence,
        template: MacroTemplate,
        *,
        check_endpoint: bool = True,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> None:
        if type(source) is not BoundaryOccurrence:
            raise TypeError("macro occurrence return requires a boundary occurrence")
        if type(template) is not MacroTemplate:
            raise TypeError("macro occurrence return requires a chart template")
        if type(check_endpoint) is not bool:
            raise TypeError("endpoint check flag must be bool")
        if template.outcome not in ("fork", "landmine"):
            raise ValueError("macro template has an unknown terminal outcome")
        if template.outcome == "fork":
            if (
                type(template.destination_a) is not int
                or not 2 <= template.destination_a <= 9
                or len(template.ordered_children) != 2
                or tuple(child.kind for child in template.ordered_children)
                != ("N", "Z")
                or any(
                    child.a != template.destination_a
                    for child in template.ordered_children
                )
            ):
                raise ValueError("fork template lost its ordered N/Z terminal children")
        elif template.destination_a is not None or template.ordered_children:
            raise ValueError("landmine template unexpectedly has fork children")

        terminal, steps, count, width, terminal_leading = _macro_prefix_arithmetic(
            source,
            template,
            check_endpoint=check_endpoint,
            charge_work=charge_work,
            charge_bits=charge_bits,
        )
        object.__setattr__(self, "_source", source)
        object.__setattr__(self, "_template", template)
        object.__setattr__(self, "_terminal_value", terminal)
        object.__setattr__(self, "_transition_count", steps)
        object.__setattr__(self, "_c1_count", count)
        object.__setattr__(self, "_width_delta", width)
        object.__setattr__(self, "_terminal_leading", terminal_leading)
        object.__setattr__(
            self,
            "_witness",
            _prefix_signature(
                source, template, terminal, steps, count, width, terminal_leading
            ),
        )
        object.__setattr__(self, "_seal", _PREFIX_RETURN_SEAL)

    def _validate(self) -> None:
        if getattr(self, "_seal", None) is not _PREFIX_RETURN_SEAL:
            raise ValueError("invalid or uninitialized occurrence prefix return")
        if (
            type(self._source) is not BoundaryOccurrence
            or type(self._template) is not MacroTemplate
            or type(self._terminal_value) is not int
            or self._terminal_value <= 0
            or type(self._transition_count) is not int
            or self._transition_count < 0
            or type(self._c1_count) is not int
            or self._c1_count < 0
            or type(self._width_delta) is not int
            or self._width_delta < 0
            or type(self._terminal_leading) is not int
            or not 1 <= self._terminal_leading <= 9
        ):
            raise ValueError("invalid occurrence prefix return fields")
        if getattr(self, "_witness", None) != _prefix_signature(
            self._source,
            self._template,
            self._terminal_value,
            self._transition_count,
            self._c1_count,
            self._width_delta,
            self._terminal_leading,
        ):
            raise ValueError("occurrence prefix fields disagree with their snapshot")

    @property
    def source(self) -> BoundaryOccurrence:
        self._validate()
        return self._source

    @property
    def template(self) -> MacroTemplate:
        self._validate()
        return self._template

    @property
    def terminal_value(self) -> int:
        self._validate()
        return self._terminal_value

    @property
    def terminal_high_prefix(self) -> int:
        self._validate()
        return self._terminal_value // 100

    @property
    def terminal_low_suffix(self) -> int:
        self._validate()
        return self._terminal_value % 100

    @property
    def terminal_c1_phase(self) -> C1Phase:
        self._validate()
        return C1Phase.from_suffix(self._terminal_leading, self._terminal_value % 100)

    @property
    def terminal_exponent(self) -> int:
        self._validate()
        return self._source.exponent + self._width_delta

    @property
    def transition_count(self) -> int:
        self._validate()
        return self._transition_count

    @property
    def c1_count(self) -> int:
        self._validate()
        return self._c1_count

    @property
    def width_delta(self) -> int:
        self._validate()
        return self._width_delta

    @property
    def outcome(self) -> Literal["fork", "landmine"]:
        self._validate()
        return self._template.outcome

    def ordered_children(
        self,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> tuple[BoundaryOccurrence, ...]:
        """Return the exact N/Z children after, and separate from, the prefix."""
        self._validate()
        _charge(
            charge_work,
            charge_bits,
            1,
            self._terminal_value,
            self._width_delta,
        )
        literal_children = comma_children(self._terminal_value)
        if self._template.outcome == "landmine":
            if literal_children:
                raise AssertionError("landmine terminal has a literal comma child")
            return ()
        child_exponent = self._source.exponent + self._width_delta
        children = tuple(
            BoundaryOccurrence(state, child_exponent)
            for state in self._template.ordered_children
        )
        child_values = tuple(
            child.value(charge_work=charge_work, charge_bits=charge_bits)
            for child in children
        )
        if child_values != literal_children:
            raise AssertionError("ordered macro children differ from literal terminal")
        return children

    def child(
        self,
        kind: Literal["N", "Z"],
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> MacroChildOccurrence:
        """Bind one literal fork edge to its exact receiving occurrence."""
        if kind not in ("N", "Z"):
            raise ValueError("comma macro child kind must be N or Z")
        if self.outcome != "fork":
            raise ValueError("landmine prefix has no literal child occurrence")
        children = self.ordered_children(
            charge_work=charge_work, charge_bits=charge_bits
        )
        index = 0 if kind == "N" else 1
        return MacroChildOccurrence(self, children[index])


@dataclass(frozen=True, slots=True, init=False)
class MacroChildOccurrence:
    """One separate literal N/Z edge after a validated macro prefix.

    This carries the prefix object itself, preserving the distinction between
    the terminal reached by the prefix and the child chosen from that terminal.
    The associated width arithmetic is owned by ``WeightedBoundaryAction``.
    """

    _prefix: OccurrencePrefixReturn
    _kind: Literal["N", "Z"]
    _witness: tuple[object, ...]

    def __init__(
        self, prefix: OccurrencePrefixReturn, target: BoundaryOccurrence
    ) -> None:
        if type(prefix) is not OccurrencePrefixReturn:
            raise TypeError("macro child requires a validated occurrence prefix")
        if type(target) is not BoundaryOccurrence:
            raise TypeError("macro child requires an exact target occurrence")
        children = prefix.ordered_children()
        if target not in children:
            raise ValueError("target occurrence is not an ordered literal macro child")
        object.__setattr__(self, "_prefix", prefix)
        object.__setattr__(self, "_kind", target.state.kind)
        object.__setattr__(self, "_witness", (id(prefix), target.state.kind))

    def _validate(self) -> None:
        self._prefix._validate()
        if self._kind not in ("N", "Z") or getattr(self, "_witness", None) != (
            id(self._prefix),
            self._kind,
        ):
            raise ValueError("macro child selection disagrees with its prefix snapshot")

    @property
    def prefix(self) -> OccurrencePrefixReturn:
        self._validate()
        return self._prefix

    @property
    def source(self) -> BoundaryOccurrence:
        return self.prefix.source

    @property
    def target(self) -> BoundaryOccurrence:
        prefix = self.prefix
        children = prefix._template.ordered_children
        index = 0 if self._kind == "N" else 1
        if len(children) != 2 or children[index].kind != self._kind:
            raise ValueError("macro child selection is stale against its prefix")
        return BoundaryOccurrence(
            children[index], prefix._source.exponent + prefix._width_delta
        )

    @property
    def kind(self) -> Literal["N", "Z"]:
        return self.target.state.kind

    def weighted_action(self) -> WeightedBoundaryAction:
        """Return the shared exact-width action for the selected fork edge."""
        action = WeightedBoundaryAction.from_selected_fork(
            self.prefix.template, self.target.state
        )
        physical_delta = self.target.exponent - self.source.exponent
        if action.exponent_delta != physical_delta:
            raise AssertionError("weighted macro edge differs from physical exponent")
        if action.end != self.target.state:
            raise AssertionError("weighted macro edge changed its occurrence target")
        return action

    def c1_count(
        self,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> int:
        """Return the exact high-prefix change through prefix plus fork edge."""
        source_value, _scale, source_high, _low, _phase = _source_coordinates(
            self.source, charge_work=charge_work, charge_bits=charge_bits
        )
        del source_value
        target_value = self.target.value(
            charge_work=charge_work, charge_bits=charge_bits
        )
        terminal_high = self.prefix.terminal_high_prefix
        source_prefix_count = self.prefix.c1_count
        if terminal_high != source_high + source_prefix_count:
            raise AssertionError("macro prefix lost its source high-prefix binding")
        branch_c1 = target_value // 100 - terminal_high
        if branch_c1 not in (0, 1):
            raise AssertionError("one literal fork edge has an invalid c1 carry")
        total = _sum_exact(source_prefix_count, branch_c1, charge_work, charge_bits)
        if target_value // 100 != source_high + total:
            raise AssertionError("macro child return lost its high-prefix binding")
        return total

    def then(
        self,
        after: MacroChildOccurrence,
        *,
        charge_work: WorkCharge | None = None,
        charge_bits: BitsCharge | None = None,
    ) -> WeightedBoundaryAction:
        """Compose via the shared weighted owner after exact occurrence binding."""
        if type(after) is not MacroChildOccurrence:
            raise TypeError(
                "macro occurrence composition requires another child return"
            )
        if self.target != after.source:
            raise ValueError("macro child returns are not physically adjacent")
        _charge(
            charge_work,
            charge_bits,
            1,
            self.prefix.transition_count,
            after.prefix.transition_count,
            self.prefix.c1_count,
            after.prefix.c1_count,
        )
        combined = self.weighted_action().then(
            after.weighted_action(), charge_bits=charge_bits
        )
        physical_width = after.target.exponent - self.source.exponent
        if combined.exponent_delta != physical_width:
            raise AssertionError("weighted composition lost exact physical width")
        initial_high = self.source.high_prefix(
            charge_work=charge_work, charge_bits=charge_bits
        )
        final_high = after.target.high_prefix(
            charge_work=charge_work, charge_bits=charge_bits
        )
        expected_c1 = _sum_exact(
            self.c1_count(charge_work=charge_work, charge_bits=charge_bits),
            after.c1_count(charge_work=charge_work, charge_bits=charge_bits),
            charge_work,
            charge_bits,
        )
        if final_high - initial_high != expected_c1:
            raise AssertionError("chronological C1 prefix count failed to compose")
        return combined


__all__ = [
    "BoundaryOccurrence",
    "MacroChildOccurrence",
    "OccurrencePrefixReturn",
]
