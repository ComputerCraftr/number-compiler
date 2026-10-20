"""Completed affine endpoint projections for untrusted C1 audit generation."""

from dataclasses import dataclass
from typing import Literal

from number_compiler.sequences.comma.boundary_chart import MAX_CHART_MOVES, PERIOD
from number_compiler.sequences.comma.boundary_quotient import (
    AffineWeight,
    BoundaryState,
    MacroTemplate,
    macro_template_component_seal,
)

_Control = tuple[Literal["fork", "landmine"], int | None]


@dataclass(frozen=True, slots=True)
class CompletedMacroReturnAudit:
    """Minimal immutable projection retained after one macro is checked."""

    source: BoundaryState
    exponent_delta: int
    weight: AffineWeight
    endpoint: AffineWeight
    ordered_children: tuple[BoundaryState, ...]
    control: _Control


@dataclass(frozen=True, slots=True)
class C1SeamObservation:
    """Finite low-phase observation at a represented occurrence."""

    n_terminal_suffix: int
    z_terminal_suffix: int
    source_borrow: int
    target_borrow: int


@dataclass(frozen=True, slots=True)
class C1OccurrencePayload:
    """Occurrence facts kept outside the FutureCID key."""

    represented_exponent: int
    exponent_delta: int
    macro_weight: tuple[int, int, int]
    terminal_endpoint: tuple[int, int, int]
    n_count: int | None
    z_count: int | None
    borrow_innovation: int | None
    seam: C1SeamObservation | None


def _canonical_exponent(state: BoundaryState) -> int:
    residue = state.exponent_residue
    return residue if residue >= 5 else residue + PERIOD


def c1_payloads(
    states: tuple[BoundaryState, ...],
    macros: tuple[CompletedMacroReturnAudit, ...],
    indices: dict[BoundaryState, int],
) -> tuple[C1OccurrencePayload, ...]:
    """Project exact C1 audit fields from checked completed returns."""
    cache: dict[tuple[int, int], tuple[int, int]] = {}
    scales: dict[int, int] = {}
    payloads: list[C1OccurrencePayload] = []
    for state, macro in zip(states, macros, strict=True):
        represented = _canonical_exponent(state)
        receiving = represented + macro.exponent_delta
        if macro.source != state or not 0 <= macro.exponent_delta <= MAX_CHART_MOVES:
            raise ValueError("C1 candidate is outside its canonical source domain")
        weight = (
            macro.weight.numerator_scale,
            macro.weight.numerator_offset,
            macro.weight.denominator,
        )
        endpoint = (
            macro.endpoint.numerator_scale,
            macro.endpoint.numerator_offset,
            macro.endpoint.denominator,
        )
        if not macro.ordered_children:
            payloads.append(
                C1OccurrencePayload(
                    represented,
                    macro.exponent_delta,
                    weight,
                    endpoint,
                    None,
                    None,
                    None,
                    None,
                )
            )
            continue
        returned: list[tuple[int, int]] = []
        for child in macro.ordered_children:
            if receiving % PERIOD != child.exponent_residue:
                raise AssertionError("source exponent transport changed child phase")
            child_index = indices[child]
            key = (child_index, receiving)
            action = cache.get(key)
            if action is None:
                scale = scales.get(receiving)
                if scale is None:
                    scale = 10**receiving
                    scales[receiving] = scale
                child_return = macros[child_index]
                if child_return.source != child:
                    raise ValueError("candidate endpoint is bound to another source")
                action = _candidate_c1_telescope(child, child_return.endpoint, scale)
                cache[key] = action
            returned.append(action)
        (n_count, n_suffix), (z_count, z_suffix) = returned
        source_borrow = 1  # Ordered N/Z constructors have suffixes 99 and 0.
        target_borrow = int(z_suffix < n_suffix)
        seam = C1SeamObservation(n_suffix, z_suffix, source_borrow, target_borrow)
        innovation = z_count - n_count + source_borrow - target_borrow
        payloads.append(
            C1OccurrencePayload(
                represented,
                macro.exponent_delta,
                weight,
                endpoint,
                n_count,
                z_count,
                innovation,
                seam,
            )
        )
    return tuple(payloads)


def _candidate_c1_telescope(
    state: BoundaryState, endpoint: AffineWeight, scale: int
) -> tuple[int, int]:
    """Compute the exact completed-endpoint projection shared by both paths."""
    if type(scale) is not int or scale <= 0 or scale % 100_000:
        raise ValueError("candidate scale is outside the admitted decimal domain")
    initial = state.a * scale - int(state.kind == "N")
    terminal = endpoint.evaluate_at_scale(scale)
    count = terminal // 100 - initial // 100
    if count < 0:
        raise ValueError("candidate endpoint has negative C1 displacement")
    return count, terminal % 100


def candidate_c1_return(
    state: BoundaryState, macro: MacroTemplate, scale: int
) -> tuple[int, int]:
    """Project untrusted audit data from the completed affine endpoint.

    C1 increments telescope to the difference of high prefixes. This is not
    runtime admission: the Isabelle instance must still check the candidate.
    """
    macro_template_component_seal(macro)
    if type(scale) is not int or scale <= 0 or scale % 100_000:
        raise ValueError("candidate scale is outside the admitted decimal domain")
    if macro.source != state:
        raise ValueError("candidate endpoint is bound to another source")
    return _candidate_c1_telescope(state, macro.endpoint, scale)
