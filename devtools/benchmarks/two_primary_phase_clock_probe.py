"""Bounded independent audit of prime two-primary phase clocks.

Finite discrete-log/circle enumeration is deliberately charged here.  The
runtime phase occurrence only performs the direct normalized jump; this probe
does not admit a production scheduler or infer primality from a clock shape.
"""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from functools import lru_cache

from number_compiler.arithmetic.functions.finite_unary import (
    minimize_unary_moore,
    partition_equivalent,
)
from number_compiler.sequences.power_numbers.numbers import (
    fermat_number,
    mersenne_number,
)
from number_compiler.sequences.power_numbers.two_primary_clock import (
    PrimeTwoPrimaryPhaseOccurrence,
    bounded_prime_two_primary_depth_clock,
    mersenne_norm_one_multiply,
    mersenne_norm_one_trace,
    prime_two_primary_depth_clock_cache_info,
    two_primary_survival_depth_from_remaining,
    two_primary_survival_depth_view,
)
from number_compiler.sequences.prime.set import is_prime_u64


@dataclass(frozen=True, slots=True)
class TwoPrimaryPhaseClockAudit:
    family: str
    parameter: int
    modulus: int
    candidate_prime: bool
    carrier_scope: str
    carrier_rows: int
    concrete_generator_order: int
    expected_two_primary_order: int
    pure_order_admitted: bool
    target_present: bool
    independent_moore_classes: int
    expected_prime_classes: int
    depth_action_classes: int | None
    moore_equals_depth_action: bool
    generator_enumeration_rows: int
    phase_lookup_rows: int
    generator_multiplications: int
    measured_horizons: tuple[int, ...]
    retained_source_phase_bits: tuple[int, ...]
    direct_jump_checks: int
    direct_jump_primitive_successors: int
    action_cache_second_lookup_hits: int
    exact_phase_is_occurrence_payload: bool
    full_carrier_derived_view_classes: int | None
    full_carrier_enriched_classes: int | None
    full_carrier_views_refine_action: bool | None
    full_carrier_dead_sink_objects: int | None
    scheduler_admitted: bool = False


@dataclass(frozen=True, slots=True)
class TwoPrimaryDepthViewAudit:
    family: str
    parameter: int
    local_depths: tuple[int, ...]
    minimum_local_depth: int
    initial_level: int
    profile_source: str
    extraction_candidate_derived: bool
    temporal_rows: int
    remaining_depth_classes: int
    derived_view_classes: int
    dead_rows: int
    dead_sink_objects: int
    bounded_moore_classes: int | None
    source_moore_classes_seen: int | None
    enriched_source_classes: int | None
    remaining_matches_source_moore: bool | None
    derived_views_refine_source_moore: bool | None
    point_observer_and_survival_observer_agree: bool | None
    scheduler_admitted: bool = False


def _clock_cache_hit(family: str, parameter: int) -> tuple[int, int]:
    first = bounded_prime_two_primary_depth_clock(family, parameter)
    middle = prime_two_primary_depth_clock_cache_info()
    second = bounded_prime_two_primary_depth_clock(family, parameter)
    after = prime_two_primary_depth_clock_cache_info()
    if first is not second:
        raise AssertionError((family, parameter, "noncanonical-clock-cache"))
    return first.classes, after[0] - middle[0]


def _full_carrier_view_metrics(
    action_ids: tuple[int, ...], moore_ids: tuple[int, ...]
) -> tuple[int, int, bool, int]:
    views = tuple(
        two_primary_survival_depth_from_remaining(action) for action in action_ids
    )
    derived_classes = len({view.derived_views for view in views})
    enriched_classes = len(
        {
            (moore, view.derived_views)
            for moore, view in zip(moore_ids, views, strict=True)
        }
    )
    moore_classes = len(set(moore_ids))
    dead_objects = len({id(view) for view in views if not view.survives})
    return (
        derived_classes,
        enriched_classes,
        enriched_classes > moore_classes,
        dead_objects,
    )


def _fermat_audit(index: int) -> TwoPrimaryPhaseClockAudit:
    n = int(index)
    width = 1 << n
    modulus = fermat_number(n)
    expected_order = 1 << width
    powers: list[int] = []
    phase_by_residue: dict[int, int] = {}
    value = 1
    while value not in phase_by_residue:
        phase_by_residue[value] = len(powers)
        powers.append(value)
        value = value * 3 % modulus
        if len(powers) > expected_order:
            raise AssertionError((n, "unbounded-generator-orbit"))
    order = len(powers)
    pure = (
        value == 1 and order == expected_order and len(phase_by_residue) == modulus - 1
    )

    transition = tuple(value * value % modulus for value in range(modulus))
    outputs = tuple(value == modulus - 1 for value in range(modulus))
    moore = minimize_unary_moore(transition, outputs)
    action_ids: list[int] = []
    jump_checks = 0
    horizons = (1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1_024, 10**12)
    for source in range(modulus):
        occurrence = (
            PrimeTwoPrimaryPhaseOccurrence.from_phase(
                "fermat", n, 0, exceptional_zero=True
            )
            if source == 0
            else PrimeTwoPrimaryPhaseOccurrence.from_phase(
                "fermat", n, phase_by_residue[source]
            )
        )
        action_ids.append(occurrence.action_state)
        for steps in (0, *horizons):
            jumped = occurrence.jump(steps)
            if source == 0:
                expected = reconstructed = 0
            else:
                reconstructed = powers[jumped.phase]
                expected = 1 if steps >= width else pow(source, 1 << steps, modulus)
            if reconstructed != expected:
                raise AssertionError((n, source, steps, reconstructed, expected))
            jump_checks += 1
    classes, hits = _clock_cache_hit("fermat", n)
    equivalent = pure and partition_equivalent(moore.class_ids, tuple(action_ids))
    full_views = _full_carrier_view_metrics(tuple(action_ids), moore.class_ids)
    return TwoPrimaryPhaseClockAudit(
        "fermat",
        n,
        modulus,
        is_prime_u64(modulus),
        "complete-residue-ring",
        modulus,
        order,
        expected_order,
        pure,
        outputs.count(True) > 0,
        moore.classes,
        width + 1,
        classes,
        equivalent,
        order,
        order,
        order,
        horizons,
        tuple(
            PrimeTwoPrimaryPhaseOccurrence.from_phase("fermat", n, 1)
            .jump(horizon)
            .retained_phase_bits
            for horizon in horizons
        ),
        jump_checks,
        0,
        hits,
        True,
        *full_views,
    )


def _mersenne_circle(exponent: int) -> tuple[tuple[tuple[int, int], ...], int]:
    p = int(exponent)
    modulus = mersenne_number(p)
    generator = (2, 1)
    elements: list[tuple[int, int]] = []
    seen: set[tuple[int, int]] = set()
    element = (1, 0)
    limit = 1 << p
    while element not in seen:
        seen.add(element)
        elements.append(element)
        element = mersenne_norm_one_multiply(element, generator, modulus)
        if len(elements) > limit:
            raise AssertionError((p, "unbounded-circle-orbit"))
    if element != (1, 0):
        raise AssertionError((p, "circle-generator-entered-nonidentity-cycle", element))
    return tuple(elements), len(elements)


def _mersenne_audit(exponent: int) -> TwoPrimaryPhaseClockAudit:
    p = int(exponent)
    modulus = mersenne_number(p)
    elements, order = _mersenne_circle(p)
    expected_order = 1 << p
    pure = order == expected_order
    traces = tuple(
        sorted({mersenne_norm_one_trace(element, modulus) for element in elements})
    )
    trace_index = {trace: index for index, trace in enumerate(traces)}
    transition = tuple(trace_index[(trace * trace - 2) % modulus] for trace in traces)
    outputs = tuple(trace == 0 for trace in traces)
    moore = minimize_unary_moore(transition, outputs)

    action_ids: list[int] = []
    jump_checks = 0
    horizons = (1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1_024, 10**12)
    if pure:
        phase_by_trace: dict[int, int] = {}
        for phase, element in enumerate(elements):
            trace = mersenne_norm_one_trace(element, modulus)
            canonical = min(phase, (-phase) % expected_order)
            old = phase_by_trace.setdefault(trace, canonical)
            if old != canonical:
                raise AssertionError((p, trace, old, canonical))
        for trace in traces:
            occurrence = PrimeTwoPrimaryPhaseOccurrence.from_phase(
                "mersenne", p, phase_by_trace[trace]
            )
            action_ids.append(occurrence.action_state)
            for steps in (0, *horizons):
                jumped = occurrence.jump(steps)
                reconstructed = mersenne_norm_one_trace(elements[jumped.phase], modulus)
                if steps >= p:
                    expected = 2 % modulus
                else:
                    expected = trace
                    for _ in range(steps):
                        expected = (expected * expected - 2) % modulus
                if reconstructed != expected:
                    raise AssertionError((p, trace, steps, reconstructed, expected))
                jump_checks += 1
        classes, hits = _clock_cache_hit("mersenne", p)
        equivalent = partition_equivalent(moore.class_ids, tuple(action_ids))
        full_views: tuple[int, int, bool, int] | tuple[None, None, None, None] = (
            _full_carrier_view_metrics(tuple(action_ids), moore.class_ids)
        )
    else:
        classes = None
        hits = 0
        equivalent = False
        full_views = (None, None, None, None)
    return TwoPrimaryPhaseClockAudit(
        "mersenne",
        p,
        modulus,
        is_prime_u64(modulus),
        "generated-quadratic-unit-trace-orbit",
        len(traces),
        order,
        expected_order,
        pure,
        outputs.count(True) > 0,
        moore.classes,
        p,
        classes,
        equivalent,
        order,
        len(traces) if pure else 0,
        order,
        horizons,
        (
            tuple(
                PrimeTwoPrimaryPhaseOccurrence.from_phase("mersenne", p, 1)
                .jump(horizon)
                .retained_phase_bits
                for horizon in horizons
            )
            if pure
            else ()
        ),
        jump_checks,
        0,
        hits,
        True,
        *full_views,
    )


@lru_cache(maxsize=1)
def two_primary_phase_clock_audits() -> tuple[TwoPrimaryPhaseClockAudit, ...]:
    return tuple(_fermat_audit(n) for n in (2, 3, 4)) + tuple(
        _mersenne_audit(p) for p in (5, 7, 11, 13)
    )


_DEPTH_PROFILES = (
    ("fermat", 2, (1,), "bounded-factor-truth"),
    ("fermat", 3, (4,), "bounded-factor-truth"),
    ("fermat", 4, (11,), "bounded-factor-truth"),
    ("mersenne", 5, (3,), "bounded-factor-truth"),
    ("mersenne", 7, (5,), "bounded-factor-truth"),
    ("mersenne", 13, (11,), "bounded-factor-truth"),
    ("fermat", 5, (1, 1), "supplied-local-germ-control"),
    ("fermat", 9, (6, 1), "supplied-local-germ-control"),
    ("mersenne", 11, (0, 0), "supplied-local-germ-control"),
    ("mersenne", 29, (0, 0, 1), "supplied-local-germ-control"),
)


def _depth_view_audit(
    family: str,
    parameter: int,
    local_depths: tuple[int, ...],
    profile_source: str,
) -> TwoPrimaryDepthViewAudit:
    from devtools.proofs.oracles.bounded_filtration import (
        bounded_candidate_image_filtration,
    )

    minimum = min(local_depths)
    initial_level = 1 if family == "fermat" else 0
    steps = tuple(range(minimum + 4))
    views = tuple(
        two_primary_survival_depth_view(local_depths, initial_level + step)
        for step in steps
    )
    dead_ids = {id(view) for view in views if not view.survives}
    bounded = None
    if (family == "fermat" and parameter <= 4) or (
        family == "mersenne" and parameter <= 13
    ):
        bounded = bounded_candidate_image_filtration(family, parameter)
    if bounded is None:
        moore_classes = source_classes = enriched_classes = None
        equivalent = refined = observer_agreement = None
    else:
        assert bounded.machine is not None and bounded.source_class is not None
        states = tuple(
            bounded.machine.power_state(bounded.source_class, step)[0] for step in steps
        )
        remaining = tuple(view.remaining for view in views)
        enriched = tuple(
            (state, view.derived_views)
            for state, view in zip(states, views, strict=True)
        )
        moore_classes = bounded.moore_classes
        source_classes = len(set(states))
        enriched_classes = len(set(enriched))
        equivalent = partition_equivalent(states, remaining)
        refined = enriched_classes > source_classes
        observer_agreement = all(
            bool(bounded.machine.output(state)) == (view.remaining == 1)
            for state, view in zip(states, views, strict=True)
        )
    return TwoPrimaryDepthViewAudit(
        family,
        parameter,
        local_depths,
        minimum,
        initial_level,
        profile_source,
        False,
        len(steps),
        len({view.canonical_key for view in views}),
        len({view.derived_views for view in views}),
        sum(not view.survives for view in views),
        len(dead_ids),
        moore_classes,
        source_classes,
        enriched_classes,
        equivalent,
        refined,
        observer_agreement,
    )


@lru_cache(maxsize=1)
def two_primary_depth_view_audits() -> tuple[TwoPrimaryDepthViewAudit, ...]:
    return tuple(_depth_view_audit(*profile) for profile in _DEPTH_PROFILES)


def metrics_dict() -> dict[str, object]:
    return {
        "two_primary_phase_clocks": [
            asdict(row) for row in two_primary_phase_clock_audits()
        ],
        "two_primary_depth_views": [
            asdict(row) for row in two_primary_depth_view_audits()
        ],
    }


if __name__ == "__main__":
    print(json.dumps(metrics_dict(), indent=2, sort_keys=True))


__all__ = [
    "TwoPrimaryPhaseClockAudit",
    "TwoPrimaryDepthViewAudit",
    "metrics_dict",
    "two_primary_phase_clock_audits",
    "two_primary_depth_view_audits",
]
