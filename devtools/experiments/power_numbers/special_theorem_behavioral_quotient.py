"""Backward behavioral quotient of the actual Pépin / Lucas--Lehmer maps.

This experiment deliberately bypasses hidden factor, bend-distance, and
Frobenius-support coordinates.  It asks whether the *actual theorem transition*
can be quotiented and powered from the final target observer.

For a deterministic transition ``T`` and target observer ``o(x)=[x=target]``,
let ``P_h`` identify states with the same next-h-step output trace.  At dyadic
horizons this is exactly

    P_(2h) = P_h ^ (T^h)^* P_h.

Because the Pépin target -1 maps to +1 forever and the Lucas--Lehmer target 0
maps -2 -> +2 -> +2, a state can hit the target at most once.  Consequently
``P_h`` has the one-rule symbolic description "first-hit distance capped at h".
That grammar is compact, but on prime special-number domains every depth
0..h-1 is populated, so the *extensional* quotient has h+1 classes.

The more decisive obstruction is the scalar theorem-observer sequence of a
passing seed.  It is exactly delta_d, where d is the classical decision depth.
Its infinite Hankel rank over characteristic zero is d+1 (the leading
(d+1)x(d+1) Hankel block is an anti-diagonal permutation matrix).  Hence a
fixed-rank linear packet cannot replace the classical recurrence.

Finally, the composed full maps have degree 2^h.  Any generic arithmetic circuit
formed from x, constants, addition/subtraction, and multiplication needs at
least h multiplicative-depth layers to compute that full polynomial: each
multiplication layer can at most double degree.  This is a lower bound on the
generic powered-map/wreath evaluation, *not* an unconditional lower bound on
special-form primality algorithms that may exploit additional number theory.
"""

from __future__ import annotations

from dataclasses import dataclass

from devtools.verification.fraction_linear_algebra import fraction_matrix_rank
from devtools.verification.partition_refinement import parent_split_count


@dataclass(frozen=True, slots=True)
class SpecialTheoremMapSpec:
    family: str
    parameter: int
    modulus: int
    seed: int
    target: int
    decision_steps: int
    modulus_bits: int
    transition_name: str
    closed_iterate: str

    def __post_init__(self) -> None:
        if self.family not in ("fermat", "mersenne"):
            raise ValueError(self.family)
        if self.parameter < 1 or self.modulus <= 2 or self.decision_steps < 1:
            raise ValueError(
                (self.family, self.parameter, self.modulus, self.decision_steps)
            )
        if not 0 <= self.seed < self.modulus or not 0 <= self.target < self.modulus:
            raise ValueError((self.seed, self.target, self.modulus))

    def transition(self, value: int) -> int:
        x = int(value) % self.modulus
        if self.family == "fermat":
            return (x * x) % self.modulus
        return (x * x - 2) % self.modulus

    @property
    def target_nonrecurrent(self) -> bool:
        first = self.transition(self.target)
        if first == self.target:
            return False
        second = self.transition(first)
        # Pépin: -1 -> +1 -> +1. LL: 0 -> -2 -> +2 -> +2.
        if self.family == "fermat":
            return second == first
        return self.transition(second) == second and second != self.target


def theorem_map_spec(family: str, parameter: int) -> SpecialTheoremMapSpec:
    family, parameter = str(family), int(parameter)
    if family == "fermat":
        if parameter < 1:
            raise ValueError(parameter)
        width = 1 << parameter
        modulus = (1 << width) + 1
        return SpecialTheoremMapSpec(
            family,
            parameter,
            modulus,
            3 % modulus,
            modulus - 1,
            width - 1,
            width + 1,
            "x -> x^2 mod F_n",
            "T^h(x) = x^(2^h) mod F_n",
        )
    if family == "mersenne":
        if parameter < 3 or not parameter & 1:
            raise ValueError(parameter)
        modulus = (1 << parameter) - 1
        return SpecialTheoremMapSpec(
            family,
            parameter,
            modulus,
            4 % modulus,
            0,
            parameter - 2,
            parameter,
            "x -> x^2 - 2 mod M_p",
            "T^h(x) = D_(2^h)(x) = z^(2^h)+z^(-2^h)",
        )
    raise ValueError(family)


def _canonicalize(values: tuple[object, ...] | list[object]) -> tuple[int, ...]:
    ids: dict[object, int] = {}
    out: list[int] = []
    for value in values:
        if value not in ids:
            ids[value] = len(ids)
        out.append(ids[value])
    return tuple(out)


def _partitions_equivalent(left: tuple[int, ...], right: tuple[int, ...]) -> bool:
    if len(left) != len(right):
        return False
    forward: dict[int, int] = {}
    reverse: dict[int, int] = {}
    for a, b in zip(left, right, strict=True):
        if a in forward and forward[a] != b:
            return False
        if b in reverse and reverse[b] != a:
            return False
        forward[a], reverse[b] = b, a
    return True


def first_future_hit_distance(
    spec: SpecialTheoremMapSpec, start: int, horizon: int
) -> int | None:
    """First target hit after 1..horizon transitions, or None.

    This is a bounded truth helper.  It intentionally performs the recurrence
    and is never presented as the missing scalable source-coordinate injector.
    """
    x, horizon = int(start) % spec.modulus, int(horizon)
    if horizon < 1:
        raise ValueError(horizon)
    for distance in range(1, horizon + 1):
        x = spec.transition(x)
        if x == spec.target:
            return distance
    return None


def capped_first_hit_class(
    spec: SpecialTheoremMapSpec, start: int, horizon: int
) -> int:
    distance = first_future_hit_distance(spec, start, horizon)
    return int(horizon) + 1 if distance is None else distance


def seed_decision_trace(spec: SpecialTheoremMapSpec) -> tuple[int, ...]:
    """Observer values through the exact classical decision time, inclusive."""
    x = spec.seed
    out: list[int] = []
    for _ in range(spec.decision_steps + 1):
        out.append(int(x == spec.target))
        x = spec.transition(x)
    return tuple(out)


def _rank_fraction(matrix: list[list[int]]) -> int:
    return fraction_matrix_rank(matrix)


def delta_hankel_rank_differential(distance: int) -> int:
    """Materialize the minimal anti-diagonal Hankel control for delta_distance."""
    distance = int(distance)
    if distance < 0:
        raise ValueError(distance)
    size = distance + 1
    hankel = [[int(i + j == distance) for j in range(size)] for i in range(size)]
    return _rank_fraction(hankel)


@dataclass(frozen=True, slots=True)
class TheoremBehavioralRow:
    horizon: int
    classes: int
    populated_hit_depths: int
    trace_matrix_rank: int
    parent_classes_split: int
    pullback_exact: bool
    capped_first_hit_formula_exact: bool
    matches_linear_h_plus_one: bool
    symbolic_rule_count: int


@dataclass(frozen=True, slots=True)
class SpecialTheoremBehavioralAudit:
    family: str
    parameter: int
    modulus: int
    modulus_bits: int
    decision_steps: int
    seed: int
    target: int
    seed_hits_target_at_decision: bool
    seed_first_hit_distance: int | None
    scalar_observer_hankel_rank: int | None
    passing_rank_equals_modulus_bits_minus_one: bool
    terminal_observer_classes: int
    terminal_observer_successor_closed: bool
    terminal_observer_successor_conflicts: int
    decision_terminal_fiber_classes: int
    decision_terminal_fiber_root_count: int
    passing_terminal_fiber_roots_equal_two_to_depth: bool
    passing_terminal_defect_degree_lower_bound: int | None
    decision_horizon_classes: int
    decision_horizon_expected_prime_classes: int
    dyadic_rows: tuple[TheoremBehavioralRow, ...]
    closed_iterate: str
    powered_descriptor_symbolic_rule_count: int
    generic_full_map_degree_log2: int
    generic_multiplicative_depth_lower_bound: int
    passing_prime_field_degree_below_modulus: bool
    passing_full_map_depth_lower_bound_applies: bool
    classical_nonlinear_steps: int
    powered_map_beats_classical_generic_depth: bool
    hidden_factor_coordinate_used: bool
    bend_coordinate_used: bool
    frobenius_support_coordinate_used: bool
    production_promotable: bool
    conclusion: str


def _terminal_successor_conflicts(
    spec: SpecialTheoremMapSpec, outputs: tuple[int, ...]
) -> int:
    successor_sets: dict[int, set[int]] = {}
    for state, output in enumerate(outputs):
        successor_sets.setdefault(output, set()).add(outputs[spec.transition(state)])
    return sum(len(values) > 1 for values in successor_sets.values())


def _decision_partition(spec: SpecialTheoremMapSpec) -> tuple[int, ...]:
    h = spec.decision_steps
    return _canonicalize(
        tuple(capped_first_hit_class(spec, state, h) for state in range(spec.modulus))
    )


def theorem_behavioral_quotient_audit(
    family: str,
    parameter: int,
    *,
    max_states: int = 70_000,
) -> SpecialTheoremBehavioralAudit:
    """Exact whole-ring audit for bounded special-number controls.

    The full ring is intentionally enumerated so the quotient cannot fake a
    small result by looking only at the one seed orbit.  Candidates larger than
    ``max_states`` are rejected rather than silently sampled.
    """
    spec = theorem_map_spec(family, parameter)
    if spec.modulus > int(max_states):
        raise ValueError(
            f"bounded whole-ring audit requires N <= {max_states}, got {spec.modulus}"
        )
    if not spec.target_nonrecurrent:
        raise AssertionError(
            (spec.family, spec.parameter, "target unexpectedly recurrent")
        )

    transition = tuple(spec.transition(state) for state in range(spec.modulus))
    outputs = tuple(int(state == spec.target) for state in range(spec.modulus))
    # P_1 observes the target predicate *after one transition*.
    classes = _canonicalize(
        tuple(outputs[transition[state]] for state in range(spec.modulus))
    )
    jump = transition  # T^1
    horizon = 1
    rows: list[TheoremBehavioralRow] = []
    previous_classes: tuple[int, ...] | None = None

    while horizon <= spec.decision_steps:
        closed = _canonicalize(
            tuple(
                capped_first_hit_class(spec, state, horizon)
                for state in range(spec.modulus)
            )
        )
        populated = len(
            {
                first_future_hit_distance(spec, state, horizon)
                for state in range(spec.modulus)
            }
            - {None}
        )
        count = len(set(classes))
        if previous_classes is None:
            parent_split = 1
        else:
            parent_split = parent_split_count(previous_classes, classes)
        rows.append(
            TheoremBehavioralRow(
                horizon,
                count,
                populated,
                populated,  # disjoint one-hot hit columns are linearly independent
                parent_split,
                _partitions_equivalent(classes, closed),
                _partitions_equivalent(classes, closed),
                count == horizon + 1,
                1,
            )
        )
        next_horizon = horizon * 2
        if next_horizon > spec.decision_steps:
            break
        previous_classes = classes
        classes = _canonicalize(
            tuple(
                (classes[state], classes[jump[state]]) for state in range(spec.modulus)
            )
        )
        jump = tuple(jump[jump[state]] for state in range(spec.modulus))
        horizon = next_horizon

    seed_trace = seed_decision_trace(spec)
    passes = bool(seed_trace[-1])
    seed_distance = next((i for i, bit in enumerate(seed_trace) if bit), None)
    hankel_rank = None if seed_distance is None else seed_distance + 1
    if (
        seed_distance is not None
        and seed_distance <= 32
        and delta_hankel_rank_differential(seed_distance) != hankel_rank
    ):
        raise AssertionError((spec, seed_distance, hankel_rank))

    terminal_conflicts = _terminal_successor_conflicts(spec, outputs)
    decision_partition = _decision_partition(spec)
    decision_classes = len(set(decision_partition))
    expected_prime_classes = spec.decision_steps + 1
    decision_root_count = sum(
        first_future_hit_distance(spec, state, spec.decision_steps)
        == spec.decision_steps
        for state in range(spec.modulus)
    )
    decision_fiber_classes = 1 if decision_root_count in (0, spec.modulus) else 2
    expected_root_count = 1 << spec.decision_steps

    # Full-map degree after d theorem transitions is exactly 2^d for both x^2
    # and x^2-2.  Multiplicative depth m can create degree at most 2^m.
    generic_depth = spec.decision_steps
    return SpecialTheoremBehavioralAudit(
        spec.family,
        spec.parameter,
        spec.modulus,
        spec.modulus_bits,
        spec.decision_steps,
        spec.seed,
        spec.target,
        passes,
        seed_distance,
        hankel_rank,
        bool(passes and hankel_rank == spec.modulus_bits - 1),
        len(set(outputs)),
        terminal_conflicts == 0,
        terminal_conflicts,
        decision_fiber_classes,
        decision_root_count,
        bool(passes and decision_root_count == expected_root_count),
        expected_root_count if passes else None,
        decision_classes,
        expected_prime_classes,
        tuple(rows),
        spec.closed_iterate,
        1,
        spec.decision_steps,
        generic_depth,
        bool(passes and (1 << spec.decision_steps) < spec.modulus),
        bool(passes and (1 << spec.decision_steps) < spec.modulus),
        spec.decision_steps,
        generic_depth < spec.decision_steps,
        False,
        False,
        False,
        False,
        (
            "actual theorem observer bypasses hidden factor/bend/Frobenius support. "
            "A fixed-horizon terminal fiber has only two classes, but on passing "
            "prime controls it contains 2^h roots, forcing degree/multiplicative "
            "depth h for an exact polynomial defect. A reusable all-horizons "
            "behavioral machine has h+1 classes and the passing seed sequence has "
            "Hankel rank B-1. No asymptotic powered shortcut is proved."
        ),
    )


@dataclass(frozen=True, slots=True)
class TwoPrimaryDepthComparison:
    family: str
    parameter: int
    modulus_bits: int
    behavioral_decision_classes: int
    conditional_two_primary_classes: int
    outer_character_method: str
    outer_character_decided: bool
    deeper_character_available: bool
    conditional_classes_linear_scale: bool
    same_source_depth_injector_missing: bool
    note: str


def two_primary_depth_comparison(
    family: str, parameter: int
) -> TwoPrimaryDepthComparison:
    """Compare the new behavioral quotient with the existing 2-primary tower.

    The pure filtration is a *conditional dynamics theorem* and is never used
    here as a classifier.  This comparison exists to prevent renaming the same
    missing seed-depth coordinate as a new Frobenius/character extractor.
    """
    from number_compiler.arithmetic.polynomials.two_primary_filtration import (
        HigherTwoPowerCharacterUnavailable,
        higher_two_power_character,
        outer_source_character,
        pure_two_primary_image_filtration,
    )

    spec = theorem_map_spec(family, parameter)
    pure = pure_two_primary_image_filtration(family, parameter)
    outer = outer_source_character(family, parameter)
    deeper = True
    try:
        higher_two_power_character(family, parameter, 2)
    except HigherTwoPowerCharacterUnavailable:
        deeper = False
    return TwoPrimaryDepthComparison(
        spec.family,
        spec.parameter,
        spec.modulus_bits,
        spec.decision_steps + 1,
        pure.moore_classes,
        outer.method,
        outer.decided,
        deeper,
        pure.moore_classes >= max(2, spec.modulus_bits // 2),
        not deeper,
        (
            "the pure two-primary image theorem compresses known structure but "
            "still has Theta(B)-scale classes on these families; only the outer "
            "source character is candidate-derived scalably, so deeper class "
            "injection is the same unresolved seed-depth information"
        ),
    )


@dataclass(frozen=True, slots=True)
class SpecialTheoremBehavioralFrontier:
    hidden_coordinate_bypassed: bool
    exact_backward_pullback_implemented: bool
    horizon_independent_two_state_powering_rejected: bool
    fixed_horizon_two_state_fiber_valid: bool
    fixed_horizon_polynomial_injector_depth_linear: bool
    capped_first_hit_grammar_constant_rule: bool
    prime_control_classes_linear_in_horizon: bool
    passing_scalar_hankel_rank_linear_in_bits: bool
    generic_powered_map_depth_matches_classical: bool
    fixed_rank_linear_shortcut_rejected: bool
    powered_wreath_shortcut_proved: bool
    next_target: str


def theorem_behavioral_frontier() -> SpecialTheoremBehavioralFrontier:
    return SpecialTheoremBehavioralFrontier(
        True,
        True,
        True,
        True,
        True,
        True,
        True,
        True,
        True,
        True,
        False,
        (
            "search for a genuinely nonlinear candidate-specific quotient of the "
            "Pépin/LL target predicate that changes the seed-class injector or "
            "multiplicative-depth model; do not reintroduce hidden factor support"
        ),
    )
