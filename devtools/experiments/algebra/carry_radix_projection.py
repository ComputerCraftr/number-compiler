"""Padded alternate-radix / cyclotomic analysis of derived carry fields.

The key distinction in this module is between a *coordinate change* and a new
quotient.  A fixed-width 0/1 word can be read as an integer in any radix b>=2;
retaining the width makes that reinterpretation lossless.  Its universal
number-theoretic structure is the polynomial structure of

    W(z) = d_0 z^(L-1) + ... + d_(L-1).

Every exact factor Phi_m(z) divides W(b) through Phi_m(b) for every evaluation
base b.  The factorization can therefore compress/summarize a carry row without
pretending that changing radix creates information that was absent from the
row.

Multi-valued Collatz and convolution carries are converted reversibly to one
scalar offset plus binary bit planes.  Those planes are ephemeral analysis
views; production continues to retain only the canonical raw field or scalar
end-around boundary carry.
"""

from __future__ import annotations

from collections.abc import Callable, Iterator, Sequence
from dataclasses import dataclass
from itertools import pairwise
from typing import TYPE_CHECKING, TypedDict

from devtools.verification.quotient_synthesis import transition_conflict_count
from number_compiler.arithmetic.carry.carry_normalization import (
    normalization_carry_boundaries,
)
from number_compiler.arithmetic.carry.event_memory import carry_field, pair_step
from number_compiler.arithmetic.fields.projection_field import (
    bounded_cyclotomic_factorization,
    cyclotomic_jet_from_values,
    offset_bit_planes,
    padded_radix_evaluation,
)
from number_compiler.arithmetic.fields.radix import (
    bit_width,
    digits_lsd,
    reverse_pair_sums,
)
from number_compiler.arithmetic.functions.finite_unary import (
    analyze_observer,
    minimize_unary_moore,
)
from number_compiler.arithmetic.polynomials.digit_convolution import (
    cyclic_binary_square_add_projection,
    negacyclic_binary_square_projection,
)
from number_compiler.sequences.collatz.pair import accelerated_odd_collatz
from number_compiler.sequences.collatz.raw_field import CollatzRawDigitField

if TYPE_CHECKING:
    from number_compiler.arithmetic.polynomials.digit_convolution import (
        DigitSquareProjection,
    )


@dataclass(frozen=True, slots=True)
class CarryCyclotomicCoverage:
    rows: int
    planes: int
    nonconstant_planes: int
    rows_with_factor: int
    fully_cyclotomic_planes: int
    factor_degree: int
    active_degree: int
    factorized_description_bits: int
    raw_plane_bits: int
    selective_description_bits: int
    factorization_wins: int

    @property
    def degree_ratio(self) -> float:
        return self.factor_degree / self.active_degree if self.active_degree else 0.0


@dataclass(frozen=True, slots=True)
class ReverseCarryRadixProfile:
    seed: int
    steps: int
    coverage: CarryCyclotomicCoverage
    exact_current_rows: int
    repeated_current_rows: int
    different_next_conflicts: int
    factor_feature_classes: int
    factor_feature_conflicts: int
    sample_bridges: tuple[
        tuple[
            int,
            tuple[int, ...],
            tuple[tuple[int, int], ...],
            tuple[tuple[int, int], ...],
        ],
        ...,
    ]


@dataclass(frozen=True, slots=True)
class CarryFeatureClosureProfile:
    family: str
    parameter: int
    source_states: int
    exact_carry_classes: int
    exact_target_separating: bool
    exact_next_closed: bool
    cyclotomic_feature_classes: int
    cyclotomic_target_separating: bool
    cyclotomic_next_closed: bool


@dataclass(frozen=True, slots=True)
class CombinedCarryDigitObserverProfile:
    family: str
    parameter: int
    source_states: int
    digit_cyclotomic_order: int
    digit_modulus: int
    carry_order_limit: int
    combined_classes: int
    target_separating: bool
    next_closed: bool
    injective: bool
    minimized_observer_classes: int | None


@dataclass(frozen=True, slots=True)
class FamilyCarryProfile:
    family: str
    parameter: int
    source_radix: int
    coverage: CarryCyclotomicCoverage
    max_bit_planes: int
    min_carry: int
    max_carry: int


def _factor_feature(values: Sequence[int], *, order_limit: int) -> tuple[object, ...]:
    factor = bounded_cyclotomic_factorization(values, order_limit=order_limit)
    # Deliberately discard the explicit residual.  This is the compact theorem
    # feature whose closure is being tested, not the lossless factorization key.
    return (
        factor.length,
        factor.leading_zero_padding,
        factor.trailing_zero_shift,
        factor.factors,
    )


def _carry_plane_feature(
    values: Sequence[int], *, order_limit: int
) -> tuple[object, ...]:
    field = tuple(map(int, values))
    offset, planes = offset_bit_planes(field)
    return (
        len(field),
        offset,
        tuple(_factor_feature(plane, order_limit=order_limit) for plane in planes),
    )


def _coverage(
    rows: Sequence[Sequence[int]], *, order_limit: int
) -> CarryCyclotomicCoverage:
    planes = nonconstant = rows_with_factor = fully = factor_degree = active_degree = 0
    factorized_bits = raw_bits = selective_bits = factorization_wins = 0
    for row in rows:
        field = tuple(map(int, row))
        _offset, bitplanes = offset_bit_planes(field)
        row_has_factor = False
        planes += len(bitplanes)
        for plane in bitplanes:
            factor = bounded_cyclotomic_factorization(plane, order_limit=order_limit)
            nonconstant += int(factor.active_degree > 0 or any(plane))
            row_has_factor |= bool(factor.factors)
            fully += int(factor.fully_cyclotomic)
            factor_degree += factor.factor_degree
            active_degree += factor.active_degree
            factor_bits = factor.description_bits
            raw_plane = len(plane) + bit_width(len(plane))
            factorized_bits += factor_bits
            raw_bits += raw_plane
            selective_bits += min(factor_bits, raw_plane)
            factorization_wins += int(factor_bits < raw_plane)
        rows_with_factor += int(row_has_factor)
    return CarryCyclotomicCoverage(
        len(rows),
        planes,
        nonconstant,
        rows_with_factor,
        fully,
        factor_degree,
        active_degree,
        factorized_bits,
        raw_bits,
        selective_bits,
        factorization_wins,
    )


def reverse_carry_rows(
    seed: int = 196, *, steps: int = 256, base: int = 10
) -> tuple[tuple[int, ...], ...]:
    pair = reverse_pair_sums(seed, base)
    rows: list[tuple[int, ...]] = []
    for _ in range(int(steps) + 1):
        rows.append(carry_field(pair, base=base))
        pair, _growth = pair_step(pair, base)
    return tuple(rows)


def reverse_carry_radix_profile(
    seed: int = 196,
    *,
    steps: int = 256,
    base: int = 10,
    order_limit: int = 64,
    evaluation_bases: Sequence[int] = (3, 5, 7, 10),
    sample_steps: Sequence[int] = (10, 40, 55, 93),
) -> ReverseCarryRadixProfile:
    rows = reverse_carry_rows(seed, steps=steps, base=base)
    current, nxt = rows[:-1], rows[1:]
    exact_conflicts = transition_conflict_count(zip(current, nxt, strict=True))
    features = tuple(_factor_feature(row, order_limit=order_limit) for row in rows)
    feature_conflicts = transition_conflict_count(pairwise(features))

    bridges: list[
        tuple[
            int,
            tuple[int, ...],
            tuple[tuple[int, int], ...],
            tuple[tuple[int, int], ...],
        ]
    ] = []
    for step in sample_steps:
        step = int(step)
        if not 0 <= step < len(rows):
            continue
        row = rows[step]
        factor = bounded_cyclotomic_factorization(row, order_limit=order_limit)
        evaluations: list[tuple[int, int]] = []
        for radix in evaluation_bases:
            evaluation = padded_radix_evaluation(row, radix=int(radix))
            divisor = factor.evaluated_cyclotomic_factor(int(radix))
            if factor.trailing_zero_shift:
                divisor *= int(radix) ** factor.trailing_zero_shift
            if divisor and evaluation.value % divisor:
                raise AssertionError(
                    (step, radix, row, factor, evaluation.value, divisor)
                )
            if evaluation.recover_msf_values() != row:
                raise AssertionError((step, radix, row, evaluation))
            evaluations.append((int(radix), evaluation.value))
        bridges.append((step, row, factor.factors, tuple(evaluations)))

    return ReverseCarryRadixProfile(
        int(seed),
        int(steps),
        _coverage(current, order_limit=order_limit),
        len(set(current)),
        len(current) - len(set(current)),
        exact_conflicts,
        len(set(features[:-1])),
        feature_conflicts,
        tuple(bridges),
    )


def _odd_orbit(seed: int) -> Iterator[int]:
    value = int(seed)
    while value > 1 and not (value & 1):
        value //= 2
    while value != 1:
        yield value
        value = accelerated_odd_collatz(value).target


def collatz_carry_profile(
    seed: int,
    *,
    source_radix: int = 10,
    order_limit: int = 64,
) -> FamilyCarryProfile:
    rows = tuple(
        CollatzRawDigitField.from_odd_value(
            value, base=source_radix
        ).normalization_carries()
        for value in _odd_orbit(seed)
    )
    extrema = [value for row in rows for value in row] or [0]
    max_planes = max((len(offset_bit_planes(row)[1]) for row in rows), default=0)
    return FamilyCarryProfile(
        "collatz",
        int(seed),
        int(source_radix),
        _coverage(rows, order_limit=order_limit),
        max_planes,
        min(extrema),
        max(extrema),
    )


def _special_projection(
    family: str, parameter: int, state: int
) -> DigitSquareProjection:
    if family == "fermat":
        width = 1 << int(parameter)
        return negacyclic_binary_square_projection(int(state), width)
    if family == "mersenne":
        width = int(parameter)
        return cyclic_binary_square_add_projection(int(state), width, -2)
    raise ValueError(family)


def _special_transition(
    family: str, parameter: int
) -> tuple[int, Callable[[int], int], Callable[[int], bool]]:
    if family == "fermat":
        modulus = (1 << (1 << int(parameter))) + 1
        return modulus, lambda x: (x * x) % modulus, lambda x: x == modulus - 1
    if family == "mersenne":
        modulus = (1 << int(parameter)) - 1
        return modulus, lambda x: (x * x - 2) % modulus, lambda x: x == 0
    raise ValueError(family)


def _special_carries(family: str, parameter: int, state: int) -> tuple[int, ...]:
    projection = _special_projection(family, parameter, state)
    return normalization_carry_boundaries(projection.field, projection.normalization)


def special_carry_trajectory_profile(
    family: str,
    parameter: int,
    *,
    order_limit: int = 64,
) -> FamilyCarryProfile:
    modulus, transition, _target = _special_transition(family, parameter)
    state = 3 % modulus if family == "fermat" else 4 % modulus
    iterations = (
        (1 << int(parameter)) - 1 if family == "fermat" else max(0, int(parameter) - 2)
    )
    rows: list[tuple[int, ...]] = []
    for _ in range(iterations):
        rows.append(_special_carries(family, parameter, state))
        state = transition(state)
    extrema = [value for row in rows for value in row] or [0]
    max_planes = max((len(offset_bit_planes(row)[1]) for row in rows), default=0)
    return FamilyCarryProfile(
        family,
        int(parameter),
        2,
        _coverage(tuple(rows), order_limit=order_limit),
        max_planes,
        min(extrema),
        max(extrema),
    )


def special_carry_feature_closure_profile(
    family: str,
    parameter: int,
    *,
    order_limit: int = 16,
) -> CarryFeatureClosureProfile:
    """Exhaustively test exact carry and lossy cyclotomic carry features.

    The bounded spaces intentionally stay small enough for exact enumeration.
    A failure for the *entire* carry vector proves that no lossless radix or
    factorization of that same vector can create next-step closure.
    """
    modulus, transition, target = _special_transition(family, parameter)
    if modulus > 1024:
        raise ValueError("bounded carry closure audit supports at most 1024 states")
    carries = tuple(
        _special_carries(family, parameter, state) for state in range(modulus)
    )
    features = tuple(
        _carry_plane_feature(row, order_limit=order_limit) for row in carries
    )

    def audit(keys: Sequence[object]) -> tuple[int, bool, bool]:
        current = tuple(keys)
        result = analyze_observer(
            current,
            tuple(current[transition(state)] for state in range(modulus)),
            tuple(bool(target(state)) for state in range(modulus)),
        )
        return result.classes, result.target_separating, result.next_closed

    exact_classes, exact_target, exact_next = audit(carries)
    feature_classes, feature_target, feature_next = audit(features)
    return CarryFeatureClosureProfile(
        family,
        int(parameter),
        modulus,
        exact_classes,
        exact_target,
        exact_next,
        feature_classes,
        feature_target,
        feature_next,
    )


def special_combined_carry_digit_observer_profile(
    family: str,
    parameter: int,
    *,
    digit_cyclotomic_order: int = 2,
    digit_modulus: int = 4,
    carry_order_limit: int = 16,
) -> CombinedCarryDigitObserverProfile:
    """Test whether one lossy digit channel plus carry factors forms a closed observer.

    This is the actual test of whether carry structure helps *summarize projection digits*.
    A positive result is allowed to be a refinement of the minimal Moore observer; if the
    combined feature is target-separating and next-closed, we minimize its unary transition
    quotient exactly and report the resulting observer-class count.
    """
    modulus, transition, target = _special_transition(family, parameter)
    width = modulus.bit_length()
    keys: list[tuple[object, ...]] = []
    for state in range(modulus):
        digits = digits_lsd(state, 2, width)
        digit_feature = cyclotomic_jet_from_values(
            digits, order=int(digit_cyclotomic_order), modulus=int(digit_modulus)
        ).residue
        carry_feature = _carry_plane_feature(
            _special_carries(family, parameter, state),
            order_limit=int(carry_order_limit),
        )
        keys.append((digit_feature, carry_feature))

    class_index: dict[tuple[object, ...], int] = {}
    for key in keys:
        class_index.setdefault(key, len(class_index))
    outputs: list[bool | None] = [None] * len(class_index)
    successors: list[int | None] = [None] * len(class_index)
    target_ok = True
    next_ok = True
    for state, key in enumerate(keys):
        index = class_index[key]
        output = bool(target(state))
        successor = class_index[keys[transition(state)]]
        if outputs[index] is None:
            outputs[index] = output
            successors[index] = successor
        else:
            target_ok &= outputs[index] == output
            next_ok &= successors[index] == successor

    minimized: int | None = None
    if target_ok and next_ok:
        concrete_outputs = tuple(bool(value) for value in outputs)
        assert all(value is not None for value in successors)
        concrete_successors = tuple(value for value in successors if value is not None)
        minimized = minimize_unary_moore(concrete_successors, concrete_outputs).classes

    return CombinedCarryDigitObserverProfile(
        family,
        int(parameter),
        modulus,
        int(digit_cyclotomic_order),
        int(digit_modulus),
        int(carry_order_limit),
        len(class_index),
        bool(target_ok),
        bool(next_ok),
        len(class_index) == modulus,
        minimized,
    )


class CarryRadixMetrics(TypedDict):
    reverse_add_196: ReverseCarryRadixProfile
    collatz: list[FamilyCarryProfile]
    special_trajectories: list[FamilyCarryProfile]
    special_closure: list[CarryFeatureClosureProfile]
    special_combined_observers: list[CombinedCarryDigitObserverProfile]


def carry_radix_projection_metrics() -> CarryRadixMetrics:
    return {
        "reverse_add_196": reverse_carry_radix_profile(),
        "collatz": [
            collatz_carry_profile(seed, source_radix=radix)
            for seed in (27, 6171, 837799)
            for radix in (4, 10, 16)
        ],
        "special_trajectories": [
            special_carry_trajectory_profile("fermat", n) for n in (3, 4, 5)
        ]
        + [special_carry_trajectory_profile("mersenne", p) for p in (11, 19, 31)],
        "special_closure": [
            special_carry_feature_closure_profile("fermat", n) for n in (1, 2, 3)
        ]
        + [special_carry_feature_closure_profile("mersenne", p) for p in (3, 5, 7)],
        "special_combined_observers": [
            special_combined_carry_digit_observer_profile("fermat", 3),
            special_combined_carry_digit_observer_profile("mersenne", 5),
            special_combined_carry_digit_observer_profile("mersenne", 7),
            special_combined_carry_digit_observer_profile("mersenne", 11),
            special_combined_carry_digit_observer_profile("mersenne", 13),
        ],
    }


__all__ = [
    "CarryCyclotomicCoverage",
    "CarryFeatureClosureProfile",
    "CombinedCarryDigitObserverProfile",
    "FamilyCarryProfile",
    "ReverseCarryRadixProfile",
    "carry_radix_projection_metrics",
    "collatz_carry_profile",
    "reverse_carry_radix_profile",
    "reverse_carry_rows",
    "special_carry_feature_closure_profile",
    "special_carry_trajectory_profile",
    "special_combined_carry_digit_observer_profile",
]
