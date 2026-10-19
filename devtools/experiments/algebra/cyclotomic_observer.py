"""Boundary-aware normalization defects and unified cyclotomic-jet observers.

This pass asks a stricter question than carry-word compression: whether small
algebraic coordinates form an exact next-closed observer.  It uses the single
``CyclotomicDigitBlock`` quotient for both linear local jets (Phi_1/Phi_2) and
higher root-of-unity channels, and keeps existing canonical residue interfaces
when a jet coordinate is merely a different spelling of information already
present in the compiler.
"""

from __future__ import annotations

from collections.abc import Callable, Iterable, Sequence
from dataclasses import dataclass
from itertools import pairwise
from typing import TYPE_CHECKING, TypedDict

from devtools.experiments.algebra.projection_observer import SignQuotientObserverProfile
from devtools.verification import exact_oracle
from devtools.verification.carry_action_quotient import CarryResetSignature
from number_compiler.arithmetic.carry.carry_itinerary import (
    reverse_add_base_pm_residues,
)
from number_compiler.arithmetic.carry.carry_normalization import (
    end_around_normalization_defect,
    linear_normalization_defect,
    linear_normalization_fields,
)
from number_compiler.arithmetic.carry.event_memory import carry_field, pair_step
from number_compiler.arithmetic.fields.projection_field import (
    binomial_moments_from_values,
    cyclotomic_jet_from_values,
)
from number_compiler.arithmetic.fields.radix import digits_lsd, reverse_radix_integer
from number_compiler.arithmetic.functions.finite_unary import analyze_observer
from number_compiler.arithmetic.polynomials.cyclotomic import (
    cyclotomic_power_coefficients,
)
from number_compiler.arithmetic.polynomials.cyclotomic_family import (
    normalization_component,
)
from number_compiler.arithmetic.polynomials.digit_convolution import (
    cyclic_binary_square_add_projection,
    negacyclic_binary_square_projection,
)
from number_compiler.arithmetic.polynomials.digit_cyclotomic import CyclotomicDigitBlock
from number_compiler.arithmetic.polynomials.polynomial import polynomial_remainder_monic
from number_compiler.arithmetic.polynomials.primary_jet import primary_jet_from_digits
from number_compiler.sequences.collatz.pair import accelerated_odd_collatz
from number_compiler.sequences.collatz.raw_field import CollatzRawDigitField

if TYPE_CHECKING:
    from number_compiler.arithmetic.carry.carry_normalization import NormalizationDefect


@dataclass(frozen=True, slots=True)
class JetUnificationProfile:
    degree: int
    modulus: int
    phi1_equals_binomial: bool
    phi2_equals_primary: bool


@dataclass(frozen=True, slots=True)
class NormalizationDefectAudit:
    reverse_steps: int
    reverse_zero_boundary_padded_steps: int
    collatz_steps: int
    cyclic_states: int
    negacyclic_states: int
    exact: bool


@dataclass(frozen=True, slots=True)
class ReverseJetCandidate:
    order: int
    power: int
    modulus: int
    classes: int
    conflicts: int

    @property
    def injective_on_trajectory(self) -> bool:
        return self.classes == 256


@dataclass(frozen=True, slots=True)
class ReverseCyclotomicObserverProfile:
    seed: int
    steps: int
    collision_steps: tuple[int, int]
    collision_action_equal: bool
    collision_carry_equal: bool
    collision_base_minus_residues: tuple[int, int]
    collision_pair_phi1_mod_base_minus: tuple[int, int]
    existing_base_minus_separates: bool
    candidate_count: int
    zero_conflict_candidates: int
    zero_conflict_noninjective_candidates: int
    minimum_zero_conflict_classes: int | None
    neighboring_base_minus_conflicts: int
    neighboring_base_pm_conflicts: int
    best_candidates: tuple[ReverseJetCandidate, ...]


@dataclass(frozen=True, slots=True)
class TemporalClosureRow:
    history: int
    classes: int
    conflicts: int


@dataclass(frozen=True, slots=True)
class ReverseTemporalObserverProfile:
    seed_start: int
    seed_stop: int
    steps: int
    base_minus: tuple[TemporalClosureRow, ...]
    base_pm: tuple[TemporalClosureRow, ...]
    apparent_jet_order: int
    apparent_jet_modulus: int
    training_seed_stop: int
    training_steps: int
    training_classes: int
    training_conflicts: int
    holdout_seed_start: int
    holdout_seed_stop: int
    holdout_steps: int
    holdout_classes: int
    holdout_conflicts: int


@dataclass(frozen=True, slots=True)
class ReverseResidualSuccessorCollision:
    """Two exact proof states aliased by a proposed bounded observer."""

    observer: str
    first_seed: int
    first_step: int
    first_value: int
    first_pair: tuple[int, ...]
    second_seed: int
    second_step: int
    second_value: int
    second_pair: tuple[int, ...]
    shared_key: object
    first_successor_key: object
    second_successor_key: object

    @property
    def is_successor_collision(self) -> bool:
        return self.first_successor_key != self.second_successor_key


@dataclass(frozen=True, slots=True)
class MersennePhiSignProfile:
    exponent: int
    states: int
    phi_classes: int
    sign_classes: int
    same_partition: bool
    target_separating: bool
    next_closed: bool


@dataclass(frozen=True, slots=True)
class SignQuotientWorkProfile:
    family: str
    parameter: int
    baseline_scalar_products: int
    quotient_scalar_products: int
    baseline_coefficient_additions: int
    quotient_coefficient_additions: int
    sign_quotient_steps: int
    nonzero_digits_saved: int

    @property
    def scalar_reduction(self) -> float:
        if not self.baseline_scalar_products:
            return 0.0
        return 1.0 - self.quotient_scalar_products / self.baseline_scalar_products

    @property
    def addition_reduction(self) -> float:
        if not self.baseline_coefficient_additions:
            return 0.0
        return (
            1.0
            - self.quotient_coefficient_additions / self.baseline_coefficient_additions
        )


@exact_oracle()
def jet_unification_profile(
    values: Sequence[int] = (2, 15, 3, 2, 2, 3, 15, 2),
    *,
    degree: int = 4,
    modulus: int = 32,
) -> JetUnificationProfile:
    """Verify that the generalized jet subsumes the old two local channels."""
    vals = tuple(map(int, values))
    degree, modulus = int(degree), int(modulus)
    phi1 = cyclotomic_jet_from_values(vals, order=1, power=degree, modulus=modulus)
    phi2 = cyclotomic_jet_from_values(vals, order=2, power=degree, modulus=modulus)
    binomial = binomial_moments_from_values(vals, degree=degree, modulus=modulus)
    primary = primary_jet_from_digits(vals, degree=degree, modulus=modulus)
    return JetUnificationProfile(
        degree,
        modulus,
        phi1.local_linear_coefficients == binomial.moments,
        phi2.local_linear_coefficients == primary.jet,
    )


@exact_oracle()
def _zero_boundary_reduced_identity(
    defect: NormalizationDefect,
    *,
    order: int,
    power: int,
    modulus: int,
) -> bool:
    # The source-digit module owns the normalization morphism now; research does
    # not duplicate ``(base-z)Q`` arithmetic locally.
    component = normalization_component(
        defect,
        order=int(order),
        power=int(power),
        modulus=int(modulus),
    )
    return component.identity_holds


@exact_oracle()
def normalization_defect_audit() -> NormalizationDefectAudit:
    """Exercise the boundary-aware identity across all active sequence families."""
    reverse_steps = reverse_zero = collatz_steps = cyclic_states = negacyclic_states = 0
    exact = True

    pair = tuple(
        d + e
        for d, e in zip(digits_lsd(196, 10), reversed(digits_lsd(196, 10)), strict=True)
    )
    for _ in range(64):
        defect = linear_normalization_defect(pair, base=10)
        exact &= defect.identity_holds
        reverse_steps += 1
        # One zero coefficient consumes the binary terminal growth carry and
        # turns the finite identity into the literal zero-boundary form.
        padded = linear_normalization_defect(pair + (0,), base=10)
        if padded.boundary_in == 0 and padded.boundary_out == 0:
            exact &= _zero_boundary_reduced_identity(
                padded, order=1, power=2, modulus=32
            )
            exact &= _zero_boundary_reduced_identity(
                padded, order=2, power=2, modulus=32
            )
            reverse_zero += 1
        pair, _ = pair_step(pair, 10)

    for radix in (4, 10, 16):
        value = 27
        while value != 1:
            if not (value & 1):
                value //= 2
                continue
            field = CollatzRawDigitField.from_odd_value(value, base=radix)
            defect = linear_normalization_defect(field.coefficients, base=radix)
            digits, carries = linear_normalization_fields(
                field.coefficients, base=radix
            )
            exact &= defect.identity_holds
            exact &= carries == field.normalization_carries()
            exact &= digits == field.normalized_digits()[: len(digits)]
            collatz_steps += 1
            value = accelerated_odd_collatz(value).target

    # Exhaustive small end-around spaces.  Their boundary polynomial vanishes
    # in z^L-sign, hence also in every cyclotomic factor of that ring modulus.
    for state_1 in range(31):
        projection = cyclic_binary_square_add_projection(state_1, 5, -2)
        defect = end_around_normalization_defect(
            projection.field, projection.normalization
        )
        exact &= defect.identity_holds and defect.boundary_vanishes_mod_end_around(1)
        exact &= _zero_boundary_reduced_identity(defect, order=5, power=1, modulus=16)
        cyclic_states += 1
    for state_2 in range(17):
        projection = negacyclic_binary_square_projection(state_2, 4)
        defect = end_around_normalization_defect(
            projection.field, projection.normalization
        )
        exact &= defect.identity_holds and defect.boundary_vanishes_mod_end_around(-1)
        exact &= _zero_boundary_reduced_identity(defect, order=8, power=1, modulus=16)
        negacyclic_states += 1

    return NormalizationDefectAudit(
        reverse_steps,
        reverse_zero,
        collatz_steps,
        cyclic_states,
        negacyclic_states,
        bool(exact),
    )


@exact_oracle()
def _reverse_orbit(
    seed: int, steps: int, base: int
) -> tuple[
    tuple[int, int, tuple[int, ...], tuple[object, ...], tuple[int, ...], int, int], ...
]:
    value = int(seed)
    out: list[
        tuple[int, int, tuple[int, ...], tuple[object, ...], tuple[int, ...], int, int]
    ] = []
    for step in range(int(steps) + 1):
        digits = digits_lsd(value, base)
        pair = tuple(digits[i] + digits[-1 - i] for i in range(len(digits)))
        action = CarryResetSignature.from_pair(pair, base=base).canonical_key
        carry = carry_field(pair, base=base)
        minus, plus = reverse_add_base_pm_residues(value, len(digits), base=base)
        out.append((step, value, pair, action, carry, minus, plus))
        value += reverse_radix_integer(value, base)
    return tuple(out)


@exact_oracle()
def _closure(keys: Sequence[object]) -> tuple[int, int]:
    audit = analyze_observer(tuple(keys[:-1]), tuple(keys[1:]))
    return audit.classes, audit.successor_conflicts


@exact_oracle()
def _neighbor_residue_conflicts(*, base: int = 10) -> tuple[int, int]:
    minus_map: dict[object, object] = {}
    pm_map: dict[object, object] = {}
    minus_conflicts = pm_conflicts = 0
    for seed in range(190, 203):
        orbit = _reverse_orbit(seed, 64, base)
        for current, nxt in pairwise(orbit):
            k_minus = (current[3], current[5])
            n_minus = (nxt[3], nxt[5])
            k_pm = (current[3], current[5], current[6])
            n_pm = (nxt[3], nxt[5], nxt[6])
            if k_minus in minus_map and minus_map[k_minus] != n_minus:
                minus_conflicts += 1
            else:
                minus_map.setdefault(k_minus, n_minus)
            if k_pm in pm_map and pm_map[k_pm] != n_pm:
                pm_conflicts += 1
            else:
                pm_map.setdefault(k_pm, n_pm)
    return minus_conflicts, pm_conflicts


def _successor_conflict_counts(
    transitions: Iterable[tuple[object, object]],
) -> tuple[int, int]:
    seen: dict[object, object] = {}
    keys: set[object] = set()
    conflicts = 0
    for key, successor in transitions:
        keys.add(key)
        old = seen.get(key)
        if old is None:
            seen[key] = successor
        elif old != successor:
            conflicts += 1
    return len(keys), conflicts


@exact_oracle()
def _temporal_feature_closure(
    orbits: tuple[
        tuple[
            tuple[
                int, int, tuple[int, ...], tuple[object, ...], tuple[int, ...], int, int
            ],
            ...,
        ],
        ...,
    ],
    feature: Callable[
        [
            tuple[
                int, int, tuple[int, ...], tuple[object, ...], tuple[int, ...], int, int
            ]
        ],
        object,
    ],
    *,
    history: int,
) -> TemporalClosureRow:
    history = int(history)
    if history <= 0:
        raise ValueError(history)
    transitions: list[tuple[object, object]] = []
    for orbit in orbits:
        symbols = tuple((row[3], feature(row)) for row in orbit)
        for index in range(history - 1, len(symbols) - 1):
            current = symbols[index - history + 1 : index + 1]
            nxt = symbols[index + 1]
            transitions.append((current, nxt))
    key_count, conflicts = _successor_conflict_counts(transitions)
    return TemporalClosureRow(history, key_count, conflicts)


@exact_oracle()
def _single_jet_multi_seed_closure(
    seed_start: int,
    seed_stop: int,
    steps: int,
    *,
    order: int,
    modulus: int,
    base: int,
) -> tuple[int, int]:
    divisor = cyclotomic_power_coefficients(int(order), 1)
    transitions: list[tuple[object, object]] = []
    for seed in range(int(seed_start), int(seed_stop) + 1):
        orbit = _reverse_orbit(seed, int(steps), int(base))
        for current, nxt in pairwise(orbit):
            key = (
                current[3],
                polynomial_remainder_monic(current[2], divisor, modulus=int(modulus)),
            )
            next_key = (
                nxt[3],
                polynomial_remainder_monic(nxt[2], divisor, modulus=int(modulus)),
            )
            transitions.append((key, next_key))
    return _successor_conflict_counts(transitions)


@exact_oracle()
def reverse_temporal_observer_profile(
    *, base: int = 10
) -> ReverseTemporalObserverProfile:
    """Reject short-history and apparent single-jet closure on independent seeds.

    The short-memory test deliberately uses the *already canonical* base-1 and
    base+1 residue channels rather than inventing parallel Phi_1/Phi_2 names.
    A higher-order Phi_11/mod-16 jet is included as an overfitting guard: it
    appears closed on a contiguous training window but fails on a disjoint
    holdout window, so it is not promoted into compiler state.
    """
    seed_start, seed_stop, steps = 1, 300, 32
    orbits = tuple(
        _reverse_orbit(seed, steps, base) for seed in range(seed_start, seed_stop + 1)
    )
    minus = tuple(
        _temporal_feature_closure(orbits, lambda row: row[5], history=h)
        for h in (1, 2, 3)
    )
    pm = tuple(
        _temporal_feature_closure(orbits, lambda row: (row[5], row[6]), history=h)
        for h in (1, 2, 3)
    )

    order, modulus = 11, 16
    training_classes, training_conflicts = _single_jet_multi_seed_closure(
        1,
        300,
        64,
        order=order,
        modulus=modulus,
        base=base,
    )
    holdout_classes, holdout_conflicts = _single_jet_multi_seed_closure(
        10_000,
        10_350,
        32,
        order=order,
        modulus=modulus,
        base=base,
    )
    return ReverseTemporalObserverProfile(
        seed_start,
        seed_stop,
        steps,
        minus,
        pm,
        order,
        modulus,
        300,
        64,
        training_classes,
        training_conflicts,
        10_000,
        10_350,
        32,
        holdout_classes,
        holdout_conflicts,
    )


@exact_oracle()
def reverse_residual_successor_collisions(
    *, base: int = 10
) -> tuple[ReverseResidualSuccessorCollision, ...]:
    """Return fixed witnesses rejecting the strongest proposed residuals.

    These are proof-only exact occurrences.  Keeping the witnesses fixed makes
    the regression cheap and prevents a future production carrier from being
    accepted merely because a broad empirical search changed its sample.
    """
    if int(base) != 10:
        raise ValueError("fixed residual closure witnesses are decimal")

    def row(
        seed: int, step: int
    ) -> tuple[
        tuple[int, int, tuple[int, ...], tuple[object, ...], tuple[int, ...], int, int],
        tuple[int, int, tuple[int, ...], tuple[object, ...], tuple[int, ...], int, int],
    ]:
        orbit = _reverse_orbit(seed, step + 1, 10)
        return orbit[step], orbit[step + 1]

    def collision(
        observer: str,
        first_seed: int,
        first_step: int,
        second_seed: int,
        second_step: int,
        key: Callable[
            [
                tuple[
                    int,
                    int,
                    tuple[int, ...],
                    tuple[object, ...],
                    tuple[int, ...],
                    int,
                    int,
                ]
            ],
            object,
        ],
    ) -> ReverseResidualSuccessorCollision:
        first, first_next = row(first_seed, first_step)
        second, second_next = row(second_seed, second_step)
        shared = key(first)
        if shared != key(second) or key(first_next) == key(second_next):
            raise AssertionError(f"stale reverse residual collision: {observer}")
        return ReverseResidualSuccessorCollision(
            observer,
            first_seed,
            first_step,
            first[1],
            first[2],
            second_seed,
            second_step,
            second[1],
            second[2],
            shared,
            key(first_next),
            key(second_next),
        )

    divisor = cyclotomic_power_coefficients(11, 1)
    return (
        collision(
            "carry+base-minus", 190, 2, 191, 1, lambda current: (current[3], current[5])
        ),
        collision(
            "carry+base-plus-minus",
            190,
            9,
            193,
            7,
            lambda current: (current[3], current[5], current[6]),
        ),
        collision(
            "carry+phi11-mod16",
            10_158,
            23,
            10_299,
            26,
            lambda current: (
                current[3],
                polynomial_remainder_monic(current[2], divisor, modulus=16),
            ),
        ),
    )


@exact_oracle()
def reverse_cyclotomic_observer_profile(
    seed: int = 196,
    *,
    steps: int = 256,
    base: int = 10,
) -> ReverseCyclotomicObserverProfile:
    """Search small single cyclotomic jets against the known 196 collision.

    A candidate counts as closed only when the *combined* state
    ``(CarryResetSignature, jet)`` determines its own next combined state.  A
    zero-conflict but trajectory-injective coordinate is reported honestly as a
    re-encoding rather than a quotient.
    """
    orbit = _reverse_orbit(seed, steps, base)

    # Find the first exact same-action / different-next-action collision.
    first_for_action: dict[object, int] = {}
    collision = None
    for index in range(len(orbit) - 1):
        action = orbit[index][3]
        prior = first_for_action.get(action)
        if prior is not None and orbit[prior + 1][3] != orbit[index + 1][3]:
            collision = (prior, index)
            break
        first_for_action.setdefault(action, index)
    if collision is None:
        raise AssertionError(
            "expected reverse-196 carry-action collision was not found"
        )
    first, second = collision

    candidates: list[ReverseJetCandidate] = []
    for order in range(1, 13):
        for power in (1, 2, 3):
            # Keep the bounded search genuinely small rather than allowing a
            # high-degree jet to reconstruct the whole pair field by definition.
            if len(cyclotomic_power_coefficients(order, power)) - 1 > 12:
                continue
            divisor = cyclotomic_power_coefficients(order, power)
            for modulus in (2, 4, 8, 16):
                keys: list[tuple[object, tuple[int, ...]]] = []
                for row in orbit:
                    residue = polynomial_remainder_monic(
                        row[2],
                        divisor,
                        modulus=modulus,
                    )
                    keys.append((row[3], residue))
                classes, conflicts = _closure(keys)
                candidates.append(
                    ReverseJetCandidate(order, power, modulus, classes, conflicts)
                )

    closed = [candidate for candidate in candidates if not candidate.conflicts]
    noninjective = [candidate for candidate in closed if candidate.classes < steps]
    best = tuple(
        sorted(
            candidates,
            key=lambda item: (
                item.conflicts,
                item.classes,
                item.modulus,
                item.order,
                item.power,
            ),
        )[:12]
    )
    neighbor_minus, neighbor_pm = _neighbor_residue_conflicts(base=base)

    m = base - 1
    p1 = tuple(sum(orbit[index][2]) % m for index in collision)
    residues = tuple(orbit[index][5] for index in collision)
    return ReverseCyclotomicObserverProfile(
        int(seed),
        int(steps),
        collision,
        orbit[first][3] == orbit[second][3],
        orbit[first][4] == orbit[second][4],
        (int(residues[0]), int(residues[1])),
        (int(p1[0]), int(p1[1])),
        residues[0] != residues[1],
        len(candidates),
        len(closed),
        len(noninjective),
        min((candidate.classes for candidate in closed), default=None),
        neighbor_minus,
        neighbor_pm,
        best,
    )


@exact_oracle()
def mersenne_phi_sign_profile(exponent: int) -> MersennePhiSignProfile:
    """Show that ``Phi_p mod 2`` is exactly the Mersenne sign/complement quotient."""
    p = int(exponent)
    if p < 2:
        raise ValueError(p)
    modulus = (1 << p) - 1
    phi_keys: list[tuple[int, ...]] = []
    sign_keys: list[int] = []
    for state in range(modulus):
        digits = digits_lsd(state, 2, p)
        phi_keys.append(
            CyclotomicDigitBlock.from_coefficients(
                digits,
                order=p,
                modulus=2,
                length=p,
            ).residue
        )
        sign_keys.append(min(state, (-state) % modulus))

    phi_to_sign: dict[tuple[int, ...], int] = {}
    sign_to_phi: dict[int, tuple[int, ...]] = {}
    same: bool = True
    for phi, sign in zip(phi_keys, sign_keys, strict=True):
        if phi in phi_to_sign:
            same &= phi_to_sign[phi] == sign
        else:
            phi_to_sign[phi] = sign
        if sign in sign_to_phi:
            same &= sign_to_phi[sign] == phi
        else:
            sign_to_phi[sign] = phi

    target_ok = next_ok = True
    outputs: dict[tuple[int, ...], bool] = {}
    successors: dict[tuple[int, ...], tuple[int, ...]] = {}
    for state, key in enumerate(phi_keys):
        output = state == 0
        nxt = phi_keys[(state * state - 2) % modulus]
        if key in outputs:
            target_ok &= outputs[key] == output
            next_ok &= successors[key] == nxt
        else:
            outputs[key] = output
            successors[key] = nxt
    return MersennePhiSignProfile(
        p,
        modulus,
        len(set(phi_keys)),
        len(set(sign_keys)),
        bool(same),
        bool(target_ok),
        bool(next_ok),
    )


@exact_oracle()
def special_sign_quotient_work_profile(
    family: str,
    parameter: int,
) -> SignQuotientWorkProfile:
    """Compare the old unquotiented digit work with the canonical sign quotient."""
    from devtools.verification.oracles.digit_power import (
        lucas_lehmer_digit_field,
        pepin_digit_field,
    )

    family = str(family)
    parameter = int(parameter)
    baseline_mul = baseline_add = 0
    if family == "mersenne":
        p = parameter
        modulus = (1 << p) - 1
        residue = 4 % modulus
        for _ in range(max(0, p - 2)):
            projection = cyclic_binary_square_add_projection(residue, p, -2)
            residue = projection.residue
            baseline_mul += projection.convolution.scalar_multiplications
            baseline_add += projection.convolution.coefficient_additions
        quotient = lucas_lehmer_digit_field(p)
    elif family == "fermat":
        n = parameter
        width = 1 << n
        modulus = (1 << width) + 1
        residue = 3 % modulus
        for _ in range(width - 1):
            projection = negacyclic_binary_square_projection(residue, width)
            residue = projection.residue
            baseline_mul += projection.convolution.scalar_multiplications
            baseline_add += projection.convolution.coefficient_additions
        quotient = pepin_digit_field(n)
    else:
        raise ValueError(family)
    return SignQuotientWorkProfile(
        family,
        parameter,
        baseline_mul,
        quotient.karatsuba_scalar_multiplications,
        baseline_add,
        quotient.coefficient_additions,
        quotient.sign_quotient_steps,
        quotient.sign_quotient_nonzero_digits_saved,
    )


@exact_oracle()
class CyclotomicObserverMetrics(TypedDict):
    jet_unification: JetUnificationProfile
    normalization_defect: NormalizationDefectAudit
    reverse_add_196: ReverseCyclotomicObserverProfile
    reverse_temporal: ReverseTemporalObserverProfile
    mersenne_phi_sign: list[MersennePhiSignProfile]
    special_sign_quotients: list[SignQuotientObserverProfile]
    special_sign_work: list[SignQuotientWorkProfile]


def cyclotomic_observer_metrics() -> CyclotomicObserverMetrics:
    from devtools.experiments.algebra.projection_observer import (
        special_square_sign_quotient_profile,
    )

    return {
        "jet_unification": jet_unification_profile(),
        "normalization_defect": normalization_defect_audit(),
        "reverse_add_196": reverse_cyclotomic_observer_profile(),
        "reverse_temporal": reverse_temporal_observer_profile(),
        "mersenne_phi_sign": [mersenne_phi_sign_profile(p) for p in (5, 7, 11, 13)],
        "special_sign_quotients": [
            special_square_sign_quotient_profile("mersenne", p) for p in (5, 7, 11, 13)
        ]
        + [special_square_sign_quotient_profile("fermat", n) for n in (2, 3)],
        "special_sign_work": [
            special_sign_quotient_work_profile("mersenne", 31),
            special_sign_quotient_work_profile("fermat", 5),
        ],
    }


__all__ = [
    "JetUnificationProfile",
    "MersennePhiSignProfile",
    "NormalizationDefectAudit",
    "ReverseCyclotomicObserverProfile",
    "ReverseJetCandidate",
    "ReverseResidualSuccessorCollision",
    "ReverseTemporalObserverProfile",
    "SignQuotientWorkProfile",
    "TemporalClosureRow",
    "cyclotomic_observer_metrics",
    "jet_unification_profile",
    "mersenne_phi_sign_profile",
    "normalization_defect_audit",
    "reverse_cyclotomic_observer_profile",
    "reverse_residual_successor_collisions",
    "reverse_temporal_observer_profile",
    "special_sign_quotient_work_profile",
]
