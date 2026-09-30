"""Cross-family closure audit for algebra on projection *outputs*.

This research layer asks whether a compact coordinate of a projection value is
itself closed under the next projection step.  Exact state merges require both
present target separation and deterministic successor feature classes.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from typing import TypedDict

from devtools.experiments.algebra.projection_observer import (
    fermat_squaring_observer_profile,
    mersenne_lucas_observer_profile,
)
from devtools.verification import exact_oracle
from devtools.verification.carry_action_quotient import CarryResetSignature
from number_compiler.arithmetic.fields.projection_field import (
    projection_field_summary_from_values,
)
from number_compiler.arithmetic.fields.radix import (
    digits_lsd,
    symbol_runs,
    value_from_lsd_digits,
)
from number_compiler.sequences.collatz.pair import (
    collatz_slab_mod_odd,
    collatz_valuation_itinerary,
    valuation_projection_from_runs,
)
from number_compiler.sequences.prime.coordinates import project_least_factor_field
from number_compiler.sequences.prime.lane_quotient import (
    canonical_prime_base_period,
    compile_prime_block_lane_quotient,
)


@dataclass(frozen=True, slots=True)
class ReverseAddProjectionFieldProfile:
    seed: int
    steps: int
    exact_actions: int
    repeated_actions: int
    conflicting_next_actions: int
    transformed_feature_conflicts: int


@dataclass(frozen=True, slots=True)
class CollatzProjectionFieldProfile:
    seed: int
    valuation_symbols: int
    valuation_runs: int
    valuation_sum: int
    raw_symbol_bits: int
    rle_description_bits: int
    theorem_channel_bits: int
    exact_slab_bits: int
    exact_slab_compositions: int
    odd_residue_maps: tuple[tuple[int, int, int], ...]


@dataclass(frozen=True, slots=True)
class PrimeProjectionFieldProfile:
    start: int
    length: int
    primes: int
    first: int | None
    least_factor_runs: int
    least_factor_rle_bits: int
    boolean_theorem_bits: int
    projection_field_compositions: int
    decision_nodes: int
    charged_projection_work: int


@dataclass(frozen=True, slots=True)
class SpecialProjectionClassProfile:
    family: str
    parameter: int
    modulus: int
    observer_classes: int
    observer_bits: int
    initial_class: int | None


@dataclass(frozen=True, slots=True)
class SpecialDigitProjectionFeatureProfile:
    family: str
    parameter: int
    feature: str
    modulus: int
    feature_classes: int
    target_separating: bool
    next_closed: bool
    injective: bool


@exact_oracle()
def _reverse_step(value: int, base: int) -> int:
    digits = digits_lsd(value, base)
    return int(value) + value_from_lsd_digits(tuple(reversed(digits)), base)


@exact_oracle()
def _reverse_action(value: int, base: int) -> CarryResetSignature:
    d = digits_lsd(value, base)
    pair = tuple(d[i] + d[-1 - i] for i in range(len(d)))
    return CarryResetSignature.from_pair(pair, base=base)


@exact_oracle()
def reverse_add_projection_field_profile(
    seed: int = 196, *, steps: int = 256, base: int = 10
) -> ReverseAddProjectionFieldProfile:
    value = int(seed)
    actions = []
    features = []
    for _ in range(int(steps) + 1):
        action = _reverse_action(value, base)
        actions.append(action.canonical_key)
        # Encode reset boundary values as a ternary field: 0=CONST0, 1=ID, 2=CONST1.
        d = digits_lsd(value, base)
        pair = tuple(d[i] + d[-1 - i] for i in range(len(d)))
        t = base - 1
        threshold = tuple(0 if x < t else 1 if x == t else 2 for x in pair)
        f = projection_field_summary_from_values(threshold, degree=4, modulus=32)
        features.append(
            (
                f.primary_jet.canonical_key,
                f.binomial_moments.canonical_key,
                tuple(x.canonical_key for x in f.cyclotomic_projection),
            )
        )
        value = _reverse_step(value, base)
    current = actions[:-1]
    nxt = actions[1:]
    by: dict[tuple[object, ...], tuple[object, ...]] = {}
    conflicts = 0
    for a, b in zip(current, nxt):
        old = by.setdefault(a, b)
        if old != b:
            conflicts += 1
    byf: dict[tuple[object, ...], tuple[object, ...]] = {}
    fconf = 0
    for a, b in zip(features[:-1], actions[1:]):
        old = byf.setdefault(a, b)
        if old != b:
            fconf += 1
    return ReverseAddProjectionFieldProfile(
        int(seed),
        int(steps),
        len(set(current)),
        len(current) - len(set(current)),
        conflicts,
        fconf,
    )


@exact_oracle()
def collatz_projection_field_profile(
    seed: int, *, max_odd_steps: int = 10000
) -> CollatzProjectionFieldProfile:
    vals = collatz_valuation_itinerary(seed, max_odd_steps=max_odd_steps)
    runs = symbol_runs(vals)
    summary = projection_field_summary_from_values(vals, degree=4, modulus=32)
    block = valuation_projection_from_runs(runs)
    raw_bits = sum(max(1, int(v).bit_length()) for v in vals)
    residue_maps = []
    for m in (3, 5, 7, 11):
        a = collatz_slab_mod_odd(block.slab, m)
        residue_maps.append((m, a.multiplier, a.offset))
    return CollatzProjectionFieldProfile(
        int(seed),
        len(vals),
        len(runs),
        sum(vals),
        raw_bits,
        summary.word_description_bits,
        summary.theorem_description_bits,
        block.description_bits,
        block.compositions,
        tuple(residue_maps),
    )


@exact_oracle()
def prime_projection_field_profile(
    start: int, length: int
) -> PrimeProjectionFieldProfile:
    least = project_least_factor_field(start, length)
    least_summary = projection_field_summary_from_values(
        least.labels, degree=4, modulus=32
    )
    q = compile_prime_block_lane_quotient(
        start,
        length,
        base_period=canonical_prime_base_period(length),
        projection_algebra=True,
    )
    assert q.primary_jet is not None
    theorem_bits = q.primary_jet.description_bits
    if q.binomial_moments is not None:
        theorem_bits += q.binomial_moments.description_bits
    theorem_bits += sum(x.description_bits for x in q.cyclotomic_projection)
    return PrimeProjectionFieldProfile(
        int(start),
        int(length),
        q.summary.count,
        q.summary.first,
        least_summary.run_count,
        least_summary.word_description_bits,
        theorem_bits,
        q.projection_field_compositions,
        q.decision_nodes,
        q.projection_work,
    )


@exact_oracle()
def special_projection_class_profile(
    family: str, parameter: int
) -> SpecialProjectionClassProfile:
    if family == "fermat":
        p = fermat_squaring_observer_profile(parameter)
        modulus = (1 << (1 << parameter)) + 1
    elif family == "mersenne":
        p = mersenne_lucas_observer_profile(parameter)
        modulus = (1 << parameter) - 1
    else:
        raise ValueError(family)
    return SpecialProjectionClassProfile(
        family,
        int(parameter),
        modulus,
        p.observer_classes,
        p.observer_bits,
        p.initial_class,
    )


@exact_oracle()
def _feature_key(value: int, width: int, names: Sequence[str]) -> tuple[object, ...]:
    digits = digits_lsd(value, 2, width)
    summary = projection_field_summary_from_values(digits, degree=4, modulus=32)
    out = []
    for name in names:
        if name == "primary":
            out.append(summary.primary_jet.jet)
        elif name == "binomial":
            out.append(summary.binomial_moments.moments)
        elif name.startswith("phi"):
            order = int(name[3:])
            out.append(
                next(
                    x.residue for x in summary.cyclotomic_projection if x.order == order
                )
            )
        else:
            raise ValueError(name)
    return tuple(out)


@exact_oracle()
def special_digit_projection_feature_profile(
    family: str, parameter: int, feature: Sequence[str] | str
) -> SpecialDigitProjectionFeatureProfile:
    names = (feature,) if isinstance(feature, str) else tuple(feature)
    if family == "fermat":
        modulus = (1 << (1 << int(parameter))) + 1

        def transition(x: int) -> int:
            return (x * x) % modulus

        def target(x: int) -> bool:
            return x == modulus - 1
    elif family == "mersenne":
        modulus = (1 << int(parameter)) - 1

        def transition(x: int) -> int:
            return (x * x - 2) % modulus

        def target(x: int) -> bool:
            return x == 0
    else:
        raise ValueError(family)
    width = modulus.bit_length()
    by: dict[tuple[object, ...], tuple[bool, tuple[object, ...]]] = {}
    target_ok = True
    next_ok = True
    keys = set()
    for state in range(modulus):
        key = _feature_key(state, width, names)
        keys.add(key)
        obs = target(state)
        nxt = _feature_key(transition(state), width, names)
        old = by.get(key)
        if old is None:
            by[key] = (obs, nxt)
        else:
            target_ok &= old[0] == obs
            next_ok &= old[1] == nxt
    label = "+".join(names)
    return SpecialDigitProjectionFeatureProfile(
        family,
        int(parameter),
        label,
        modulus,
        len(keys),
        bool(target_ok),
        bool(next_ok),
        len(keys) == modulus,
    )


class ProjectionFieldMetrics(TypedDict):
    reverse_add: list[ReverseAddProjectionFieldProfile]
    collatz: list[CollatzProjectionFieldProfile]
    primes: list[PrimeProjectionFieldProfile]
    special_observers: list[SpecialProjectionClassProfile]
    special_digit_features: list[SpecialDigitProjectionFeatureProfile]


@exact_oracle()
def projection_field_metrics() -> ProjectionFieldMetrics:
    return {
        "reverse_add": [
            reverse_add_projection_field_profile(seed) for seed in (195, 196, 197)
        ],
        "collatz": [
            collatz_projection_field_profile(seed)
            for seed in (27, 97, 871, 6171, 837799)
        ],
        "primes": [
            prime_projection_field_profile(9_999_993, L) for L in (64, 256, 1024, 4096)
        ],
        "special_observers": [
            special_projection_class_profile("fermat", n) for n in (1, 2, 3, 4)
        ]
        + [special_projection_class_profile("mersenne", p) for p in (3, 5, 7, 11, 13)],
        "special_digit_features": [
            special_digit_projection_feature_profile("fermat", n, f)
            for n in (1, 2, 3)
            for f in ("phi2", "phi4", ("primary", "binomial", "phi2", "phi4", "phi8"))
        ]
        + [
            special_digit_projection_feature_profile("mersenne", p, f)
            for p in (3, 5, 7)
            for f in ("phi2", "phi4", ("primary", "binomial", "phi2", "phi4", "phi8"))
        ],
    }


__all__ = [
    "CollatzProjectionFieldProfile",
    "PrimeProjectionFieldProfile",
    "ReverseAddProjectionFieldProfile",
    "SpecialDigitProjectionFeatureProfile",
    "SpecialProjectionClassProfile",
    "collatz_projection_field_profile",
    "prime_projection_field_profile",
    "projection_field_metrics",
    "reverse_add_projection_field_profile",
    "special_digit_projection_feature_profile",
    "special_projection_class_profile",
]
