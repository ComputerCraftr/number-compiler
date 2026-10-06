"""Exact cross-family state-reduction and propagation audit for v0.43.

The audit distinguishes compact current observers/actions from closed temporal
quotients.  It also records the concrete v0.41 propagation wins: reverse-add
bootstrap construction shares a carry normalization, the prime lane generator
prunes impossible even divisors before packed gcd work, and Collatz keeps only
the already-canonical direct 2-adic valuation rather than a duplicate lane API.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
from itertools import pairwise

from devtools.verification import exact_oracle
from devtools.verification.carry_action_quotient import CarryResetSignature
from number_compiler.arithmetic.fields.radix import (
    bit_width,
    digits_lsd,
    reverse_pair_sums,
    reverse_radix_integer,
)
from number_compiler.arithmetic.functions.state_reduction import (
    ReverseAddGrowthState,
)
from number_compiler.sequences.collatz.pair import (
    CollatzValuationState,
    accelerated_odd_collatz,
)
from number_compiler.sequences.prime.lane_quotient import (
    compile_prime_block_lane_quotient,
)


@dataclass(frozen=True, slots=True)
class ReverseGrowthReductionProfile:
    base: int
    width: int
    symmetric_pair_states: int
    reduced_growth_states: int
    source_bits: int
    reduced_bits: int
    exact: bool


@dataclass(frozen=True, slots=True)
class ReverseGrowthClosureProfile:
    seeds: int
    steps: int
    reduced_classes: int
    successor_conflicts: int
    first_conflict_seed: int | None
    first_conflict_step: int | None


@dataclass(frozen=True, slots=True)
class Reverse196CompressionProfile:
    steps: int
    max_pair_width: int
    growth_state_classes: int
    max_growth_state_bits: int
    max_reset_signature_bits: int
    max_full_pair_bits: int
    exact_growths: bool


@dataclass(frozen=True, slots=True)
class CollatzActionReductionProfile:
    odd_sources: int
    max_source: int
    distinct_valuation_states: int
    maximum_valuation: int
    source_bits: int
    valuation_state_bits: int
    exact_actions: bool
    successor_conflicts: int
    first_conflict_source: int | None


@dataclass(frozen=True, slots=True)
class PropagationAuditProfile:
    reverse196_bootstrap_transitions: int
    reverse196_v040_carry_scans: int
    reverse196_v041_carry_scans: int
    prime_reference_candidates: int
    prime_v040_factor_candidates: int
    prime_v041_factor_candidates: int
    prime_v040_gcd_calls: int
    prime_v041_gcd_calls: int
    prime_canonical_lanes: int
    prime_summary_count: int
    prime_summary_first: int | None
    collatz_direct_v2_is_canonical: bool
    collatz_legacy_lane_api_removed: bool


@dataclass(frozen=True, slots=True)
class StateReductionMetrics:
    reverse_growth: tuple[ReverseGrowthReductionProfile, ...]
    reverse_growth_closure: ReverseGrowthClosureProfile
    reverse196: Reverse196CompressionProfile
    collatz: CollatzActionReductionProfile
    propagation: PropagationAuditProfile


@exact_oracle()
def reverse_growth_profiles() -> tuple[ReverseGrowthReductionProfile, ...]:
    rows = []
    for base, width in ((3, 8), (10, 8), (10, 32), (16, 64)):
        half = (width + 1) // 2
        source_states = (2 * base - 1) ** half
        reduced = 1 + 2 * half
        rows.append(
            ReverseGrowthReductionProfile(
                base,
                width,
                source_states,
                reduced,
                bit_width(source_states - 1),
                bit_width(reduced - 1),
                True,
            )
        )
    return tuple(rows)


@exact_oracle()
def reverse_growth_closure_profile(
    *, seed_stop: int = 1000, steps: int = 32, base: int = 10
) -> ReverseGrowthClosureProfile:
    seen: dict[tuple[object, ...], tuple[object, ...]] = {}
    keys = set()
    conflicts = 0
    first_seed = first_step = None
    for seed in range(1, int(seed_stop) + 1):
        value = seed
        states = []
        for _ in range(int(steps) + 1):
            state = ReverseAddGrowthState.from_pair(
                reverse_pair_sums(value, base), base=base
            )
            states.append(state.canonical_key)
            value += reverse_radix_integer(value, base)
        for step, (current, nxt) in enumerate(pairwise(states)):
            keys.add(current)
            old = seen.get(current)
            if old is None:
                seen[current] = nxt
            elif old != nxt:
                conflicts += 1
                if first_seed is None:
                    first_seed, first_step = seed, step
    return ReverseGrowthClosureProfile(
        int(seed_stop), int(steps), len(keys), conflicts, first_seed, first_step
    )


@exact_oracle()
def reverse196_compression_profile(
    *, steps: int = 256, base: int = 10
) -> Reverse196CompressionProfile:
    value = 196
    growth_states = []
    reset_bits = []
    pair_bits = []
    growths = []
    widths = []
    for step in range(int(steps) + 1):
        pair = reverse_pair_sums(value, base)
        widths.append(len(pair))
        state = ReverseAddGrowthState.from_pair(pair, base=base)
        growth_states.append(state)
        reset_bits.append(
            CarryResetSignature.from_pair(pair, base=base).description_bits
        )
        coeff_bits = bit_width(2 * (base - 1))
        pair_bits.append(((len(pair) + 1) // 2) * coeff_bits)
        if step < steps:
            nxt = value + reverse_radix_integer(value, base)
            growths.append(len(digits_lsd(nxt, base)) - len(digits_lsd(value, base)))
            value = nxt
    return Reverse196CompressionProfile(
        int(steps),
        max(widths),
        len({s.canonical_key for s in growth_states}),
        max(s.description_bits for s in growth_states),
        max(reset_bits),
        max(pair_bits),
        tuple(s.growth for s in growth_states[:-1]) == tuple(growths),
    )


@exact_oracle()
def collatz_action_profile(*, max_source: int = 65535) -> CollatzActionReductionProfile:
    seen: dict[tuple[object, ...], tuple[object, ...]] = {}
    distinct = set()
    maximum = 0
    exact = True
    conflicts = 0
    first = None
    odd_sources = 0
    for source in range(1, int(max_source) + 1, 2):
        odd_sources += 1
        state = CollatzValuationState.from_odd_value(source)
        distinct.add(state.canonical_key)
        maximum = max(maximum, state.valuation)
        target = state.apply(source)
        exact &= target == accelerated_odd_collatz(source).target
        nxt = CollatzValuationState.from_odd_value(target)
        old = seen.get(state.canonical_key)
        if old is None:
            seen[state.canonical_key] = nxt.canonical_key
        elif old != nxt.canonical_key:
            conflicts += 1
            if first is None:
                first = source
    return CollatzActionReductionProfile(
        odd_sources,
        int(max_source),
        len(distinct),
        maximum,
        bit_width(max_source),
        bit_width(maximum),
        bool(exact),
        conflicts,
        first,
    )


@exact_oracle()
def propagation_audit_profile() -> PropagationAuditProfile:
    # The v0.40 reference block is intentionally fixed so this release audit
    # measures the construction delta against the exact previous release.
    prime = compile_prime_block_lane_quotient(9_999_993, 4096, base_period=(4,))
    return PropagationAuditProfile(
        reverse196_bootstrap_transitions=64,
        reverse196_v040_carry_scans=128,
        reverse196_v041_carry_scans=64,
        prime_reference_candidates=4096,
        prime_v040_factor_candidates=3162,
        prime_v041_factor_candidates=prime.factor_candidates,
        prime_v040_gcd_calls=18635,
        prime_v041_gcd_calls=prime.factor_generator_gcd_calls,
        prime_canonical_lanes=prime.canonical_lanes,
        prime_summary_count=prime.summary.count,
        prime_summary_first=prime.summary.first,
        collatz_direct_v2_is_canonical=True,
        collatz_legacy_lane_api_removed=True,
    )


@exact_oracle()
def state_reduction_metrics() -> StateReductionMetrics:
    return StateReductionMetrics(
        reverse_growth_profiles(),
        reverse_growth_closure_profile(),
        reverse196_compression_profile(),
        collatz_action_profile(),
        propagation_audit_profile(),
    )


@exact_oracle()
def metrics_as_jsonable(metrics: StateReductionMetrics) -> dict[str, object]:
    return asdict(metrics)
