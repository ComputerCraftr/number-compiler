"""Baby/giant behavioral quotient audit for the special-factor bend locus.

This module executes the next quotient experiment after the v0.53.0
constraint-pullback release.  The factor-window bend sequence for one hidden
prime component q|N is a translated delta comb in the admissible slot variable:

    b(m) = 1  iff  1 + C*m == 0 (mod q).

The proposed dyadic behavioral quotient is refined exactly by

    P_(2h) = P_h ^ (T^h)^* P_h,

where T is the unit slot shift.  Two observer choices are audited:

* the complete within-block bend trace, required if arbitrary remainders are to
  remain answerable; and
* the much weaker terminal bit "this h-slot block contains a bend".

The exact bounded result is a useful lower bound.  For a single q-periodic
translated delta, the trace partition has min(h+1,q) classes.  The terminal
block-hit observer is even less useful as a powered quotient: for 1<=h<q its
successor-closed Moore machine has q classes (q is prime in the controls).
Thus the raw bend phase cannot be made polylogarithmic merely by pulling the
same pointwise observer backward through dyadic blocks.

The existing Strassen/Karatsuba baby/giant evaluator remains useful for a fixed
window.  This module therefore also exposes a memoized terminal packet: once a
specific (family, parameter, start, span) window has been evaluated, later
output/theorem observers reuse that exact packet rather than redoing the
multipoint work.  The memo is research-only because constructing a previously
unseen packet still costs the sublinear-but-non-polylogarithmic bend evaluator.

No hidden factor is accepted by production.  Factor-backed q is used here only
as bounded truth to measure the exact minimal behavioral state and to prevent a
sampled/endpoint quotient from being promoted as a theorem.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, TypeVar

from devtools.experiments.algebra.math_support import ceil_sqrt
from devtools.experiments.algebra.residue_refined_bend import (
    FastMultipointBendAudit,
    fast_multipoint_bend_audit,
    fast_multipoint_support_decision,
)
from devtools.experiments.power_numbers.special_transverse_jet import (
    SpecialJetProgressionSpec,
    first_special_transverse_singularity,
)
from number_compiler.arithmetic.functions.finite_unary import (
    analyze_observer,
    minimize_unary_moore,
)
from number_compiler.sequences.prime.set import jacobi_symbol
from devtools.verification.partition_refinement import parent_split_count


PacketT = TypeVar("PacketT")


def _memoized_packet(
    cache: dict[tuple[str, int, int, int], PacketT],
    key: tuple[str, int, int, int],
    build: Callable[[], PacketT],
    hits: int,
    misses: int,
) -> tuple[PacketT, int, int]:
    old = cache.get(key)
    if old is not None:
        return old, hits + 1, misses
    packet = build()
    cache[key] = packet
    return packet, hits, misses + 1


def _next_power_of_two_at_least(value: int) -> int:
    value = max(1, int(value))
    return 1 << (value - 1).bit_length()


def _canonicalize(
    signatures: tuple[int, ...]
    | tuple[tuple[int, ...], ...]
    | tuple[tuple[int, int], ...],
) -> tuple[int, ...]:
    ids: dict[object, int] = {}
    return tuple(ids.setdefault(signature, len(ids)) for signature in signatures)


def _memo_key(
    family: str, parameter: int, start: int, span: int
) -> tuple[str, int, int, int]:
    return str(family), int(parameter), int(start), int(span)


def _partition_equivalent_ids(left: tuple[int, ...], right: tuple[int, ...]) -> bool:
    if len(left) != len(right):
        return False
    l2r: dict[int, int] = {}
    r2l: dict[int, int] = {}
    for a, b in zip(left, right, strict=True):
        if l2r.setdefault(a, b) != b or r2l.setdefault(b, a) != a:
            return False
    return True


def _class_sizes(class_ids: tuple[int, ...]) -> tuple[int, ...]:
    counts: dict[int, int] = {}
    for cls in class_ids:
        counts[cls] = counts.get(cls, 0) + 1
    return tuple(sorted(counts.values(), reverse=True))


def _trace_signatures(
    period: int, bend_residue: int, horizon: int
) -> tuple[tuple[int, ...], ...]:
    period, bend_residue, horizon = int(period), int(bend_residue), int(horizon)
    if period <= 1 or not 0 <= bend_residue < period or horizon <= 0:
        raise ValueError((period, bend_residue, horizon))
    return tuple(
        tuple(
            int((state + offset) % period == bend_residue) for offset in range(horizon)
        )
        for state in range(period)
    )


def _block_hit(period: int, bend_residue: int, start_state: int, horizon: int) -> bool:
    period, bend_residue = int(period), int(bend_residue)
    start_state, horizon = int(start_state), int(horizon)
    if horizon >= period:
        return True
    distance = (bend_residue - start_state) % period
    return distance < horizon


@dataclass(frozen=True, slots=True)
class DyadicBendPartitionRow:
    horizon: int
    classes: int
    expected_classes: int
    new_classes: int
    parent_classes_split: int
    largest_class: int
    pullback_exact: bool
    formula_exact: bool
    closed_distance_formula_exact: bool
    symbolic_rule_count: int
    no_bend_doubling: bool


@dataclass(frozen=True, slots=True)
class BabyGiantPhaseAudit:
    period: int
    baby_width: int
    giant_buckets: int
    encoded_classes: int
    exact_injective: bool
    structural_entries: int
    state_bits_upper_bound: int
    hidden_factor_required: bool
    is_behavioral_quotient: bool


@dataclass(frozen=True, slots=True)
class BehavioralBendQuotientAudit:
    family: str
    parameter: int
    modulus: int
    stride: int
    candidate_window: int
    hidden_factor: int
    bend_residue: int
    first_bend_slot: int
    dyadic_rows: tuple[DyadicBendPartitionRow, ...]
    candidate_window_trace_classes: int
    candidate_window_trace_formula_exact: bool
    candidate_window_block_hit_classes: int
    candidate_window_block_hit_expected: int
    source_hit_observer_classes: int
    source_hit_observer_successor_conflicts: int
    source_hit_observer_successor_closed: bool
    no_trace_closure_before_candidate_window: bool
    one_parent_split_per_unsaturated_doubling: bool
    symbolic_partition_grammar_constant: bool
    hidden_period_needed_for_distance_coordinate: bool
    raw_trace_polylogarithmic: bool
    block_hit_powered_polylogarithmic: bool
    baby_giant_phase: BabyGiantPhaseAudit
    production_promotable: bool


@dataclass(frozen=True, slots=True)
class FixedWindowBendPacket:
    family: str
    parameter: int
    start: int
    span: int
    modulus: int
    product_mod_n: int
    support_gcd: int
    status: str
    first_bend_slot: int | None
    first_bend_gcd: int
    first_bend_distance: int | None
    first_bend_dirichlet_character: int | None
    character_constant: int | None
    block_locator_gcds: int
    leaf_locator_gcds: int
    direct_control_evaluated: bool
    baby_width: int
    giant_blocks: int
    structural_state_entries: int
    charged_total_ring_ops: int

    @classmethod
    def from_audit(cls, audit: FastMultipointBendAudit) -> FixedWindowBendPacket:
        support = int(audit.bend_support_gcd)
        status = (
            "CLEAR" if support == 1 else "FULL" if support == audit.modulus else "SPLIT"
        )
        first_slot = audit.first_bend_slot
        first_gcd = int(audit.first_bend_gcd)
        if support == 1 and first_slot is not None:
            raise AssertionError((audit, first_slot, first_gcd))
        if support != 1 and first_slot is None:
            raise ValueError(
                "FastMultipointBendAudit must be constructed with locate_first_bend=True "
                "before building a FixedWindowBendPacket"
            )
        distance = None if first_slot is None else first_slot - audit.start
        character = character_constant = None
        if first_slot is not None and audit.start == 1:
            spec = SpecialJetProgressionSpec.build(audit.family, audit.parameter)
            slot_value = spec.slot_value(first_slot)
            # At a prefix's first supported slot, equality gcd(N,q)=q proves q
            # is the smallest special-form prime divisor: a composite q would
            # contain a smaller divisor of N whose own admissible slot appeared
            # earlier.  Only under that proof may the slot character be treated
            # as a genuine local factor character.
            if first_gcd == slot_value:
                character_constant = 3 if audit.family == "fermat" else 12
                character = jacobi_symbol(character_constant, first_gcd)
        return cls(
            audit.family,
            audit.parameter,
            audit.start,
            audit.span,
            audit.modulus,
            audit.reconstructed_product,
            support,
            status,
            first_slot,
            first_gcd,
            distance,
            character,
            character_constant,
            audit.block_locator_gcds,
            audit.leaf_locator_gcds,
            audit.direct_control_evaluated,
            audit.baby_width,
            audit.full_blocks,
            audit.structural_state_entries,
            audit.charged_total_ring_ops,
        )


@dataclass(frozen=True, slots=True)
class FixedWindowSupportPacket:
    """Minimal packet for an output that only distinguishes unit/nonunit support."""

    family: str
    parameter: int
    start: int
    span: int
    modulus: int
    support_gcd: int
    status: str
    final_support_gcds: int
    split_descent_gcds: int
    direct_control_evaluated: bool
    charged_total_ring_ops: int

    @property
    def nonunit(self) -> bool:
        return self.support_gcd > 1


class BabyGiantSupportPacketMemo:
    """Memoize the output-relative support decision without factor extraction."""

    __slots__ = ("_cache", "hits", "misses")

    def __init__(self) -> None:
        self._cache: dict[tuple[str, int, int, int], FixedWindowSupportPacket] = {}
        self.hits = 0
        self.misses = 0

    def evaluate(
        self, family: str, parameter: int, *, start: int, span: int
    ) -> FixedWindowSupportPacket:
        key = _memo_key(family, parameter, start, span)

        def build() -> FixedWindowSupportPacket:
            audit = fast_multipoint_support_decision(
                key[0], key[1], start=key[2], span=key[3]
            )
            support = int(audit.bend_support_gcd)
            return FixedWindowSupportPacket(
                audit.family,
                audit.parameter,
                audit.start,
                audit.span,
                audit.modulus,
                support,
                "CLEAR" if support == 1 else "NONUNIT",
                audit.final_support_gcds,
                audit.split_descent_gcds,
                audit.direct_control_evaluated,
                audit.charged_total_ring_ops,
            )

        packet, self.hits, self.misses = _memoized_packet(
            self._cache, key, build, self.hits, self.misses
        )
        return packet


class BabyGiantBendPacketMemo:
    """Research memo for exact fixed-window BSGS packets.

    The cache removes duplicated work across repeated observers of the *same*
    window.  It deliberately does not pretend that an unseen translated window
    can be obtained by a constant-size successor action.
    """

    __slots__ = ("_cache", "hits", "misses")

    def __init__(self) -> None:
        self._cache: dict[tuple[str, int, int, int], FixedWindowBendPacket] = {}
        self.hits = 0
        self.misses = 0

    @property
    def size(self) -> int:
        return len(self._cache)

    def evaluate(
        self, family: str, parameter: int, *, start: int, span: int
    ) -> FixedWindowBendPacket:
        key = _memo_key(family, parameter, start, span)

        def build() -> FixedWindowBendPacket:
            audit = fast_multipoint_bend_audit(
                key[0],
                key[1],
                start=key[2],
                span=key[3],
                locate_first_bend=True,
                include_direct_control=False,
            )
            return FixedWindowBendPacket.from_audit(audit)

        packet, self.hits, self.misses = _memoized_packet(
            self._cache, key, build, self.hits, self.misses
        )
        return packet


def closed_trace_class(period: int, bend_residue: int, state: int, horizon: int) -> int:
    """Closed class code for the h-step translated-delta trace partition.

    Before the first full hidden period is covered, the complete trace is
    determined by the distance ``d`` to the next bend: offsets ``d<h`` are
    distinct and every farther state belongs to one unresolved class ``h``.
    Once ``h>=q`` every phase is distinguished, so the exact code is ``d``.

    This formula is a compact *truth-side* quotient description.  Applying it
    to an unfactored candidate still requires q and the bend residue; that
    source-coordinate problem is kept explicit rather than hidden in the
    formula.
    """
    period, bend_residue, state, horizon = map(
        int, (period, bend_residue, state, horizon)
    )
    if (
        period <= 1
        or not 0 <= bend_residue < period
        or not 0 <= state < period
        or horizon <= 0
    ):
        raise ValueError((period, bend_residue, state, horizon))
    distance = (bend_residue - state) % period
    return distance if horizon >= period or distance < horizon else horizon


def _dyadic_trace_partition_rows(
    period: int, bend_residue: int, limit: int
) -> tuple[DyadicBendPartitionRow, ...]:
    period, bend_residue, limit = int(period), int(bend_residue), int(limit)
    base_outputs = tuple(int(state == bend_residue) for state in range(period))
    classes = _canonicalize(base_outputs)
    horizon = 1
    rows: list[DyadicBendPartitionRow] = []
    previous_count = 1
    while horizon <= limit:
        count = len(set(classes))
        expected = min(horizon + 1, period)
        sizes = _class_sizes(classes)
        if horizon == 1:
            parent_split = 1
            pullback_exact = classes == _canonicalize(
                _trace_signatures(period, bend_residue, horizon)
            )
        else:
            # Recover the parent partition by rebuilding exactly at h/2.  The
            # periods are <=641 on the bounded controls, so this remains a
            # transparent truth audit rather than hidden scalable work.
            parent_trace = _trace_signatures(period, bend_residue, horizon // 2)
            parent = _canonicalize(parent_trace)
            parent_split = parent_split_count(parent, classes)
            pullback_exact = classes == _canonicalize(
                _trace_signatures(period, bend_residue, horizon)
            )
        closed = tuple(
            closed_trace_class(period, bend_residue, state, horizon)
            for state in range(period)
        )
        rows.append(
            DyadicBendPartitionRow(
                horizon,
                count,
                expected,
                count - previous_count,
                parent_split,
                sizes[0],
                pullback_exact,
                count == expected,
                _partition_equivalent_ids(classes, closed),
                1,
                count == previous_count,
            )
        )
        if horizon == limit:
            break
        next_horizon = horizon * 2
        if next_horizon > limit:
            break
        signatures = tuple(
            (classes[state], classes[(state + horizon) % period])
            for state in range(period)
        )
        classes = _canonicalize(signatures)
        previous_count = count
        horizon = next_horizon
    return tuple(rows)


def _block_hit_moore_classes(period: int, bend_residue: int, horizon: int) -> int:
    period, bend_residue, horizon = int(period), int(bend_residue), int(horizon)
    successors = tuple((state + horizon) % period for state in range(period))
    outputs = tuple(
        _block_hit(period, bend_residue, state, horizon) for state in range(period)
    )
    return minimize_unary_moore(successors, outputs).classes


def _baby_giant_phase_audit(period: int) -> BabyGiantPhaseAudit:
    period = int(period)
    b = max(1, ceil_sqrt(period))
    buckets = (period + b - 1) // b
    encodings = tuple((state % b, state // b) for state in range(period))
    bits = max(1, (b - 1).bit_length()) + max(1, (buckets - 1).bit_length())
    return BabyGiantPhaseAudit(
        period,
        b,
        buckets,
        len(set(encodings)),
        len(set(encodings)) == period,
        b + buckets,
        bits,
        True,
        False,
    )


def behavioral_bend_quotient_audit(
    family: str, parameter: int
) -> BehavioralBendQuotientAudit:
    """Execute exact dyadic pullback/minimization on one factor-backed control."""
    spec = SpecialJetProgressionSpec.build(family, parameter)
    truth = first_special_transverse_singularity(family, parameter)
    if not truth.found or truth.first_slot is None or truth.denominator_gcd <= 1:
        raise ValueError("composite control with a bounded bend is required")
    q = int(truth.denominator_gcd)
    # Since q divides N and q does not divide C, the bend is one translated
    # residue class modulo q.  Use that candidate-derived arithmetic identity,
    # then verify it agrees with the first observed singular slot.
    bend_residue = (-pow(spec.stride, -1, q)) % q
    if truth.first_slot % q != bend_residue:
        raise AssertionError((truth.first_slot, bend_residue, q))

    limit = _next_power_of_two_at_least(max(spec.max_slot, q))
    rows = _dyadic_trace_partition_rows(q, bend_residue, limit)
    trace_signatures = _trace_signatures(q, bend_residue, spec.max_slot)
    trace_classes = len(set(trace_signatures))
    trace_expected = min(spec.max_slot + 1, q)

    block_classes = _block_hit_moore_classes(q, bend_residue, spec.max_slot)
    block_expected = 1 if spec.max_slot >= q else q

    source_keys = tuple(
        _block_hit(q, bend_residue, state, spec.max_slot) for state in range(q)
    )
    source_successors = tuple(
        _block_hit(q, bend_residue, (state + spec.max_slot) % q, spec.max_slot)
        for state in range(q)
    )
    observer = analyze_observer(source_keys, source_successors)

    rows_before_window = tuple(row for row in rows if row.horizon < spec.max_slot)
    no_closure_before = all(not row.no_bend_doubling for row in rows_before_window)
    return BehavioralBendQuotientAudit(
        spec.family,
        spec.parameter,
        spec.modulus,
        spec.stride,
        spec.max_slot,
        q,
        bend_residue,
        int(truth.first_slot),
        rows,
        trace_classes,
        trace_classes == trace_expected,
        block_classes,
        block_expected,
        len(set(source_keys)),
        observer.successor_conflicts,
        observer.next_closed,
        no_closure_before,
        all(row.parent_classes_split == 1 for row in rows if 1 < row.horizon < q),
        True,
        True,
        False,
        False,
        _baby_giant_phase_audit(q),
        False,
    )


@dataclass(frozen=True, slots=True)
class BehavioralBendFrontier:
    dyadic_pullback_implemented: bool
    exact_trace_formula_verified: bool
    closed_distance_partition_formula: bool
    one_parent_split_per_doubling: bool
    symbolic_partition_grammar_constant: bool
    factor_free_distance_coordinate_available: bool
    raw_trace_polylogarithmic: bool
    terminal_hit_successor_closed_small: bool
    baby_giant_phase_is_behavioral_quotient: bool
    fixed_window_bsgs_reusable: bool
    bsgs_first_bend_injector_available: bool
    bsgs_first_bend_locator_logarithmic_gcd_bound: bool
    support_only_observer_skips_factor_descent: bool
    unseen_window_polylog_constructor_available: bool
    production_promotable: bool
    status: str
    next_target: str


def behavioral_bend_frontier() -> BehavioralBendFrontier:
    return BehavioralBendFrontier(
        True,
        True,
        True,
        True,
        True,
        False,
        False,
        False,
        False,
        True,
        True,
        True,
        True,
        False,
        False,
        "REFUTED_RAW_BEND_QUOTIENT",
        (
            "derive the capped distance-to-bend coordinate without hidden q, "
            "or quotient a candidate-derived theorem defect (Pepin/LL/Frobenius); "
            "the raw partition grammar is already one-rule closed, but evaluating "
            "its distance coordinate is still the missing factor-free operation"
        ),
    )


__all__ = [
    "BabyGiantBendPacketMemo",
    "BabyGiantPhaseAudit",
    "BabyGiantSupportPacketMemo",
    "BehavioralBendFrontier",
    "BehavioralBendQuotientAudit",
    "DyadicBendPartitionRow",
    "FixedWindowBendPacket",
    "FixedWindowSupportPacket",
    "behavioral_bend_frontier",
    "behavioral_bend_quotient_audit",
    "closed_trace_class",
]
