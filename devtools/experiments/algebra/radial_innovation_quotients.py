"""Radial-mode / innovation quotient audit for reverse-add and Collatz.

The large predictable exponential mode is removed *before* testing closure.
Reverse-add uses the exact cyclotomic factorization of ``2**q(1+z)**r``;
Collatz uses the exact p-adic affine slab ``(3**H*x+C)/2**K`` modulo ``3**a``.
No carry vector or cross-radix source reconstruction is used.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import asdict, dataclass
from functools import cache

from devtools.proofs import exact_oracle
from devtools.proofs.carry_action_quotient import CarryResetSignature
from number_compiler.arithmetic.automata.program_word import from_runs
from number_compiler.arithmetic.carry.event_memory import forcing_event, pair_step
from number_compiler.arithmetic.fields.adic_morphism import collatz_slab_padic3
from number_compiler.arithmetic.fields.radial_innovation import (
    ReverseAddCyclotomicInnovationBlock,
)
from number_compiler.arithmetic.fields.radix import (
    reverse_pair_sums,
    reverse_radix_integer,
)
from number_compiler.arithmetic.formula.symmetry_frame import (
    FixedRealCyclotomicGerm,
    ReverseAddSymmetryInnovationBlock,
)
from number_compiler.arithmetic.polynomials.cyclotomic_transport import (
    power_two_cyclotomic_radial_quotient,
)
from number_compiler.sequences.collatz.frame import (
    CollatzFixedPointPadicFrame,
    collatz_affine_suffix_valuations_value,
    collatz_affine_suffix_valuations_word,
    collatz_radix4_frame_factorization,
    fixed_frame_future_collision,
)
from number_compiler.sequences.collatz.pair import (
    accelerated_odd_collatz,
    valuation_itinerary_slab,
)
from number_compiler.sequences.collatz.root_germs import RationalPadicRootGerm


@dataclass(frozen=True, slots=True)
class RadialMultiplierAudit:
    classes: int
    bits: int
    no_growth: int
    growth: int
    radial_exponent: int
    scalar_v2: int
    remainder_growth: int
    annihilated: bool
    exact_reconstruction: bool


@dataclass(frozen=True, slots=True)
class ReverseInnovationAudit:
    label: str
    seeds: int
    steps: int
    orders: tuple[int, ...]
    bits: int
    usable_states: int
    innovation_classes: int
    distinct_pair_states: int
    next_growth_conflicts: int
    next_action_conflicts: int
    max_live_steps: int
    near_reconstruction: bool


@dataclass(frozen=True, slots=True)
class CollatzRadialAudit:
    label: str
    source_start: int
    source_stop: int
    precision: int
    trajectory_steps: int
    usable_states: int
    innovation_classes: int
    distinct_current_states: int
    next_valuation_conflicts: int
    source_annihilation_exact: bool
    innovation_projection_exact: bool
    near_reconstruction: bool


@dataclass(frozen=True, slots=True)
class CollatzFixedFrameAudit:
    label: str
    source_start: int
    source_stop: int
    precision: int
    trajectory_steps: int
    usable_states: int
    distinct_current_states: int
    raw_future_classes: int
    raw_future_conflicts: int
    frame_future_classes: int
    frame_future_conflicts: int
    frame_projection_exact: bool
    frame_near_reconstruction: bool
    finite_precision_nonclosure_witness: bool


@dataclass(frozen=True, slots=True)
class CollatzRationalRootAudit:
    odd_sources: int
    projected_steps: int
    exact: bool
    max_denominator_power: int
    million_run_valuation: int
    million_run_final_suffix_length: int


@dataclass(frozen=True, slots=True)
class RadialInnovationMetrics:
    multiplier: tuple[RadialMultiplierAudit, ...]
    reverse_add: tuple[ReverseInnovationAudit, ...]
    reverse_add_symmetry: tuple[ReverseInnovationAudit, ...]
    collatz: tuple[CollatzRadialAudit, ...]
    collatz_fixed_frame: tuple[CollatzFixedFrameAudit, ...]
    collatz_rational_root: CollatzRationalRootAudit


@cache
@exact_oracle()
def _innovation_atom(
    event: tuple[int, ...],
    growth: int,
    order: int,
    bits: int,
) -> ReverseAddCyclotomicInnovationBlock:
    return ReverseAddCyclotomicInnovationBlock.atom(
        event,
        growth,
        order=order,
        bits=bits,
    )


@exact_oracle()
def _live_reverse_innovation(
    events: tuple[tuple[int, ...], ...],
    growths: tuple[int, ...],
    end: int,
    *,
    order: int,
    bits: int,
) -> tuple[tuple[int, ...], int] | None:
    suffix = ReverseAddCyclotomicInnovationBlock.identity(order=order, bits=bits)
    for start in range(int(end) - 1, -1, -1):
        suffix = _innovation_atom(events[start], growths[start], order, bits).then(
            suffix
        )
        if suffix.source_annihilated:
            return suffix.innovation, end - start
    return None


@exact_oracle()
def _reverse_domain(
    label: str,
    seeds: Iterable[int],
    steps: int,
    *,
    orders: tuple[int, ...],
    bits: int,
) -> ReverseInnovationAudit:
    seed_values = tuple(map(int, seeds))
    seen: dict[tuple[object, ...], tuple[int, tuple[object, ...]]] = {}
    classes: set[tuple[object, ...]] = set()
    pair_states: set[tuple[int, ...]] = set()
    growth_conflicts = action_conflicts = usable = max_live = 0
    for seed in seed_values:
        value = seed
        pairs: list[tuple[int, ...]] = []
        events: list[tuple[int, ...]] = []
        growths: list[int] = []
        for _ in range(int(steps)):
            pair = reverse_pair_sums(value, 10)
            target, growth = pair_step(pair, 10)
            pairs.append(pair)
            events.append(forcing_event(pair, target, growth))
            growths.append(growth)
            value += reverse_radix_integer(value, 10)
        event_rows = tuple(events)
        growth_rows = tuple(growths)
        for index in range(1, len(pairs)):
            factors = []
            live = 0
            for order in orders:
                result = _live_reverse_innovation(
                    event_rows,
                    growth_rows,
                    index,
                    order=order,
                    bits=bits,
                )
                if result is None:
                    break
                innovation, age = result
                factors.append((order, innovation))
                live = max(live, age)
            else:
                key = (len(pairs[index]), tuple(factors))
                behavior = (
                    growths[index],
                    CarryResetSignature.from_pair(pairs[index], base=10).canonical_key,
                )
                old = seen.get(key)
                if old is not None:
                    growth_conflicts += int(old[0] != behavior[0])
                    action_conflicts += int(old[1] != behavior[1])
                else:
                    seen[key] = behavior
                classes.add(key)
                pair_states.add(pairs[index])
                usable += 1
                max_live = max(max_live, live)
    distinct = len(pair_states)
    return ReverseInnovationAudit(
        label,
        len(seed_values),
        int(steps),
        tuple(orders),
        int(bits),
        usable,
        len(classes),
        distinct,
        growth_conflicts,
        action_conflicts,
        max_live,
        distinct > 0 and len(classes) >= distinct * 0.95,
    )


@exact_oracle()
def reverse_radial_audits() -> tuple[ReverseInnovationAudit, ...]:
    # Low modes show the residual conflicts; adding Phi_16 removes those on the
    # bounded holdouts only by approaching one innovation state per pair.
    rows: list[ReverseInnovationAudit] = []
    for orders in ((2, 4, 8), (2, 4, 8, 16)):
        rows.extend(
            (
                _reverse_domain("train", range(1, 81), 28, orders=orders, bits=5),
                _reverse_domain(
                    "holdout", range(10_000, 10_061), 28, orders=orders, bits=5
                ),
                _reverse_domain(
                    "high", range(1_000_000, 1_000_031), 28, orders=orders, bits=5
                ),
            )
        )
    return tuple(rows)


@cache
@exact_oracle()
def _symmetry_innovation_atom(
    event: tuple[int, ...],
    growth: int,
    source_width: int,
    order: int,
    bits: int,
) -> ReverseAddSymmetryInnovationBlock:
    return ReverseAddSymmetryInnovationBlock.atom(
        event,
        growth,
        source_width=source_width,
        order=order,
        bits=bits,
    )


@exact_oracle()
def _live_reverse_symmetry_innovations_aligned(
    events: tuple[tuple[int, ...], ...],
    growths: tuple[int, ...],
    widths: tuple[int, ...],
    end: int,
    *,
    orders: tuple[int, ...],
    bits: int,
) -> tuple[dict[int, tuple[int, ...]], int] | None:
    """Return all fixed-ring innovations at one common source-death horizon.

    Older audits independently stopped each cyclotomic factor at its earliest
    annihilation point and then combined those different forcing suffixes into
    one key.  That product did not describe a single innovation polynomial.
    The joint fixed-ring germ is meaningful only after every requested factor
    has killed the same old source, so composition proceeds in lockstep and the
    first *joint* annihilation horizon is used.
    """
    if not orders:
        raise ValueError("aligned symmetry innovation requires at least one order")
    suffix = {
        order: ReverseAddSymmetryInnovationBlock.identity(
            start_parity=widths[end] & 1,
            order=order,
            bits=bits,
        )
        for order in orders
    }
    for start in range(int(end) - 1, -1, -1):
        for order in orders:
            atom = _symmetry_innovation_atom(
                events[start],
                growths[start],
                widths[start],
                order,
                bits,
            )
            suffix[order] = atom.then(suffix[order])
        if all(block.source_annihilated for block in suffix.values()):
            return (
                {order: suffix[order].fixed_innovation for order in orders},
                end - start,
            )
    return None


@exact_oracle()
def _reverse_symmetry_domain(
    label: str,
    seeds: Iterable[int],
    steps: int,
    *,
    orders: tuple[int, ...],
    bits: int,
) -> ReverseInnovationAudit:
    seed_values = tuple(map(int, seeds))
    seen: dict[tuple[object, ...], tuple[int, tuple[object, ...]]] = {}
    classes: set[tuple[object, ...]] = set()
    pair_states: set[tuple[int, ...]] = set()
    growth_conflicts = action_conflicts = usable = max_live = 0
    for seed in seed_values:
        value = seed
        pairs: list[tuple[int, ...]] = []
        events: list[tuple[int, ...]] = []
        growths: list[int] = []
        widths: list[int] = []
        for _ in range(int(steps)):
            pair = reverse_pair_sums(value, 10)
            target, growth = pair_step(pair, 10)
            pairs.append(pair)
            widths.append(len(pair))
            events.append(forcing_event(pair, target, growth))
            growths.append(growth)
            value += reverse_radix_integer(value, 10)
        event_rows = tuple(events)
        growth_rows = tuple(growths)
        width_rows = tuple(widths)
        for index in range(1, len(pairs)):
            aligned = _live_reverse_symmetry_innovations_aligned(
                event_rows,
                growth_rows,
                width_rows,
                index,
                orders=orders,
                bits=bits,
            )
            if aligned is None:
                continue
            views, live = aligned
            if {2, 4, 8}.issubset(views):
                germ = FixedRealCyclotomicGerm.from_fixed_views(views, bits=bits)
                retained: tuple[object, ...] = (germ.canonical_key,)
                if 16 in views:
                    retained += ((16, views[16]),)
            else:
                retained = tuple((order, views[order]) for order in orders)
            key = (len(pairs[index]), retained)
            behavior = (
                growths[index],
                CarryResetSignature.from_pair(pairs[index], base=10).canonical_key,
            )
            old = seen.get(key)
            if old is not None:
                growth_conflicts += int(old[0] != behavior[0])
                action_conflicts += int(old[1] != behavior[1])
            else:
                seen[key] = behavior
            classes.add(key)
            pair_states.add(pairs[index])
            usable += 1
            max_live = max(max_live, live)
    distinct = len(pair_states)
    return ReverseInnovationAudit(
        label,
        len(seed_values),
        int(steps),
        tuple(orders),
        int(bits),
        usable,
        len(classes),
        distinct,
        growth_conflicts,
        action_conflicts,
        max_live,
        distinct > 0 and len(classes) >= distinct * 0.95,
    )


@exact_oracle()
def reverse_symmetry_audits() -> tuple[ReverseInnovationAudit, ...]:
    rows: list[ReverseInnovationAudit] = []
    for orders in ((2, 4, 8), (2, 4, 8, 16)):
        rows.extend(
            (
                _reverse_symmetry_domain(
                    "train", range(1, 81), 28, orders=orders, bits=5
                ),
                _reverse_symmetry_domain(
                    "holdout", range(10_000, 10_061), 28, orders=orders, bits=5
                ),
                _reverse_symmetry_domain(
                    "high", range(1_000_000, 1_000_031), 28, orders=orders, bits=5
                ),
            )
        )
    return tuple(rows)


@exact_oracle()
def radial_multiplier_audits() -> tuple[RadialMultiplierAudit, ...]:
    from number_compiler.arithmetic.polynomials.digit_cyclotomic import (
        CyclotomicDigitBlock,
    )

    rows: list[RadialMultiplierAudit] = []
    for classes in (1, 2, 4, 8):
        for q, r in ((0, 1), (3, 2), (4, 4), (8, 7), (12, 16)):
            bits = 5
            radial = power_two_cyclotomic_radial_quotient(classes, q, r, bits=bits)
            direct = CyclotomicDigitBlock.from_coefficients(
                (1,),
                order=2 * classes,
                modulus=1 << bits,
            ).reverse_add_linear_transport(no_growth=q, growth=r)
            rows.append(
                RadialMultiplierAudit(
                    classes,
                    bits,
                    q,
                    r,
                    radial.radial_exponent,
                    radial.scalar_v2,
                    radial.remainder_growth,
                    radial.annihilated,
                    radial.multiplier_residue() == direct.residue,
                )
            )
    return tuple(rows)


@exact_oracle()
def _collatz_domain(
    label: str,
    source_start: int,
    source_stop: int,
    *,
    precision: int,
    steps: int,
) -> CollatzRadialAudit:
    seen: dict[int, int] = {}
    classes: set[int] = set()
    current_states: set[int] = set()
    conflicts = usable = 0
    annihilation_exact = projection_exact = True
    start = int(source_start) | 1
    stop = int(source_stop)
    for source in range(start, stop, 2):
        value = source
        valuations: list[int] = []
        states: list[tuple[int, int]] = []
        for _ in range(int(steps)):
            step = accelerated_odd_collatz(value)
            valuations.append(step.valuation)
            states.append((value, step.valuation))
            value = step.target
            if value == 1:
                break
        for index in range(int(precision), len(states)):
            recent = valuations[index - precision : index]
            slab = valuation_itinerary_slab(recent)
            radial = collatz_slab_padic3(slab, precision).radial_quotient
            annihilation_exact &= radial.source_annihilated
            modulus = 3**precision
            projection_exact &= radial.innovation == states[index][0] % modulus
            key = radial.innovation
            target = states[index][1]
            old = seen.get(key)
            if old is not None and old != target:
                conflicts += 1
            else:
                seen.setdefault(key, target)
            classes.add(key)
            current_states.add(states[index][0])
            usable += 1
    distinct = len(current_states)
    return CollatzRadialAudit(
        label,
        start,
        stop,
        int(precision),
        int(steps),
        usable,
        len(classes),
        distinct,
        conflicts,
        annihilation_exact,
        projection_exact,
        distinct > 0 and len(classes) >= distinct * 0.95,
    )


@exact_oracle()
def collatz_radial_audits() -> tuple[CollatzRadialAudit, ...]:
    rows: list[CollatzRadialAudit] = []
    # Precision sweep on one bounded domain, then disjoint p=12/16 guards.
    for precision in (4, 8, 12, 16):
        rows.append(
            _collatz_domain(
                "small",
                1,
                6_001,
                precision=precision,
                steps=24,
            )
        )
    rows.extend(
        (
            _collatz_domain("holdout", 100_001, 106_001, precision=12, steps=24),
            _collatz_domain("holdout", 100_001, 106_001, precision=16, steps=24),
            _collatz_domain("high", 1_000_001, 1_006_001, precision=16, steps=24),
        )
    )
    return tuple(rows)


@exact_oracle()
def _collatz_fixed_frame_domain(
    label: str,
    source_start: int,
    source_stop: int,
    *,
    precision: int,
    steps: int,
) -> CollatzFixedFrameAudit:
    raw_seen: dict[int, int] = {}
    frame_seen: dict[tuple[object, ...], int] = {}
    raw_classes: set[int] = set()
    frame_classes: set[tuple[object, ...]] = set()
    current_states: set[int] = set()
    raw_conflicts = frame_conflicts = usable = 0
    projection_exact = True
    start = int(source_start) | 1
    stop = int(source_stop)
    for source in range(start, stop, 2):
        value = source
        valuations: list[int] = []
        states: list[tuple[int, int, int]] = []
        for _ in range(int(steps)):
            step = accelerated_odd_collatz(value)
            valuations.append(step.valuation)
            states.append((value, step.valuation, step.target))
            value = step.target
            if value == 1:
                break
        # Current valuation is allowed to choose the frame; closure is audited
        # against the *following* valuation, never against the value used to
        # construct the current key.
        for index in range(int(precision), len(states) - 1):
            n, current_k, target = states[index]
            next_k = states[index + 1][1]
            recent = valuations[index - precision : index]
            slab = valuation_itinerary_slab(recent)
            radial = collatz_slab_padic3(slab, precision).radial_quotient
            if not radial.source_annihilated or radial.innovation != n % (3**precision):
                projection_exact = False
                continue
            frame = CollatzFixedPointPadicFrame.from_radial_quotient(radial, current_k)
            exact = collatz_radix4_frame_factorization(n)
            projection_exact &= (
                frame.tail_residue == exact.tail % frame.modulus
                and frame.local_shift == exact.local_shift
                and frame.successor_residue == target % frame.modulus
            )
            raw_key = radial.innovation
            frame_key = frame.canonical_key
            old = raw_seen.get(raw_key)
            if old is not None and old != next_k:
                raw_conflicts += 1
            else:
                raw_seen.setdefault(raw_key, next_k)
            old = frame_seen.get(frame_key)
            if old is not None and old != next_k:
                frame_conflicts += 1
            else:
                frame_seen.setdefault(frame_key, next_k)
            raw_classes.add(raw_key)
            frame_classes.add(frame_key)
            current_states.add(n)
            usable += 1
    distinct = len(current_states)
    witness = False
    try:
        _m1, _m2, k1, k2 = fixed_frame_future_collision(precision)
        witness = k1 != k2
    except (ValueError, AssertionError):
        witness = False
    return CollatzFixedFrameAudit(
        label,
        start,
        stop,
        int(precision),
        int(steps),
        usable,
        distinct,
        len(raw_classes),
        raw_conflicts,
        len(frame_classes),
        frame_conflicts,
        projection_exact,
        distinct > 0 and len(frame_classes) >= distinct * 0.95,
        witness,
    )


@exact_oracle()
def collatz_fixed_frame_audits() -> tuple[CollatzFixedFrameAudit, ...]:
    return (
        _collatz_fixed_frame_domain("small", 1, 6_001, precision=8, steps=24),
        _collatz_fixed_frame_domain("small", 1, 6_001, precision=12, steps=24),
        _collatz_fixed_frame_domain(
            "holdout", 100_001, 106_001, precision=12, steps=24
        ),
        _collatz_fixed_frame_domain(
            "holdout", 100_001, 106_001, precision=16, steps=24
        ),
        _collatz_fixed_frame_domain(
            "high", 1_000_001, 1_006_001, precision=16, steps=24
        ),
    )


@exact_oracle()
def collatz_rational_root_audit() -> CollatzRationalRootAudit:
    """Differential audit for the general ``-c/3^h`` angular-root engine."""
    exact = True
    max_h = 0
    odd_sources = 0
    projected_steps = 8
    for source in range(1, 5_000, 2):
        odd_sources += 1
        projected, _germ = collatz_affine_suffix_valuations_value(
            source, projected_steps
        )
        value = source
        expected: list[int] = []
        for _ in range(projected_steps):
            step = accelerated_odd_collatz(value)
            expected.append(step.valuation)
            value = step.target
        exact &= projected == tuple(expected)

    # General-denominator spot-checks ensure the root engine is not secretly
    # specialized to the historical h=2 period-three case.
    for h in range(1, 9):
        max_h = max(max_h, h)
        p = 3**h
        for constant in (1, p // 3 if h > 1 else 1, p - 1):
            root = RationalPadicRootGerm(h, constant)
            for value in range(128):
                numerator = p * value + constant
                v2 = (abs(numerator) & -abs(numerator)).bit_length() - 1
                exact &= root.valuation_from_integer(value) == v2

    q = 1_000_000
    word = from_runs(((1, q), (3, 1)))
    valuations, final = collatz_affine_suffix_valuations_word(word, 2)
    exact &= valuations == (2 * q + 1, 4)
    return CollatzRationalRootAudit(
        odd_sources,
        projected_steps,
        bool(exact),
        max_h,
        valuations[0],
        final.suffix.length,
    )


@exact_oracle()
def radial_innovation_metrics() -> RadialInnovationMetrics:
    return RadialInnovationMetrics(
        radial_multiplier_audits(),
        reverse_radial_audits(),
        reverse_symmetry_audits(),
        collatz_radial_audits(),
        collatz_fixed_frame_audits(),
        collatz_rational_root_audit(),
    )


@exact_oracle()
def metrics_as_jsonable(metrics: RadialInnovationMetrics) -> dict[str, object]:
    return asdict(metrics)
