"""Finite carry/Hensel evidence, never production successor-class identity.

Reconstructed from the supplied September 10 results. Every arithmetic helper
comes from its existing owner. Exact fields below are research observations;
the negative controls forbid interpreting their finite keys as closed state.
"""

from collections import Counter, defaultdict
from collections.abc import Iterator
from dataclasses import dataclass
from itertools import product
from typing import Hashable

import pytest

from devtools.proofs import exact_oracle
from number_compiler.arithmetic.automata.program_word import from_values
from number_compiler.arithmetic.carry.collatz_carry_wires import (
    collatz_digit_carry_wires,
)
from number_compiler.arithmetic.carry.collatz_output_quotient import (
    DOMAIN_ACTIONS,
    RADIX64_DIRECTIONAL_DOMAIN_COUNTS,
    radix64_domain,
    radix64_domain_from_directional_views,
    radix64_growth_edge,
    radix64_join_shift_views,
    radix64_left_domain_view,
    radix64_raw_emit,
    radix64_right_domain_view,
    radix64_shift,
    radix64_shift_views,
    radix64_split,
)
from number_compiler.arithmetic.fields.radix import digits_lsd, value_from_lsd_digits
from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.sequences.collatz import radix64_transducer, raw_field
from number_compiler.sequences.collatz.raw_field import (
    summarize_collatz_sentinel_boundaries,
)
from number_compiler.sequences.collatz.root_germs import (
    PadicAngularBoundaryGerm,
    RationalPadicRootGerm,
)

DomainKey = tuple[
    int,
    tuple[int, ...],
    tuple[tuple[tuple[int, ...], int], ...],
    int,
    int,
    tuple[int, ...],
]


@pytest.fixture(autouse=True)
def _reference_scope() -> Iterator[None]:
    with exact_oracle():
        yield


def _crop(digits: tuple[int, ...]) -> tuple[tuple[int, ...], int]:
    boundary = summarize_collatz_sentinel_boundaries(digits, base=64)
    count = boundary.length if boundary.all_sentinel else boundary.low_first_mismatch
    assert count is not None
    return digits[count:] or (0,), count


def _hensel(m: int, e: int) -> tuple[int, int, int]:
    """Pull back to the source word; no successor word is constructed here."""
    root = RationalPadicRootGerm(2, 3 + (1 << e))
    mismatch, _suffix = root.first_mismatch_word(from_values(digits_lsd(m, 4)))
    angular = PadicAngularBoundaryGerm.from_mismatch(root, mismatch)
    return mismatch.valuation_bits - e, angular.multiplier, angular.offset


def _directional_next_domains(source: tuple[int, ...]) -> tuple[int, ...]:
    """Compile one domain output using only derived carries and L/R views."""
    _normalized, frame = _crop(source)
    active = source[frame:]
    if not active:
        return (radix64_domain(1),)
    shift = v2_positive(3 * active[0] + 1)
    assert shift < 6
    carry = 1
    raws = []
    for digit in active:
        carry, raw = radix64_raw_emit(*radix64_split(digit), carry)
        raws.append(raw)
    domains = [
        radix64_domain_from_directional_views(
            radix64_left_domain_view(raw, shift),
            radix64_right_domain_view(adjacent, shift),
            shift,
        )
        for raw, adjacent in zip(raws, raws[1:])
    ]
    quotient, _ = radix64_shift_views(raws[-1], shift)
    _, remainder = radix64_shift_views(carry, shift)
    last = radix64_join_shift_views(quotient, remainder, shift)
    edge = radix64_growth_edge(carry, shift)
    if last or edge:
        domains.append(
            radix64_domain_from_directional_views(
                radix64_left_domain_view(raws[-1], shift),
                radix64_right_domain_view(carry, shift),
                shift,
            )
        )
    if edge:
        domains.append(radix64_domain(edge))
    return tuple(domains)


@dataclass(frozen=True)
class _Observation:
    domain: DomainKey
    hensel: tuple[int, int, int]
    target: int
    frame: int  # Occurrence metadata, deliberately excluded from both keys.

    def key(self, refined: bool) -> Hashable:
        return (self.domain, self.hensel) if refined else self.domain


def _observe(n: int) -> _Observation:
    source = digits_lsd(n, 64)
    normalized, q = _crop(source)
    m = value_from_lsd_digits(normalized, 64)
    event = radix64_transducer.compose_radix64_events(source)
    e = event.source_shift
    assert event.source_frame == q
    assert event.valuation == 6 * q + e
    assert e == v2_positive(3 * m + 1) < 6
    ports = []
    for incoming in range(3):
        carry = incoming
        output_domains = []
        for digit in normalized:
            carry, raw = radix64_raw_emit(*radix64_split(digit), carry)
            output_domains.append(radix64_domain(raw))
        ports.append((tuple(output_domains), carry))
    successor, next_frame = _crop(event.target_digits)
    assert next_frame == event.exit_frame
    domain: DomainKey = (
        e,
        tuple(map(radix64_domain, normalized)),
        tuple(ports),
        radix64_growth_edge(ports[1][1], e),
        next_frame,
        tuple(map(radix64_domain, successor)),
    )
    return _Observation(
        domain, _hensel(m, e), value_from_lsd_digits(event.target_digits, 64), q
    )


def test_radix64_five_way_carry_domain_quotient() -> None:
    fibers = Counter(radix64_domain(d) for d in range(64))
    assert tuple(fibers[i] for i in range(5)) == (21, 1, 20, 1, 21)
    actions = {d: tuple((3 * d + c) // 64 for c in range(3)) for d in range(64)}
    assert set(actions.values()) == set(DOMAIN_ACTIONS)
    for d in range(64):
        assert collatz_digit_carry_wires(d, base=64).outputs == actions[d]
        assert DOMAIN_ACTIONS[radix64_domain(d)] == actions[d]
    assert {d for d in range(64) if radix64_domain(d) in (1, 3)} == {21, 42}


def test_adjacent_division_domain_factorization_all_six_phases() -> None:
    counts = []
    for e in range(6):
        table = tuple(
            tuple(radix64_domain(radix64_shift(a, b, e)) for b in range(64))
            for a in range(64)
        )
        left = tuple(dict.fromkeys(table))
        columns = tuple(tuple(table[a][b] for a in range(64)) for b in range(64))
        right = tuple(dict.fromkeys(columns))
        counts.append((len(left), len(right)))
        # Factor the entire output table through the two independently formed
        # residual partitions; this asserts more than the number of classes.
        projected: dict[tuple[int, int], int] = {}
        for a, b in product(range(64), repeat=2):
            assert radix64_shift(a, b, e) == (a + 64 * b) >> e & 63
            key = left.index(table[a]), right.index(columns[b])
            assert projected.setdefault(key, table[a][b]) == table[a][b]
            assert key == (
                radix64_left_domain_view(a, e),
                radix64_right_domain_view(b, e),
            )
            assert radix64_domain_from_directional_views(*key, e) == table[a][b]
    assert counts == [(5, 1), (5, 2), (5, 4), (5, 5), (4, 5), (2, 5)]
    assert tuple(counts) == RADIX64_DIRECTIONAL_DOMAIN_COUNTS


def test_directional_views_reconstruct_complete_next_geometry() -> None:
    for n in range(1, 1 << 16, 2):
        source = digits_lsd(n, 64)
        event = radix64_transducer.compose_radix64_events(source)
        assert _directional_next_domains(source) == tuple(
            map(radix64_domain, event.target_digits)
        )
    for seed in (1, 15, 19, 27, 129, 385, 58723):
        n = seed
        for _ in range(8):
            source = digits_lsd(n, 64)
            event = radix64_transducer.compose_radix64_events(source)
            assert _directional_next_domains(source) == tuple(
                map(radix64_domain, event.target_digits)
            )
            n = value_from_lsd_digits(event.target_digits, 64)


def test_eq_survives_complete_acceleration_and_next_frame_crop() -> None:
    state = _observe(58723)
    event = radix64_transducer.compose_radix64_events(digits_lsd(58723, 64))
    assert digits_lsd(58723, 64) == (35, 21, 14)
    assert event.target_digits == (21, 32, 21)
    assert event.source_shift == 1 and event.exit_frame == 1
    assert state.domain[1] == (2, 1, 0)
    assert state.domain[-1] == (2, 1)
    assert state.domain[1][1] == state.domain[-1][1] == radix64_domain(21)


def test_growth_is_ordinary_lt_output_over_sixteen_bit_odd_domain() -> None:
    grown: dict[int, set[int]] = defaultdict(set)
    phases = set()
    for n in range(1, 1 << 16, 2):
        original = digits_lsd(n, 64)
        normalized, q = _crop(original)
        # An all-sentinel input has an empty normalized active field. The
        # implicit zero used in observation keys is not an active source cell.
        ds = original[q:]
        m = value_from_lsd_digits(normalized, 64)
        e = v2_positive(3 * m + 1)
        phases.add(e)
        carry = 1
        for d in ds:
            carry, _raw = radix64_raw_emit(*radix64_split(d), carry)
        edge = radix64_growth_edge(carry, e)
        target = (3 * m + 1) >> e
        target_digits = digits_lsd(target, 64)
        assert bool(edge) == (len(target_digits) > len(ds))
        if edge:
            assert edge == target_digits[-1]
            assert radix64_domain(edge) == 0
            grown[e].add(edge)
    assert phases == set(range(6))
    assert dict(grown) == {0: {1, 2}, 1: {1}}


def test_hensel_pullback_uses_source_without_successor_word(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("Hensel pullback constructed a successor word")

    monkeypatch.setattr(radix64_transducer, "compose_radix64_events", forbidden)
    monkeypatch.setattr(
        raw_field, "accelerated_collatz_sentinel_step_digits", forbidden
    )
    monkeypatch.setattr(raw_field.CollatzRawDigitField, "normalized_digits", forbidden)
    for m in range(4096):
        if m % 64 == 21:
            continue
        e = v2_positive(3 * m + 1)
        k_next, _multiplier, _offset = _hensel(m, e)
        # Independent scalar arithmetic is used only on the assertion side.
        assert k_next == v2_positive(3 * ((3 * m + 1) >> e) + 1)
        assert (
            k_next
            == RationalPadicRootGerm(2, 3 + (1 << e)).valuation_from_integer(m) - e
        )


def test_hensel_splits_fifteen_nineteen_but_is_not_successor_complete() -> None:
    fifteen, nineteen = _observe(15), _observe(19)
    assert fifteen.domain == nineteen.domain
    assert (fifteen.hensel[0], nineteen.hensel[0]) == (1, 3)
    assert fifteen.key(True) != nineteen.key(True)
    first, second = _observe(129), _observe(385)
    assert first.key(True) == second.key(True)
    assert first.hensel == second.hensel == (2, 36, 1)
    assert (first.target, second.target) == (97, 289)
    assert _observe(first.target).key(True) != _observe(second.target).key(True)


def test_seven_workbook_collisions_split_on_next_leaf_consumer_action() -> None:
    # Static rows from Occurrences1984/Context1152. Source and class labels are
    # provenance only; the compared value is the position-bound future action.
    fixtures = (
        (
            339,
            2,
            (1929, 2249),
            (30, 35),
            ((2, 2, 2), (2, 3, 0)),
            ((3, 3, 3), (1, 2, 3)),
        ),
        (
            555,
            2,
            (3209, 3529),
            (50, 55),
            ((1, 1, 2), (2, 3, 0)),
            ((2, 2, 2), (1, 2, 3)),
        ),
        (767, 2, (481, 801), (7, 12), ((1, 1, 1), (1, 2, 3)), ((2, 2, 2), (0, 1, 2))),
        (807, 3, (477, 797), (7, 12), ((1, 1, 1), (3, 4, 4)), ((2, 2, 2), (2, 3, 4))),
        (823, 4, (485, 805), (7, 12), ((1, 1, 1), (1, 2, 2)), ((2, 2, 2), (0, 1, 2))),
        (1442, 3, (557, 877), (8, 13), ((2, 2, 2), (0, 0, 1)), ((2, 3, 3), (4, 0, 0))),
        (
            1696,
            3,
            (1853, 2173),
            (28, 33),
            ((1, 1, 1), (2, 3, 4)),
            ((2, 2, 2), (2, 2, 3)),
        ),
    )

    def consumer(digit: int, shift: int) -> tuple[tuple[int, ...], tuple[int, ...]]:
        raw = tuple((3 * digit + carry) % 64 for carry in range(3))
        return (
            tuple(radix64_left_domain_view(value, shift) for value in raw),
            tuple(radix64_right_domain_view(value, shift) for value in raw),
        )

    for _old_class, shift, sources, digits, left_expected, right_expected in fixtures:
        assert sources[1] - sources[0] == 320
        assert digits[1] - digits[0] == 5
        left, right = (consumer(digit, shift) for digit in digits)
        assert left == left_expected
        assert right == right_expected
        assert left != right


def test_semantic_quotient_counts_with_frame_gauge_disabled() -> None:
    sources = tuple(n for n in range(1, 4096, 2) if n % 64 != 21)
    current = {n: _observe(n) for n in sources}
    assert len(current) == 1984 and all(s.frame == 0 for s in current.values())
    following = {s.target: _observe(s.target) for s in current.values()}
    measurements = []
    for refined in (False, True):
        fibers: dict[Hashable, list[_Observation]] = defaultdict(list)
        for state in current.values():
            fibers[state.key(refined)].append(state)
        conflicted = [
            states
            for states in fibers.values()
            if len({following[s.target].key(refined) for s in states}) > 1
        ]
        measurements.append((len(fibers), sum(map(len, conflicted)), len(conflicted)))
    assert measurements == [(792, 1707, 522), (1024, 1476, 524)]
    # Fewer source states in conflicting fibers does not mean fewer conflicting
    # classes, and neither refinement is an admissible temporal quotient.


def test_1152_frame_translation_all_phases_preserves_semantic_keys_and_target() -> None:
    tails = {
        e: next(m for m in range(64) if m != 21 and v2_positive(3 * m + 1) == e)
        for e in range(6)
    }
    for e, m in tails.items():
        states = []
        weights = []
        for q in (1, 193, 385):
            n = 64**q * m + (64**q - 1) // 3
            state = _observe(n)
            assert state.frame == q and state.domain[0] == e
            assert state.target == (3 * m + 1) >> e
            states.append(state)
            weights.append(v2_positive(3 * n + 1))
        assert len({s.key(True) for s in states}) == 1
        assert weights == [6 * q + e for q in (1, 193, 385)]
        assert weights[1] - weights[0] == weights[2] - weights[1] == 1152
