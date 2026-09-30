"""Prime buckets and carry domains consume the same source-derived event."""

from fractions import Fraction
from math import comb

import pytest

from devtools.experiments.antihydra.source_observers import (
    BranchChoiceSuffix,
    collatz_prime_buckets,
    observe_event,
    prime_buckets,
)
from devtools.experiments.antihydra.source_safety import (
    PRIME_BANK,
    SourceSafetyWorkspace,
    source_event,
)
from number_compiler.arithmetic.carry.collatz_output_quotient import DOMAIN_ACTIONS
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.consumer_pullback import ExactRational as Q
from number_compiler.resources.ledger import ResourceLedger


def _binary_y_coefficient(value: int, degree: int) -> int:
    return sum(
        comb(i, degree) * (-1) ** (i - degree)
        for i in range(degree, value.bit_length())
        if value & (1 << i)
    )


def test_updated_collatz_prime_partition_uses_its_own_phase_law() -> None:
    ledger = ResourceLedger()
    total = 0
    for prime in PRIME_BANK:
        labels = collatz_prime_buckets(prime, ledger)
        total += len(set(labels))
        phases = {3 * pow(2, -q, prime) % prime for q in range(1, prime)}
        signatures: dict[int, frozenset[tuple[int, bool, bool]]] = {}
        for u in range(prime):
            outcomes = frozenset(
                (
                    labels[(a * u - 1) % prime],
                    u != 0 and (a * u - 1) % prime == 0,
                    u == 0 and (a * u - 1) % prime != 0,
                )
                for a in phases
            )
            assert signatures.setdefault(labels[u], outcomes) == outcomes
        for source in range(1, 256, 2):
            numerator, q = 3 * source + 1, 0
            while numerator % 2 == 0:
                numerator //= 2
                q += 1
            u, target = -3 * source - 1, -3 * numerator - 1
            assert target % prime == (3 * pow(2, -q, prime) * u - 1) % prime
    assert total == 55
    assert ledger.counters["collatz_prime_phase_visits"] > 0
    assert ledger.counters.get("mahler_prime_phase_visits", 0) == 0


def test_branch_suffix_monoid_matches_bounded_word_concatenation() -> None:
    states = [
        BranchChoiceSuffix(length, code)
        for length in range(7)
        for code in range(3**length)
    ]
    identity = BranchChoiceSuffix()
    assert len(states) == 1093
    assert identity != identity.append(1)  # Leading ternary zero is not empty.
    for i, state in enumerate(states):
        assert state.then(identity) == identity.then(state) == state
        for choice in (1, 2, 3):
            assert state.append(choice).choices() == (state.choices() + (choice,))[-6:]
        for shift in range(1, 8):
            second = states[(37 * i + shift) % len(states)]
            third = states[(71 * i + 11 * shift) % len(states)]
            joined = state.then(second).then(third)
            assert joined == state.then(second.then(third))
            assert (
                joined.choices()
                == (state.choices() + second.choices() + third.choices())[-6:]
            )


@pytest.mark.parametrize(
    "length,code", ((7, 0), (0, 1), (6, 729), (True, 0), (1, False))
)
def test_branch_suffix_rejects_invalid_encodings(length: int, code: int) -> None:
    with pytest.raises(ValueError, match="bounded branch suffix"):
        BranchChoiceSuffix(length, code)


@pytest.mark.parametrize("choice", (0, 4, True))
def test_branch_suffix_rejects_invalid_choices(choice: int) -> None:
    with pytest.raises(ValueError, match="branch choice"):
        BranchChoiceSuffix().append(choice)


def test_mahler_possibility_bucket_is_not_a_fixed_event_collatz_action() -> None:
    labels = prime_buckets(5, ResourceLedger())
    # Both odd sources have exact v2(3*n+1)=1 and the same Mahler bucket.
    # Their Collatz targets have different buckets. This only refutes direct
    # deterministic reuse of this single observer, not the proposed product.
    assert labels[3] == labels[7 % 5]
    targets = tuple((3 * source + 1) // 2 for source in (3, 7))
    assert targets == (5, 11)
    assert all(target % 2 for target in targets)
    assert labels[5 % 5] != labels[11 % 5]


def test_prime_possibility_buckets_reproduce_the_research_partition() -> None:
    ledger = ResourceLedger()
    partitions = {p: prime_buckets(p, ledger) for p in PRIME_BANK}
    sizes = {p: len(set(labels)) for p, labels in partitions.items()}
    assert sum(sizes.values()) == 67
    assert {p: sizes[p] for p in (13, 29, 53, 61, 79)} == {
        13: 3,
        29: 4,
        53: 3,
        61: 4,
        79: 3,
    }
    for p, labels in partitions.items():
        assert all(labels[u] != labels[0] for u in range(1, p))
        outcomes: dict[int, set[tuple[int, bool, bool]]] = {}
        for u in range(p):
            # Exponents 1..p-1 cover every nonzero phase; direct arithmetic
            # verifies representative independence without invoking refinement.
            targets = set()
            for q in range(1, p):
                v = (pow(3, q, p) * pow(pow(2, q, p), -1, p) * u - 1) % p
                targets.add((labels[v], u != 0 and v == 0, u == 0 and v != 0))
            key = labels[u]
            if key in outcomes:
                assert outcomes[key] == targets
            outcomes[key] = targets
    assert ledger.counters["mahler_prime_phase_visits"] > 0


@pytest.mark.parametrize(
    "source,t",
    (
        (1, Q(3, 8)),
        (1, Q(7, 16)),
        (1, Q(15, 32)),
        (1, Q((1 << 120) - 1, 1 << 121)),
        (2, Q(1, 4)),
        (4, Q(3, 16)),
        (8, Q(1, 8)),
    ),
)
def test_joint_readouts_match_the_admitted_event(source: int, t: Q) -> None:
    ledger = ResourceLedger()
    event = source_event(SourceSafetyWorkspace(ledger), source, t)
    observation = observe_event(event, ledger)
    w = 4 * Fraction(t.numerator, t.denominator)
    expected = Fraction(3, 2) ** event.exponent * w - 2
    assert (
        Fraction(observation.raw_numerator, 1 << observation.denominator_exponent)
        == expected
    )
    assert observation.source == source and observation.exponent == event.exponent
    assert len(observation.multiplication) == event.exponent
    for p, first, last in observation.prime_buckets:
        assert (first == 0) == (w.numerator % p == 0)
        assert (last == 0) == (expected.numerator % p == 0)
    numerator = w.numerator
    for action in observation.multiplication:
        word, extent, phase = numerator, 1, 0
        while word:
            word, digit = divmod(word, 64)
            extent *= 64
            # Independent y^2 coefficient of D_(3d+1)(y-1)
            # minus y D_d(y-1), not the production F5 table.
            phase += _binary_y_coefficient(3 * digit + 1, 2) - _binary_y_coefficient(
                digit, 1
            )
        assert DOMAIN_ACTIONS[action.carry_action] == tuple(
            (3 * numerator + carry) // extent for carry in range(3)
        )
        assert action.phase == phase % 5
        w *= 3
        numerator = w.numerator
    assert ledger.counters["mahler_carry_columns"] > 0
    assert (
        ledger.counters.get("mahler_f5_spatial_compositions", 0)
        == ledger.counters["mahler_f5_spatial_leaves"] - event.exponent
    )


def test_carry_work_is_explicitly_bounded_before_observation() -> None:
    ledger = ResourceLedger()
    event = source_event(SourceSafetyWorkspace(ledger), 8, Q(1, 8))
    with pytest.raises(BlockContextBudgetExceeded, match="column budget"):
        observe_event(event, ledger, max_columns=1)
    assert ledger.counters.get("mahler_carry_columns", 0) == 0
    assert ledger.counters.get("mahler_prime_phase_visits", 0) == 0


def test_invalid_finite_bank_lane_is_rejected() -> None:
    with pytest.raises(ValueError, match="declared"):
        prime_buckets(9, ResourceLedger())
