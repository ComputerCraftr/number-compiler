"""Prime buckets and carry domains consume the same source-derived event."""

from fractions import Fraction

import pytest

from devtools.experiments.antihydra.source_observers import observe_event, prime_buckets
from devtools.experiments.antihydra.source_safety import (
    PRIME_BANK,
    SourceSafetyWorkspace,
    source_event,
)
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.consumer_pullback import ExactRational as Q
from number_compiler.resources.ledger import ResourceLedger


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
    for actions in observation.multiplication:
        direct = []
        while numerator:
            numerator, digit = divmod(numerator, 64)
            direct.append(tuple((3 * digit + c) // 64 for c in range(3)))
        assert actions == tuple(direct)
        w *= 3
        numerator = w.numerator
    assert ledger.counters["mahler_carry_columns"] > 0


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
