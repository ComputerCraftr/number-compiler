"""Source-bound Collatz consumers share the Mahler phase-partition owner."""

from __future__ import annotations

import pytest

from devtools.experiments.collatz.coarse_future_context import (
    collatz_prime_bucket_counts,
    observe_occurrence_context,
    source_prime_bucket_vector,
)
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.branch_quotients import (
    PRIME_BANK,
    PrimeBucketWorkspace,
    prime_lane_after,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.pair import accelerated_odd_collatz
from number_compiler.sequences.collatz.saturated_future import publish_valuation_block


@pytest.mark.validation
def test_coarse_bank_reuses_charged_shared_collatz_partitions() -> None:
    ledger = ResourceLedger()
    workspace = PrimeBucketWorkspace(ledger)
    try:
        counts = collatz_prime_bucket_counts(workspace)
        assert len(counts) == len(PRIME_BANK)
        assert sum(count for _, count in counts) == 55
        assert dict(counts)[31] == 6
        work = workspace.work
        assert collatz_prime_bucket_counts(workspace) == counts
        assert workspace.work == work
        assert ledger.entries == len(PRIME_BANK)
    finally:
        workspace.close()
    assert ledger.nodes == ledger.entries == 0


@pytest.mark.validation
def test_source_context_uses_exact_occurrence_admission_before_observation() -> None:
    occurrence = publish_valuation_block((2,) * 6)
    modulus = 1 << occurrence.domain.bits
    source = occurrence.domain.residue + modulus * (17 + 64 * 3)
    ledger = ResourceLedger()
    workspace = PrimeBucketWorkspace(ledger)
    try:
        context = observe_occurrence_context(occurrence, source, workspace, primes=8)
        assert context.deck == 17
        assert len(context.prime_buckets) == 8
        assert context.descent_fiber_start == 1
        work = workspace.work
        with pytest.raises(ValueError, match="outside"):
            observe_occurrence_context(occurrence, source + 2, workspace)
        assert workspace.work == work
        assert source_prime_bucket_vector(source, workspace, primes=8) == (
            context.prime_buckets
        )
    finally:
        workspace.close()
    assert ledger.nodes == ledger.entries == 0


@pytest.mark.validation
def test_one_source_selected_q_transports_every_prime_lane() -> None:
    ledger = ResourceLedger()
    workspace = PrimeBucketWorkspace(ledger)
    try:
        for source in (1, 7, 27, 31, 97, 1961):
            step = accelerated_odd_collatz(source)
            before_buckets = source_prime_bucket_vector(source, workspace, primes=8)
            after_buckets = source_prime_bucket_vector(step.target, workspace, primes=8)
            for index, prime in enumerate(PRIME_BANK[:8]):
                before = (-3 * source - 1) % prime
                after = (-3 * step.target - 1) % prime
                assert after == prime_lane_after(
                    "collatz", prime, before, step.valuation
                )
                labels = workspace.partition("collatz", prime)
                assert (before_buckets[index], after_buckets[index]) == (
                    labels[before],
                    labels[after],
                )
    finally:
        workspace.close()


@pytest.mark.validation
def test_partition_budget_refusal_does_not_publish_context() -> None:
    occurrence = publish_valuation_block((2,) * 6)
    source = occurrence.domain.residue
    ledger = ResourceLedger(max_nodes=1)
    workspace = PrimeBucketWorkspace(ledger)
    try:
        with pytest.raises(BlockContextBudgetExceeded):
            observe_occurrence_context(occurrence, source, workspace, primes=1)
        assert ledger.nodes == ledger.entries == 0
        assert workspace.work == 0
    finally:
        workspace.close()


@pytest.mark.validation
def test_equal_deck_and_prime_views_do_not_identify_exact_successors() -> None:
    occurrence = publish_valuation_block((2,) * 6)
    modulus = 1 << occurrence.domain.bits
    prime_product = PRIME_BANK[0] * PRIME_BANK[1] * PRIME_BANK[2]
    first = occurrence.domain.residue + modulus * 17
    second = first + modulus * 64 * prime_product
    ledger = ResourceLedger()
    workspace = PrimeBucketWorkspace(ledger)
    try:
        left = observe_occurrence_context(occurrence, first, workspace, primes=3)
        right = observe_occurrence_context(occurrence, second, workspace, primes=3)
        assert left == right
        assert occurrence.apply_exact(first) != occurrence.apply_exact(second)
    finally:
        workspace.close()
