"""Shared phase observers preserve exact laws and charge bounded reuse."""

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.branch_quotients import (
    PRIME_BANK,
    BranchChoiceSuffix,
    PrimeBucketWorkspace,
    prime_lane_after,
)
from number_compiler.resources.ledger import ResourceLedger
from tests.support.exact_integer_power import exact_integer_power


def test_phase_partitions_share_workspace_without_cross_family_aliasing() -> None:
    ledger = ResourceLedger()
    workspace = PrimeBucketWorkspace(ledger)
    totals: list[int] = []
    for family in ("mahler", "collatz"):
        total = 0
        for p in PRIME_BANK:
            labels = workspace.partition(family, p)
            work = workspace.work
            assert workspace.partition(family, p) is labels
            assert workspace.work == work
            total += len(set(labels))
        totals.append(total)
    assert totals == [67, 55]
    assert ledger.nodes > 0 and ledger.entries == 40
    workspace.close()
    assert ledger.nodes == ledger.entries == 0
    with pytest.raises(ValueError, match="closed"):
        workspace.partition("mahler", 5)


def test_compact_phase_signatures_keep_reference_class_ids() -> None:
    ledger = ResourceLedger()
    workspace = PrimeBucketWorkspace(ledger)
    for family in ("mahler", "collatz"):
        for prime in PRIME_BANK:
            phases = {
                (exact_integer_power(3, q, prime) if family == "mahler" else 3)
                * exact_integer_power(2, -q, prime)
                % prime
                for q in range(1, prime)
            }
            labels = tuple(int(u != 0) for u in range(prime))
            result = labels
            for _ in range(prime + 1):
                classes: dict[tuple[int, tuple[tuple[int, bool, bool], ...]], int] = {}
                refined: list[int] = []
                for u in range(prime):
                    outcomes = {
                        (
                            labels[(phase * u - 1) % prime],
                            u != 0 and (phase * u - 1) % prime == 0,
                            u == 0 and (phase * u - 1) % prime != 0,
                        )
                        for phase in phases
                    }
                    key = labels[u], tuple(sorted(outcomes))
                    refined.append(classes.setdefault(key, len(classes)))
                result = tuple(refined)
                if result == labels:
                    break
                labels = result
            assert workspace.partition(family, prime) == result
    workspace.close()
    assert ledger.nodes == ledger.entries == 0


def test_phase_refusal_releases_scratch_and_does_not_publish() -> None:
    ledger = ResourceLedger()
    workspace = PrimeBucketWorkspace(ledger, max_phase_work=4)
    with pytest.raises(BlockContextBudgetExceeded, match="phase work"):
        workspace.partition("mahler", 5)
    assert ledger.nodes == ledger.entries == 0
    assert workspace.work == 4
    workspace.close()


def test_partition_storage_refusal_precedes_refinement() -> None:
    ledger = ResourceLedger(max_nodes=1)
    workspace = PrimeBucketWorkspace(ledger)
    with pytest.raises(BlockContextBudgetExceeded):
        workspace.partition("mahler", 5)
    assert workspace.work == 0
    assert ledger.nodes == ledger.entries == 0
    workspace.close()


def test_refinement_storage_refusal_releases_admitted_phase_workspace() -> None:
    ledger = ResourceLedger(max_nodes=80)
    workspace = PrimeBucketWorkspace(ledger)
    with pytest.raises(BlockContextBudgetExceeded):
        workspace.partition("mahler", 11)
    assert workspace.work >= 10
    assert ledger.nodes == ledger.entries == 0
    workspace.close()


def test_distinct_phase_actions_use_same_explicit_q_without_identification() -> None:
    for p in PRIME_BANK:
        for q in range(1, 9):
            for u in range(p):
                assert (
                    prime_lane_after("mahler", p, u, q)
                    == (
                        exact_integer_power(3, q, p) * exact_integer_power(2, -q, p) * u
                        - 1
                    )
                    % p
                )
                assert (
                    prime_lane_after("collatz", p, u, q)
                    == (3 * exact_integer_power(2, -q, p) * u - 1) % p
                )
    assert prime_lane_after("mahler", 5, 1, 2) == 0
    assert prime_lane_after("collatz", 5, 1, 2) == 1


def test_suffix_repetition_is_chronological_and_preserves_leading_choices() -> None:
    left = BranchChoiceSuffix().append(1).append(2)
    right = BranchChoiceSuffix().append(3).append(1)
    assert left.then(right).choices() == (1, 2, 3, 1)
    assert left.then(right).then(left).then(right).choices() == (3, 1, 1, 2, 3, 1)
    assert BranchChoiceSuffix().append(1) != BranchChoiceSuffix()
