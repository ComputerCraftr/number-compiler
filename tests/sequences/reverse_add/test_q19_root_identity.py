"""Issued Q19 roots retain node identity across arena suffix rollback."""

from collections.abc import Generator
from contextlib import contextmanager
from dataclasses import replace

import pytest

from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.q19_gram_observation import source_carry_gram
from number_compiler.sequences.reverse_add.q19_output import ReversePairQ19OutputOwner
from tests.support.q19_tiles import U as _U
from tests.support.q19_tiles import physical_seed


@contextmanager
def _paired_owners(
    source_word: tuple[int, ...],
) -> Generator[tuple[ReversePairQ19OutputOwner, ReversePairQ19OutputOwner], None, None]:
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(
        ledger, digits_lsd(int(physical_seed(source_word)), 10), base=10
    )
    reference = ReversePairQ19OutputOwner(
        ledger, digits_lsd(int(physical_seed(_U)), 10), base=10
    )
    try:
        yield owner, reference
    finally:
        reference.dispose()
        owner.dispose()
        assert ledger.nodes == ledger.entries == 0


def _rebuild_at_issued_id(
    owner: ReversePairQ19OutputOwner,
    reference: ReversePairQ19OutputOwner,
    *,
    discard_summaries: bool,
) -> int:
    old_root = owner.initial.root
    valid_root = reference.initial.root
    assert old_root >= valid_root
    before_remove = owner.discard_published_word_summary if discard_summaries else None
    owner.arena.rollback_unpublished_suffix(1, before_remove=before_remove)
    for offset in range(old_root - valid_root):
        owner.arena.terminal(100 + offset)
    new_root = owner._word(iter((19, 17) + _U + (11, 21)))  # pyright: ignore[reportPrivateUsage]
    assert new_root == old_root
    return new_root


@pytest.mark.parametrize("same_word", [False, True])
def test_reissued_node_id_is_not_the_issued_source(same_word: bool) -> None:
    original = _U if same_word else _U[:12] + (_U[12] + 9,) + _U[13:]
    with _paired_owners(original) as (owner, reference):
        issued = owner.initial
        old_root = issued.root
        candidate = owner.candidate(old_root, 2)
        old_binding = issued.publication_binding
        assert old_binding is not None
        new_root = _rebuild_at_issued_id(owner, reference, discard_summaries=True)
        new_node = owner.arena.nodes[new_root]
        assert new_node is not old_binding[-1]
        if same_word:
            assert new_node == old_binding[-1]
        with pytest.raises(ValueError, match="already bound"):
            issued.bind_publication((*old_binding[:-1], new_node))
        with pytest.raises(ValueError, match="generation is stale"):
            owner.publish(candidate)
        with pytest.raises(ValueError, match="root is stale"):
            owner.validate_issued_occurrence(issued)
        with pytest.raises(ValueError, match="root is stale"):
            owner.issued_occurrence((old_root, 1))
        with pytest.raises(ValueError, match="root is stale"):
            owner._issue(old_root, 1)  # pyright: ignore[reportPrivateUsage]
        with pytest.raises(ValueError, match="root is stale"):
            with source_carry_gram(owner, issued):
                pass


def test_unpublished_suffix_rollback_preserves_earlier_issued_root() -> None:
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(
        ledger, digits_lsd(int(physical_seed(_U)), 10), base=10
    )
    try:
        root = owner.initial
        before = ledger.nodes, ledger.entries
        checkpoint = len(owner.arena.nodes)
        owner.arena.terminal(100)
        owner.arena.rollback_unpublished_suffix(
            checkpoint, before_remove=owner.discard_published_word_summary
        )
        assert (ledger.nodes, ledger.entries) == before
        owner.validate_issued_occurrence(root)
        assert owner.issued_occurrence((root.root, 1)) is root
        with source_carry_gram(owner, root) as action:
            assert action.length == root.pair_width
    finally:
        owner.dispose()
        assert ledger.nodes == ledger.entries == 0


def test_unissued_matching_candidate_cannot_publish_at_a_fresh_key() -> None:
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(
        ledger, digits_lsd(int(physical_seed(_U)), 10), base=10
    )
    try:
        candidate = owner.candidate(owner.initial.root, 2)
        forged = replace(candidate)
        with pytest.raises(ValueError, match="generation is stale or foreign"):
            owner.publish(forged)
        assert owner.issued_occurrence((candidate.root, 2)) is None
        from number_compiler.sequences.reverse_add.q19_occurrence import (
            occurrence_publication_snapshot,
        )

        forged.bind_publication(
            (*occurrence_publication_snapshot(forged), owner.arena.nodes[forged.root])
        )
        with pytest.raises(ValueError, match="generation is stale or foreign"):
            owner.publish(forged)
        object.__setattr__(candidate, "pair_width", candidate.pair_width - 1)
        with pytest.raises(ValueError, match="candidate metadata was altered"):
            owner.publish(candidate)
        object.__setattr__(candidate, "pair_width", candidate.pair_width + 1)
        assert owner.publish(candidate) is candidate
        owner.validate_issued_occurrence(candidate)
    finally:
        owner.dispose()
        assert ledger.nodes == ledger.entries == 0


def test_reused_node_ids_invalidate_summary_and_projector_memos() -> None:
    old_word = _U[:2] + ((_U[2] + 1) % 10,) + _U[3:]
    with _paired_owners(old_word) as (owner, reference):
        owner.apply_pair_step(owner.initial)
        expected_next = reference.apply_pair_step(reference.initial)
        # Leave cached summaries in place while the node IDs are retired.
        rebuilt = _rebuild_at_issued_id(owner, reference, discard_summaries=False)
        candidate = owner.candidate(rebuilt, 2)
        assert (candidate.pair_width, candidate.q19_domain, candidate.q19_f9) == (
            reference.initial.pair_width,
            reference.initial.q19_domain,
            reference.initial.q19_f9,
        )
        result = owner.apply_pair_step(owner.publish(candidate))
        assert (result.pair_width, result.q19_domain, result.q19_f9) == (
            expected_next.pair_width,
            expected_next.q19_domain,
            expected_next.q19_f9,
        )


def test_failed_cache_refresh_is_retried_before_owner_reuse(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.automata.slp import BimachineSLPProjector

    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(
        ledger, digits_lsd(int(physical_seed(_U)), 10), base=10
    )
    try:
        checkpoint = len(owner.arena.nodes)
        owner.arena.terminal(100)
        owner.arena.rollback_unpublished_suffix(checkpoint)
        original = BimachineSLPProjector.clear_caches
        attempts = 0

        def fail_once(projector: BimachineSLPProjector) -> None:
            nonlocal attempts
            attempts += 1
            if attempts == 1:
                raise RuntimeError("interrupted cache refresh")
            original(projector)

        monkeypatch.setattr(BimachineSLPProjector, "clear_caches", fail_once)
        with pytest.raises(RuntimeError, match="interrupted cache refresh"):
            owner.validate_issued_occurrence(owner.initial)
        owner.validate_issued_occurrence(owner.initial)
        assert attempts == 2
    finally:
        owner.dispose()
        assert ledger.nodes == ledger.entries == 0


def test_rollback_does_not_remove_structurally_equal_unissued_handle() -> None:
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(
        ledger, digits_lsd(int(physical_seed(_U)), 10), base=10
    )
    try:
        issued = owner.initial
        forged = replace(issued)
        assert forged == issued and forged is not issued
        checkpoint = len(owner.arena.nodes)
        owner.rollback_punctured_application(checkpoint, forged, None)
        assert owner.issued_occurrence((issued.root, issued.temporal_steps)) is issued
        owner.validate_issued_occurrence(issued)
    finally:
        owner.dispose()
        assert ledger.nodes == ledger.entries == 0


def test_failed_candidate_publication_can_be_retried() -> None:
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )

    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(
        ledger, digits_lsd(int(physical_seed(_U)), 10), base=10
    )
    try:
        candidate = owner.candidate(owner.initial.root, 2)
        before = ledger.nodes, ledger.entries
        ledger.max_nodes = ledger.nodes
        with pytest.raises(BlockContextBudgetExceeded):
            owner.publish(candidate)
        assert (ledger.nodes, ledger.entries) == before
        assert owner.issued_occurrence((candidate.root, 2)) is None
        ledger.max_nodes = None
        assert owner.publish(candidate) is candidate
        owner.validate_issued_occurrence(candidate)
    finally:
        owner.dispose()
        assert ledger.nodes == ledger.entries == 0
