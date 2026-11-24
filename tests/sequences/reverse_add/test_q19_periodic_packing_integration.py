"""Quotient-first Q19 publication/recovery over authentic repeated source words."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.q19_broadword_publisher import PackedQ19
from number_compiler.sequences.reverse_add.q19_output import ReversePairQ19OutputOwner
from number_compiler.sequences.reverse_add.q19_periodic_packing import (
    packed_repeated_motif,
    publish_packed_word,
    recover_repeated_word,
)
from tests.support.private_attributes import private_test_attribute


def packed_pattern(motif: tuple[int, ...], count: int) -> int:
    return sum(motif[i % len(motif)] << (6 * i) for i in range(count))


@pytest.mark.parametrize("motif", ((2,), (4, 13), (2, 10, 8), (17, 3, 14, 6)))
@pytest.mark.parametrize("count", (128, 129, 513))
@pytest.mark.parametrize("center", (None, 0, 4, 9))
def test_repeated_q19_folds_exactly_from_symbolic_dag(
    motif: tuple[int, ...], count: int, center: int | None
) -> None:
    ledger = ResourceLedger()
    scratch = ledger.register("q19-repeated-workspace", "scratch")
    arena = LedgerSLPArena(ledger, "q19-repeated", "test")
    frame = PackedQ19(packed_pattern(motif, count), count, center)
    try:
        root = publish_packed_word(arena, frame)
        assert root is not None
        assert arena.nodes[root].length == count + 2 + int(center is not None)
        assert recover_repeated_word(arena, root, frame.width, ledger, scratch) == frame
        assert ledger.account_usage(scratch) == (0, 0)
    finally:
        arena.dispose()
        ledger.mark_disposed(scratch)
    assert ledger.entries == ledger.nodes == 0


def test_ordered_motifs_may_not_merge_after_a_rotation() -> None:
    n = 513
    a = packed_pattern((2, 13, 6), n)
    b = packed_pattern((13, 6, 2), n)
    assert a != b
    assert packed_repeated_motif(a, n) != packed_repeated_motif(b, n)
    changed = a ^ (7 << (6 * 213))
    assert packed_repeated_motif(changed, n) is None


@pytest.mark.parametrize(
    ("opening", "middle", "closing", "message"),
    ((19, 4, 21, "marker"), (20, 3, 21, "center"), (20, 4, 20, "marker")),
)
def test_repeated_decode_rejects_bad_markers_and_center(
    opening: int, middle: int, closing: int, message: str
) -> None:
    ledger = ResourceLedger()
    scratch = ledger.register("q19-invalid-workspace", "scratch")
    arena = LedgerSLPArena(ledger, "q19-invalid", "test")
    try:
        root = arena.concat_many(
            (
                arena.terminal(opening),
                arena.repeat(arena.terminal(2), 128),
                arena.terminal(middle),
                arena.terminal(closing),
            )
        )
        with pytest.raises(ValueError, match=message):
            recover_repeated_word(arena, root, 257, ledger, scratch)
        assert ledger.account_usage(scratch) == (0, 0)
    finally:
        arena.dispose()
        ledger.mark_disposed(scratch)
    assert ledger.entries == ledger.nodes == 0


def test_issued_source_reuses_algebraic_fold_without_symbol_replay(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    digits = (1,) * 2048
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits, base=10)
    try:
        one = owner.publish_broadword_source(1)
        expected = PackedQ19.from_digits(digits)

        def forbidden(*_args: object, **_kwargs: object) -> object:
            raise AssertionError("reconstructed repeated Q19 occurrences")

        monkeypatch.setattr(
            "number_compiler.sequences.reverse_add.q19_output_publication.iter_symbols",
            forbidden,
        )
        resume = private_test_attribute(owner, "_resume_owned_broadword_frame")
        assert callable(resume) and resume(one) == expected
        # This is an actual production continuation. The remaining one
        # physical transition is still honestly counted, not hidden as a
        # supposed quotient-first temporal power.
        later = owner.publish_broadword_source(2)
        assert later.pair_width == 2048
        assert ledger.counters["reverse_q19_broadword_semantic_steps"] == 1
    finally:
        owner.dispose()
    assert ledger.entries == ledger.nodes == 0


def test_repeated_fold_capacity_miss_uses_exact_streaming_fallback(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.reverse_add import q19_periodic_packing

    digits = (1,) * 2048
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits, base=10)
    try:
        occurrence = owner.publish_broadword_source(1)

        def refuse(*_args: object, **_kwargs: object) -> PackedQ19:
            raise BlockContextBudgetExceeded("optional packed fold capacity")

        monkeypatch.setattr(q19_periodic_packing, "recover_repeated_word", refuse)
        resume = private_test_attribute(owner, "_resume_owned_broadword_frame")
        assert callable(resume) and resume(occurrence) == PackedQ19.from_digits(digits)
    finally:
        owner.dispose()
    assert ledger.entries == ledger.nodes == 0


def test_q19_small_dense_sources_keep_existing_publisher() -> None:
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, (6, 9, 1), base=10)
    try:
        original = owner.publish_broadword_source(128)
        after = owner.publish_broadword_source(256)
        assert original.temporal_steps == 128
        assert after.temporal_steps == 256
        assert ledger.counters["reverse_q19_broadword_semantic_steps"] == 255
    finally:
        owner.dispose()
    assert ledger.entries == ledger.nodes == 0
