"""Independent chronological oracles for bounded ordered ×5 actions."""

from dataclasses import replace
from unittest.mock import patch

import pytest

from number_compiler.arithmetic.automata.carry_spacetime_trace import Pow5SpatialTrace
from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp_interval import fold_slp_dag
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.ordered_matrix import Matrix2
from number_compiler.resources.ledger import LedgerReservation, ResourceLedger
from number_compiler.sequences.antihydra.mahler_pow5_ordered_blocks import (
    Pow5OrderedBlockSource,
)


def literal_action(word: str) -> Matrix2:
    value = Matrix2.identity()
    for digit in word:
        value = value.multiply(Matrix2.digit(int(digit) + 1))
    return value


@pytest.mark.parametrize("shared", [False, True])
@pytest.mark.parametrize("rows", [1, 2, 3, 4, 8])
def test_ordered_blocks_preserve_every_row_and_prefix(shared: bool, rows: int) -> None:
    ledger = ResourceLedger(max_nodes=10_000)
    with Pow5OrderedBlockSource(ledger, shared_cache=shared) as source:
        first = 1
        for _ in range(5):
            block = source.next_block(rows, 100_000)
            word = "".join(str(5**exponent) for exponent in range(first, first + rows))
            assert block.coefficient_count == len(word)
            assert block.product == literal_action(word)
            for count in range(len(word) + 1):
                assert block.prefix(count) == literal_action(word[:count])
            first += rows
    assert ledger.nodes == ledger.entries == 0


def test_spatial_width_exit_preserves_the_next_physical_row(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    widths: list[int] = []
    issue = Pow5SpatialTrace.issue

    def observe(
        trace: Pow5SpatialTrace, source: int, width: int, span: int
    ) -> tuple[tuple[int, int], ...]:
        widths.append(width)
        return issue(trace, source, width, span)

    monkeypatch.setattr(Pow5SpatialTrace, "issue", observe)
    ledger = ResourceLedger(max_nodes=10_000)
    with Pow5OrderedBlockSource(ledger, spatial=True) as source:
        for exponent in range(1, 49):
            block = source.next_block(1, 40)
            word = str(5**exponent)
            assert block.coefficient_count == len(word)
            assert block.product == literal_action(word)
    assert max(widths) == 32
    assert ledger.nodes == ledger.entries == 0


def test_clipped_row_resumes_without_skipping_digits() -> None:
    ledger = ResourceLedger()
    with Pow5OrderedBlockSource(ledger) as source:
        word = "".join(str(5**exponent) for exponent in range(1, 15))
        position = 0
        previous = None
        for budget in (1, 3, 2, 7, 11, 1, 4):
            block = source.next_block(8, budget)
            emitted = block.coefficient_count
            assert 1 <= emitted <= budget
            assert block.product == literal_action(word[position : position + emitted])
            position += emitted
            if previous is not None:
                with pytest.raises(ValueError, match="stale or foreign"):
                    _ = previous.product
            previous = block
    assert ledger.nodes == ledger.entries == 0


def test_foreign_or_stale_block_and_bad_lengths_are_rejected() -> None:
    with Pow5OrderedBlockSource(ResourceLedger()) as source:
        block = source.next_block(2, 10)
        with Pow5OrderedBlockSource(ResourceLedger()) as other:
            with pytest.raises(ValueError, match="stale or foreign"):
                _ = replace(block, _owner=other).product
        with pytest.raises(ValueError, match="stale or foreign"):
            _ = replace(block).product
        for invalid in (-1, block.coefficient_count + 1):
            with pytest.raises(ValueError):
                block.prefix(invalid)
    with pytest.raises(RuntimeError, match="closed"):
        _ = block.product


@pytest.mark.parametrize("shared", [False, True])
def test_bypass_rebuilds_only_the_requested_block_actions(shared: bool) -> None:
    ledger = ResourceLedger()
    with patch(
        "number_compiler.sequences.antihydra.mahler_pow5_ordered_blocks.fold_slp_dag",
        wraps=fold_slp_dag,
    ) as compile_word:
        with Pow5OrderedBlockSource(ledger, shared_cache=shared) as source:
            block = source.next_block(4, 100)
            assert compile_word.call_count == 1
            assert block.prefix(3) == literal_action("525")
            assert block.prefix(3) == literal_action("525")
            assert compile_word.call_count == (1 if shared else 3)
    assert ledger.nodes == ledger.entries == 0


def test_failed_block_admission_preserves_previous_authority() -> None:
    ledger = ResourceLedger(max_nodes=1_000)
    with Pow5OrderedBlockSource(ledger) as source:
        old = source.next_block(1, 1)
        with pytest.raises(BlockContextBudgetExceeded):
            source.next_block(64, 100_000)
        assert old.product == Matrix2.digit(6)
        following = source.next_block(1, 2)
        assert following.product == literal_action("25")
    assert ledger.nodes == ledger.entries == 0


def test_bounded_source_reuses_owner_slots_across_blocks() -> None:
    ledger = ResourceLedger(max_nodes=10_000)
    with Pow5OrderedBlockSource(ledger) as source:
        owners = ledger.owner_count
        for _ in range(50):
            block = source.next_block(4, 20)
            assert 0 < block.coefficient_count <= 20
        assert ledger.owner_count == owners
    assert ledger.nodes == ledger.entries == 0


@pytest.mark.parametrize("exception_type", [RuntimeError, KeyboardInterrupt])
def test_failed_arena_retirement_revokes_block_and_allows_cleanup_retry(
    monkeypatch: pytest.MonkeyPatch, exception_type: type[BaseException]
) -> None:
    ledger = ResourceLedger()
    source = Pow5OrderedBlockSource(ledger)
    block = source.next_block(2, 20)
    original = LedgerSLPArena.rollback_unpublished_suffix
    failed = False

    def interrupted(arena: LedgerSLPArena, first_new_node: int) -> None:
        nonlocal failed
        if not failed:
            failed = True
            raise exception_type("injected source retirement failure")
        original(arena, first_new_node)

    monkeypatch.setattr(LedgerSLPArena, "rollback_unpublished_suffix", interrupted)
    with pytest.raises(exception_type, match="retirement failure"):
        source.next_block(2, 20)
    with pytest.raises(RuntimeError, match="closed"):
        _ = block.product
    source.close()
    assert ledger.nodes == ledger.entries == 0


def test_failed_construction_rollback_revokes_and_allows_cleanup_retry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    source = Pow5OrderedBlockSource(ledger)
    block = source.next_block(2, 20)

    def fail_multiply(_left: Matrix2, _right: Matrix2) -> Matrix2:
        raise ValueError("injected construction failure")

    def fail_rollback(_arena: LedgerSLPArena, _first_new_node: int) -> None:
        raise RuntimeError("injected rollback failure")

    monkeypatch.setattr(Matrix2, "multiply", fail_multiply)
    monkeypatch.setattr(LedgerSLPArena, "rollback_unpublished_suffix", fail_rollback)
    with pytest.raises(RuntimeError, match="rollback failure"):
        source.next_block(2, 20)
    with pytest.raises(RuntimeError, match="closed"):
        _ = block.product
    source.close()
    assert ledger.nodes == ledger.entries == 0


def test_failed_candidate_reservation_close_is_retained_for_retry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    source = Pow5OrderedBlockSource(ledger)
    block = source.next_block(2, 20)
    original = LedgerReservation.close
    failed = False

    def fail_multiply(_left: Matrix2, _right: Matrix2) -> Matrix2:
        raise ValueError("injected construction failure")

    def interrupted(reservation: LedgerReservation) -> None:
        nonlocal failed
        if not failed:
            failed = True
            raise RuntimeError("injected reservation close failure")
        original(reservation)

    monkeypatch.setattr(Matrix2, "multiply", fail_multiply)
    monkeypatch.setattr(LedgerReservation, "close", interrupted)
    with pytest.raises(RuntimeError, match="reservation close failure"):
        source.next_block(2, 20)
    with pytest.raises(RuntimeError, match="closed"):
        _ = block.product
    source.close()
    assert ledger.nodes == ledger.entries == 0
