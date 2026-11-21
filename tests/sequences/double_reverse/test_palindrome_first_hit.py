"""Bounded palindrome search respects physical clocks and source budgets."""

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm


def test_first_palindrome_matches_literal_prefix() -> None:
    for seed in (0, 7, 30, 73, 196, 903939):
        value = seed
        expected = None
        for generation in range(1, 41):
            value = 2 * int(str(value)[::-1])
            if str(value) == str(value)[::-1]:
                expected = generation
                break
        with DoubleReverseTerm(seed, 0, max_steps=40) as term:
            assert term.first_palindrome_within(40) == expected
            assert term.first_palindrome_within(0) is None


def test_first_palindrome_rejects_exhausted_budget_and_closed_term() -> None:
    term = DoubleReverseTerm(196, 0, max_steps=2)
    with pytest.raises(BlockContextBudgetExceeded):
        term.first_palindrome_within(3)
    term.dispose()
    with pytest.raises(ValueError, match="disposed"):
        term.first_palindrome_within(1)


def test_positive_pre_admission_hit_and_horizon_boundary() -> None:
    # 17 -> 142 -> 482 -> 568 -> 1730 -> 742 -> 494.
    with DoubleReverseTerm(17, 0, max_steps=6) as term:
        assert term.first_palindrome_within(5) is None
        assert term.first_palindrome_within(6) == 6
    # The seed is itself palindromic; only positive generations count.
    with DoubleReverseTerm(11, 0, max_steps=1) as term:
        assert term.first_palindrome_within(0) is None
        assert term.first_palindrome_within(1) == 1


def test_event_evidence_reuses_covered_prefix(monkeypatch: pytest.MonkeyPatch) -> None:
    from number_compiler.sequences.double_reverse import palindrome_event_cursor

    with DoubleReverseTerm(17, 0, max_steps=8) as term:
        assert term.first_palindrome_within(6) == 6

        def forbidden(*args: object, **kwargs: object) -> None:
            raise AssertionError("covered event evidence was replayed")

        monkeypatch.setattr(
            palindrome_event_cursor, "advance_palindrome_cursor", forbidden
        )
        assert term.first_palindrome_within(5) is None
        assert term.first_palindrome_within(8) == 6


@pytest.mark.parametrize(("seed", "hit"), ((17, 6), (196, None)))
def test_terminal_event_cursor_releases_physical_value(
    seed: int, hit: int | None
) -> None:
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.double_reverse.palindrome_event_cursor import (
        PalindromeCursor,
        advance_palindrome_cursor,
        cursor_nodes,
    )

    ledger = ResourceLedger()
    owner = ledger.register("palindrome-cursor-test", "scratch")
    try:
        result = advance_palindrome_cursor(
            PalindromeCursor(seed, 0, 0, seed), 64, ledger, owner, 4096
        )
        assert result.first_hit == hit
        assert result.first_hit is not None or result.c0_closed
        assert result.value is None
        assert cursor_nodes(0, result) == 8
        assert advance_palindrome_cursor(result, 64, ledger, owner, 4096) == result
    finally:
        ledger.mark_disposed(owner)
    assert ledger.nodes == ledger.entries == 0


def test_endpoint_prefix_does_not_prove_event_absence() -> None:
    with DoubleReverseTerm(11, 0, max_steps=4) as term:
        engine = term.source_adapter.temporal_hashlife
        engine.advance_source_prefix()
        engine.advance_source_prefix()
        assert term.first_palindrome_within(2) == 1
