from __future__ import annotations

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm


def _literal(seed: int, steps: int) -> int:
    value = seed
    for _ in range(steps):
        value = 2 * int(str(value)[::-1])
    return value


@pytest.mark.parametrize(
    "seed,steps",
    (
        (0, 0),
        (0, 6),
        (10, 0),
        (10, 1),
        (10, 6),
        (12, 4),
        (1001, 5),
        (4721, 8),
    ),
)
def test_scheduler_slp_matches_independent_literal_recurrence(
    seed: int, steps: int
) -> None:
    expected = _literal(seed, steps)
    with DoubleReverseTerm(seed, steps) as term:
        assert term.width() == len(str(expected))
        assert term.materialize(max_bits=expected.bit_length()) == expected
        assert term.digits() == tuple(
            int(character) for character in reversed(str(expected))
        )
        assert term.digit(0) == expected % 10


def test_trailing_zero_contraction_is_applied_on_every_step() -> None:
    with DoubleReverseTerm(10, 1) as term:
        assert term.materialize(max_bits=2) == 2
    with DoubleReverseTerm(100, 1) as term:
        assert term.materialize(max_bits=3) == 2


def test_materialization_checks_the_exact_value_not_a_decimal_width_bound() -> None:
    with DoubleReverseTerm(10, 1) as term:
        assert term.materialize(max_bits=2) == 2
        with pytest.raises(BlockContextBudgetExceeded, match="materialization budget"):
            term.materialize(max_bits=1)


def test_state_bit_cap_uses_exact_value_when_decimal_bound_is_inconclusive() -> None:
    with DoubleReverseTerm(10, 1, max_state_bits=4) as term:
        assert term.materialize(max_bits=4) == 2

    with DoubleReverseTerm(60, 1, max_state_bits=6) as term:
        assert term.materialize(max_bits=6) == 12
        term.prepare_endpoint()
        assert term.metrics()["double_reverse_threshold_conversion_bytes"] > 0
        assert len(term._threshold_memo) == 1

    with (
        DoubleReverseTerm(9, 1, max_state_bits=4) as term,
        pytest.raises(BlockContextBudgetExceeded, match="state-bit budget"),
    ):
        term.prepare_endpoint()


def test_step_and_initial_state_limits_are_checked_before_execution() -> None:
    with pytest.raises(BlockContextBudgetExceeded, match="step budget"):
        DoubleReverseTerm(10, 2, max_steps=1)
    with pytest.raises(BlockContextBudgetExceeded, match="source"):
        DoubleReverseTerm(10, 0, max_state_bits=3)


def test_partial_stream_cancellation_releases_temporary_traversal_storage() -> None:
    term = DoubleReverseTerm(4721, 8)
    stream = term.iter_digits()
    next(stream)
    stream.close()

    scratch = next(
        item for item in term._ledger.inventory() if item.name.endswith("-scratch")
    )
    assert scratch.entries == scratch.nodes == 0
    assert term.metrics()["double_reverse_output_stream_cancellations"] == 1
    term.dispose()
    assert sum(item.accounting_delta or 0 for item in term._ledger.inventory()) == 0


def test_closed_term_rejects_endpoint_and_context_access() -> None:
    term = DoubleReverseTerm(12, 2)
    term.dispose()
    with pytest.raises(ValueError, match="disposed"):
        term.prepare_endpoint()
    with pytest.raises(ValueError, match="disposed"):
        term.width()
    with pytest.raises(ValueError, match="disposed"):
        term.__enter__()


def test_successful_construction_keeps_scheduler_and_memos_live() -> None:
    with DoubleReverseTerm(10, 1) as term:
        assert not term._arena._closed
        assert not term._adapter._closed
        assert not term._threshold_memo._disposed
        assert term.materialize(max_bits=4) == 2
