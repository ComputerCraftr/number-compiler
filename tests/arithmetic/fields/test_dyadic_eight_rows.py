"""Compare every eight-row terminal restriction with the physical digit word."""

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields import dyadic_eight_rows
from number_compiler.arithmetic.fields.dyadic_eight_rows import eight_row_interval
from number_compiler.arithmetic.fields.ordered_matrix import (
    Matrix2,
    compile_dyadic_ordered_band,
)


def test_every_core_and_right_shear_clip() -> None:
    identity = Matrix2.identity()
    for q in range(1280):
        digits = [(q >> j) % 10 for j in range(8)]
        for start in range(9):
            expected = identity
            assert eight_row_interval(q, start, start) == expected
            for stop in range(start + 1, 9):
                expected = expected.multiply(Matrix2.digit(digits[stop - 1] + 1))
                assert eight_row_interval(q, start, stop) == expected


def test_refusal_precedes_terminal_lookup(monkeypatch: pytest.MonkeyPatch) -> None:
    calls: list[int] = []

    def reserve(_q: int, _rows: int, bits: int) -> None:
        calls.append(bits)
        if bits > 1024:
            raise BlockContextBudgetExceeded("table does not fit")

    def forbidden(_q: int) -> Matrix2:
        raise AssertionError("refused terminal was opened")

    expected = eight_row_interval(991)
    monkeypatch.setattr(dyadic_eight_rows, "eight_row_interval", forbidden)
    assert compile_dyadic_ordered_band(991, 8, 1, reserve, use_memo=False) == expected
    assert len(calls) == 2 and calls[0] > 1024 and calls[1] == 0


def test_reservation_failure_propagates() -> None:
    def broken(_q: int, _rows: int, _bits: int) -> None:
        raise RuntimeError("broken workspace")

    with pytest.raises(RuntimeError, match="broken workspace"):
        compile_dyadic_ordered_band(9, 8, 1, broken, use_memo=True)


def test_real_band_releases_scratch_after_refusal_and_interruption(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.antihydra.mahler_continued_fraction import (
        continued_fraction_band,
    )

    def interrupted(_q: int) -> Matrix2:
        raise InterruptedError("cancelled admitted terminal")

    monkeypatch.setattr(dyadic_eight_rows, "eight_row_interval", interrupted)
    tight = ResourceLedger(max_nodes=300)
    packet = continued_fraction_band(16, 4, 1, 8, ledger=tight)
    assert packet["status"] == "available" and packet["lifted_source"] == 370
    assert tight.nodes == tight.entries == 0
    admitted = ResourceLedger(max_nodes=10000)
    with pytest.raises(InterruptedError, match="cancelled admitted terminal"):
        continued_fraction_band(16, 4, 1, 8, ledger=admitted)
    assert admitted.nodes == admitted.entries == 0
