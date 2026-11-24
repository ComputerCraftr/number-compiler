"""Independent decimal and authority checks for the finite CF source."""

from dataclasses import replace

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.ordered_matrix import Matrix2
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.antihydra.mahler_pow5_source import Pow5CFSource


def literal_matrix(digits: str) -> Matrix2:
    value = Matrix2.identity()
    for digit in digits:
        value = value.multiply(Matrix2.digit(int(digit) + 1))
    return value


@pytest.mark.parametrize("shared", [False, True])
def test_rows_and_ordered_intervals_match_integer_oracle(shared: bool) -> None:
    ledger = ResourceLedger()
    with Pow5CFSource(ledger, shared_cache=shared) as source:
        row = source.next_row()
        assert row.exponent == row.width == 1
        assert row.segment(0, 1) == Matrix2.digit(6)
        for exponent in range(2, 46):
            previous, row = row, source.next_row()
            expected = str(5**exponent)
            assert row.exponent == exponent
            assert row.width == len(expected)
            assert "".join(str(row.digit_at(i)) for i in range(row.width)) == expected
            for begin, end in (
                (0, row.width),
                (0, 1),
                (row.width - 1, row.width),
                (row.width // 3, row.width),
            ):
                assert row.segment(begin, end - begin) == literal_matrix(
                    expected[begin:end]
                )
            with pytest.raises(ValueError, match="stale or foreign"):
                _ = previous.width
    assert ledger.nodes == 0
    assert ledger.entries == 0
    with pytest.raises(RuntimeError, match="closed"):
        _ = row.width


def test_suffix_clock_does_not_walk_source_digits(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with Pow5CFSource(ResourceLedger()) as source:
        row = source.next_row()
        for _ in range(29):
            row = source.next_row()
        expected = str(5**30)[-4:]

        def forbidden(*_args: object, **_kwargs: object) -> None:
            raise AssertionError("source subtree must not be folded")

        monkeypatch.setattr(source, "checked_segment", forbidden)
        assert row.segment(row.width - 4, 4) == literal_matrix(expected)


def test_forged_row_and_out_of_bounds_are_rejected() -> None:
    with Pow5CFSource(ResourceLedger()) as source:
        row = source.next_row()
        for forged in (
            replace(row, _exponent=2),
            replace(row, _root=-1),
            replace(row, _epoch=0),
        ):
            with pytest.raises(ValueError, match="stale or foreign"):
                _ = forged.exponent
        for start, length in ((-1, 1), (0, 0), (0, 2)):
            with pytest.raises(ValueError, match="outside"):
                row.segment(start, length)
        with pytest.raises(ValueError, match="outside"):
            row.digit_at(row.width)


def test_foreign_owner_and_failed_row_publication_preserve_current_source() -> None:
    ledger = ResourceLedger()
    with Pow5CFSource(ledger) as source, Pow5CFSource(ResourceLedger()) as foreign:
        row = source.next_row()
        foreign.next_row()
        with pytest.raises(ValueError, match="stale or foreign"):
            _ = replace(row, _source=foreign).width
        retained = ledger.nodes
        ledger.tighten_limits(retained, ledger.max_cache_entries)
        with pytest.raises(BlockContextBudgetExceeded):
            source.next_row()
        assert row.exponent == 1
        assert row.digit_at(0) == 5
        assert ledger.nodes == retained
    assert ledger.nodes == ledger.entries == 0


def test_compaction_retires_prior_rows_and_bounds_ledger() -> None:
    ledger = ResourceLedger(max_nodes=10_000)
    with Pow5CFSource(ledger) as source:
        previous = source.next_row()
        for exponent in range(2, 201):
            row = source.next_row()
            if exponent % 25 == 0:
                assert "".join(str(row.digit_at(i)) for i in range(row.width)) == str(
                    5**exponent
                )
        with pytest.raises(ValueError, match="stale or foreign"):
            _ = previous.width
        assert ledger.peak_nodes < 10_000
    assert ledger.nodes == 0


def test_failed_compaction_revokes_and_cleans_source(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    source = Pow5CFSource(ledger)

    def fail() -> None:
        raise RuntimeError("injected compaction failure")

    monkeypatch.setattr(source, "_compact_current_root", fail)
    with pytest.raises(RuntimeError, match="injected compaction failure"):
        for _ in range(300):
            source.next_row()
    with pytest.raises(RuntimeError, match="closed"):
        source.next_row()
    assert ledger.nodes == 0
