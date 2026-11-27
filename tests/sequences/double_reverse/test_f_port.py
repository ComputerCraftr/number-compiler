"""The four-cell quotient preserves both literal stencil outputs."""

from collections.abc import Callable

import pytest

from number_compiler.sequences.double_reverse import stencil_moore
from number_compiler.sequences.double_reverse.stencil_moore import stencil_cell


def test_f_port_matches_every_decimal_four_cell_window() -> None:
    for a in range(10):
        for b in range(10):
            for c in range(10):
                for d in range(10):
                    assert stencil_moore.f_port_cell(a, b, c, d) == (
                        stencil_cell(a, b, c),
                        stencil_cell(b, c, d),
                    )


def test_equivalent_ports_do_not_recompute_cell_arithmetic(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    expected = stencil_moore.f_port_cell(1, 7, 3, 2)

    def forbidden(*_args: int) -> int:
        raise AssertionError("recomputed a certified F-port row")

    monkeypatch.setattr(stencil_moore, "stencil_from_ports", forbidden)
    evaluate: Callable[[int, int, int, int], tuple[int, int]] = (
        stencil_moore.f_port_cell
    )
    assert evaluate(4, 7, 3, 7) == expected


def test_port_responses_match_the_literal_minimal_partition() -> None:
    literal_rows = {
        (a, b): tuple(stencil_cell(a, b, c) for c in range(10))
        for a in range(10)
        for b in range(10)
    }
    public_rows = {
        (a, b): tuple(stencil_moore.f_port_cell(a, b, c, 0)[0] for c in range(10))
        for a in range(10)
        for b in range(10)
    }
    assert public_rows == literal_rows
    assert len(set(literal_rows.values())) == 10

    literal_columns = {
        c: tuple(literal_rows[(a, b)][c] for a in range(10) for b in range(10))
        for c in range(10)
    }
    public_columns = {
        c: tuple(public_rows[(a, b)][c] for a in range(10) for b in range(10))
        for c in range(10)
    }
    assert public_columns == literal_columns
    assert len(set(literal_columns.values())) == 3
