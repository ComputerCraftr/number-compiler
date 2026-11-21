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
