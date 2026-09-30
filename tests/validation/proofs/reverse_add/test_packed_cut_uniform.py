"""Exact oracle regression; these objects are not production carriers."""

from typing import Never

import pytest

from number_compiler.arithmetic.carry.event_memory import (
    event_memory_horizon as _canonical_event_memory_horizon,
)


def test_cut_builds_and_validates_large_uniform_rows_without_flattening(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import devtools.verification.temporal_quotient as quotient
    from number_compiler.arithmetic.fields.dyadic_tile import uniform_span

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("eager row traversal")

    monkeypatch.setattr(quotient, "iter_symbols", forbidden)
    horizon = _canonical_event_memory_horizon(10)
    rows = tuple(uniform_span(0, 1 << 30, index % 2) for index in range(horizon))
    state = quotient.ReverseAddCarryCutState.from_rows(rows)
    assert state.spatial_cells == 1 << 30
    assert state.distinct_cell_symbols == 1
    assert len(state.tape.chunks) == 1
