from __future__ import annotations

from typing import TYPE_CHECKING

from devtools.verification.reverse_spacetime import ReverseAddCarrySlab
from devtools.verification.temporal_quotient import ReverseAddCarryCutState
from number_compiler.arithmetic.carry.event_memory import (
    carry_field,
    event_memory_horizon,
    pair_step,
)
from number_compiler.arithmetic.fields.dyadic_tile import iter_symbols, source_span

if TYPE_CHECKING:
    from number_compiler.arithmetic.fields.dyadic_tile import DyadicSpan


def _bootstrap_rows(
    seed_pair: tuple[int, int, int] = (7, 10, 7), base: int = 10
) -> tuple[DyadicSpan, ...]:
    pair = tuple(seed_pair)
    rows = []
    for _ in range(event_memory_horizon(base)):
        carry = carry_field(pair, base=base)
        rows.append(source_span(carry, blank=0, logical_length=len(carry)))
        pair, _ = pair_step(pair, base)
    return tuple(rows)


def test_reverse_cut_state_roundtrips_rows_without_row_lengths_in_identity() -> None:
    rows = _bootstrap_rows()
    cut = ReverseAddCarryCutState.from_rows(rows, base=10)
    assert cut.horizon == 20
    assert cut.cell_payload_bits == 40
    assert cut.row_values() == tuple(tuple(map(int, iter_symbols(row))) for row in rows)
    assert all(
        not isinstance(part, int) or part in (10, 20) for part in cut.canonical_key[:3]
    )
    # Geometry is represented by the dyadic tiles themselves, not a separate
    # row-width vector or source-length scalar.
    geometry = cut.canonical_key[3]
    assert isinstance(geometry, tuple)
    assert all(hasattr(tile, "width") for tile in geometry)


def test_reverse_slab_and_forcing_source_use_packed_cut_identity() -> None:
    rows = _bootstrap_rows()
    slab = ReverseAddCarrySlab(10, rows)
    assert slab.canonical_key == slab.cut_state.canonical_key
    assert "carry-history-source" not in repr(slab.canonical_key)
