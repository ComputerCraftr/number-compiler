from __future__ import annotations

from typing import TYPE_CHECKING, cast

import pytest

from number_compiler.arithmetic.contracts.exact_tree_context import (
    OriginalSourceConstruction,
)
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken, ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.hashlife.execution.field_images import SourceCellArena
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.range_runtime import (
    CollatzRadix4RangeArena,
    CollatzRadix4RangeID,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.field_images import SourceCellID


def _sources(bits: tuple[int, ...]) -> tuple[SourceCellArena, SourceCellID]:
    ledger = ResourceLedger()
    construction = OriginalSourceConstruction(
        ExactSource(bits, 2, blank=2, extent=len(bits), alphabet_size=2),
    )
    geometry = SourceGeometry(ledger, construction.source, construction)
    geometry.span(bits, 2, len(bits))
    sources = SourceCellArena(geometry)
    root = sources.resolve_forest(sources.forest(0, len(bits))).cells[0]
    return sources, root


def test_collatz_radix4_range_is_extensional_and_parent_composed() -> None:
    sources, root = _sources((1, 0, 1, 1, 0, 0, 1, 0))
    arena = CollatzRadix4RangeArena(sources)
    action = arena.summarize(root)
    record = arena.resolve(action)
    assert record.length == 4
    assert record.first_root_mismatch == 1
    assert record.mismatch_symbol == 3
    assert tuple(row.exit_carry for row in record.rows) == (0, 0, 0)
    assert arena.summarize(root) == action
    assert sources.ledger.counters["collatz_range_parent_hits"] == 1


def test_collatz_radix4_root_run_skips_as_one_parent() -> None:
    # Four radix-4 sentinel digits (...1111_4) represented as binary pairs.
    sources, root = _sources((1, 0) * 4)
    arena = CollatzRadix4RangeArena(sources)
    record = arena.resolve(arena.summarize(root))
    assert record.length == 4
    assert record.first_root_mismatch is None
    assert record.mismatch_symbol is None
    assert sources.ledger.counters["collatz_range_parent_publications"] <= 3


def test_collatz_range_rejects_integer_aliases_before_mutation() -> None:
    sources, root = _sources((1, 0, 0, 1))
    arena = CollatzRadix4RangeArena(sources)
    action = arena.summarize(root)
    before = sources.ledger.snapshot()
    for invalid in (
        action.local_id,
        True,
        action.__class__(ArenaToken("foreign-range"), action.kind, action.local_id),
        action.__class__(action.owner, "foreign-kind", action.local_id),
        action.__class__(action.owner, action.kind, action.local_id + 1),
    ):
        with pytest.raises((TypeError, ValueError, IndexError)):
            arena.resolve(cast(CollatzRadix4RangeID, invalid))
    after = sources.ledger.snapshot()
    assert after.entries == before.entries
    assert after.nodes == before.nodes


def test_collatz_range_matches_direct_three_carry_scan() -> None:
    bits = (1, 1, 0, 1, 1, 0, 0, 1)
    digits = tuple(bits[index] + 2 * bits[index + 1] for index in range(0, 8, 2))
    sources, root = _sources(bits)
    arena = CollatzRadix4RangeArena(sources)
    record = arena.resolve(arena.summarize(root))
    for incoming, row in enumerate(record.rows):
        carry = incoming
        nonzero: list[int] = []
        for position, digit in enumerate(digits):
            value = 3 * digit + carry
            carry = value >> 2
            if value & 3:
                nonzero.append(position)
        assert row.exit_carry == carry
        assert row.first_nonzero == (nonzero[0] if nonzero else None)
        assert row.last_nonzero == (nonzero[-1] if nonzero else None)
