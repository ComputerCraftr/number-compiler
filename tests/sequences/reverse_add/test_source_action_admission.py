"""Input and ownership gates for original reverse/add source admission."""

from __future__ import annotations

from dataclasses import replace
from typing import cast

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.source_actions import ReverseActionArena


@pytest.mark.parametrize(
    ("seed", "base", "error"),
    (
        (-1, 10, ValueError),
        (1, 1, ValueError),
        (True, 10, TypeError),
        (1, False, TypeError),
        (1.0, 10, TypeError),
    ),
)
def test_source_admission_rejects_invalid_integer_geometry_without_mutation(
    seed: object, base: object, error: type[Exception]
) -> None:
    ledger = ResourceLedger()
    arena = ReverseActionArena(ledger)
    before = ledger.snapshot()

    with pytest.raises(error):
        arena.admit_source(cast(int, seed), cast(int, base))

    assert ledger.snapshot() == before
    snapshot = arena.audit_snapshot()
    assert not snapshot.sources.payload_view
    assert snapshot.source_authority is None
    arena.dispose()


def test_source_admission_is_ledger_owned_and_single_assignment() -> None:
    ledger = ResourceLedger()
    arena = ReverseActionArena(ledger)

    source = arena.admit_source(196, 10)
    assert arena.source(source).digits == (6, 9, 1)
    source_rows = tuple(
        row for row in ledger.inventory() if row.role == "reverse_original_source"
    )
    assert len(source_rows) == 1
    assert (source_rows[0].entries, source_rows[0].nodes) == (1, 1)

    before = ledger.snapshot()
    with pytest.raises(ValueError, match="already owns"):
        arena.admit_source(197, 10)
    assert ledger.snapshot() == before

    arena.dispose()
    assert ledger.entries == ledger.nodes == 0


def test_failed_source_reservation_does_not_publish_source_authority() -> None:
    # The identity and primitive descriptors use four entries; source admission
    # needs one additional entry and node.
    ledger = ResourceLedger(max_cache_entries=4)
    arena = ReverseActionArena(ledger)
    before = ledger.snapshot()

    with pytest.raises(RuntimeError, match="cache budget exceeded"):
        arena.admit_source(196, 10)

    # Decoding happened before the reservation failed. Retention is unchanged,
    # but this real failed work remains visible rather than being rolled back.
    assert ledger.snapshot() == replace(
        before, counters={"reverse_source_original_digit_decodes": 3}
    )
    snapshot = arena.audit_snapshot()
    assert not snapshot.sources.payload_view
    assert snapshot.source_authority is None
    arena.dispose()
    assert ledger.entries == ledger.nodes == 0
