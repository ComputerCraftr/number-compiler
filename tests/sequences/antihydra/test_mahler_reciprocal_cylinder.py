"""Physical source and cleanup checks for the bounded reciprocal cylinder."""

import pytest

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.resources.ledger import LedgerReservation, ResourceLedger
from number_compiler.sequences.antihydra.mahler_continued_fraction_cylinder import (
    continued_fraction_cylinder,
)
from number_compiler.sequences.antihydra.mahler_pow5_ordered_blocks import (
    Pow5OrderedBlock,
    Pow5OrderedBlockSource,
)
from tests.sequences.antihydra.test_mahler_cf_cylinder import literal_cylinder


@pytest.mark.parametrize("horizon", (0, 20, 63))
def test_short_cylinder_uses_reciprocal_source_without_chronological_row_staging(
    horizon: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    calls = 0
    original = Pow5OrderedBlockSource.next_block

    def issue(
        source: Pow5OrderedBlockSource, rows: int, limit: int
    ) -> Pow5OrderedBlock:
        nonlocal calls
        calls += 1
        return original(source, rows, limit)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("the short reciprocal route opened the other source")

    monkeypatch.setattr(Pow5OrderedBlockSource, "next_block", issue)
    monkeypatch.setattr(LedgerSLPArena, "terminal", forbidden)
    ledger = ResourceLedger(max_nodes=10_000)
    result = continued_fraction_cylinder(horizon, 500, ledger=ledger)
    count, matrix = literal_cylinder(horizon, 500)
    assert (result["coefficient_count"], result["matrix"]) == (count, matrix)
    assert calls > 0
    assert ledger.nodes == ledger.entries == 0


def test_reciprocal_blocks_reject_stale_epochs_and_restore_the_ledger() -> None:
    ledger = ResourceLedger(max_nodes=10_000)
    with Pow5OrderedBlockSource(ledger, reciprocal=True) as source:
        first = source.next_block(2, 3)
        assert first.coefficient_count == 3
        second = source.next_block(2, 2)
        with pytest.raises(ValueError, match="stale or foreign"):
            first.prefix(1)
        assert second.coefficient_count == 2
    assert ledger.nodes == ledger.entries == 0


@pytest.mark.parametrize("exception_type", [RuntimeError, KeyboardInterrupt])
def test_reciprocal_failure_preserves_previous_block_and_releases_staging(
    monkeypatch: pytest.MonkeyPatch, exception_type: type[BaseException]
) -> None:
    from number_compiler.sequences.antihydra.mahler_cf_reciprocal_tile import (
        ReciprocalTile,
    )

    ledger = ResourceLedger(max_nodes=10_000)
    with Pow5OrderedBlockSource(ledger, reciprocal=True) as source:
        first = source.next_block(1, 1)
        expected = first.product
        reserved = ledger.nodes

        def fail(_tile: ReciprocalTile, _start: int, _length: int) -> None:
            raise exception_type("interrupted reciprocal compilation")

        monkeypatch.setattr(ReciprocalTile, "segment", fail)
        with pytest.raises(exception_type, match="interrupted"):
            source.next_block(2, 4)
        assert first.product == expected
        assert ledger.nodes == reserved
    assert ledger.nodes == ledger.entries == 0


def test_reciprocal_failed_reservation_close_revokes_and_can_retry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.antihydra.mahler_cf_reciprocal_tile import (
        ReciprocalTile,
    )

    ledger = ResourceLedger(max_nodes=10_000)
    source = Pow5OrderedBlockSource(ledger, reciprocal=True)
    first = source.next_block(1, 1)
    original = LedgerReservation.close
    failed = False

    def fail_compile(_tile: ReciprocalTile, _start: int, _length: int) -> None:
        raise ValueError("injected compilation failure")

    def fail_close(reservation: LedgerReservation) -> None:
        nonlocal failed
        if not failed:
            failed = True
            raise RuntimeError("injected reservation close failure")
        original(reservation)

    monkeypatch.setattr(ReciprocalTile, "segment", fail_compile)
    monkeypatch.setattr(LedgerReservation, "close", fail_close)
    with pytest.raises(RuntimeError, match="reservation close failure"):
        source.next_block(2, 4)
    with pytest.raises(RuntimeError, match="closed"):
        _ = first.product
    source.close()
    assert ledger.nodes == ledger.entries == 0


@pytest.mark.parametrize(("field", "forged"), [("_threshold", 100), ("_width", 2)])
def test_reciprocal_width_clock_refuses_wrong_source_before_publication(
    field: str, forged: int
) -> None:
    ledger = ResourceLedger(max_nodes=10_000)
    with Pow5OrderedBlockSource(ledger, reciprocal=True) as source:
        first = source.next_block(1, 1)
        expected = first.product
        reserved = ledger.nodes
        object.__setattr__(source, field, forged)
        with pytest.raises(ValueError, match="cursor binding"):
            source.next_block(1, 3)
        assert first.product == expected
        assert ledger.nodes == reserved
    assert ledger.nodes == ledger.entries == 0


def test_reciprocal_tile_source_binding_is_immutable() -> None:
    from number_compiler.sequences.antihydra.mahler_cf_reciprocal_tile import (
        ReciprocalTile,
    )

    tile = ReciprocalTile(5, (1,), 0, 1)
    with pytest.raises(AttributeError):
        tile.quotient = 6  # type: ignore[misc]
    with pytest.raises(AttributeError):
        tile.widths = (2,)  # type: ignore[misc]


def test_reciprocal_block_rejects_retargeted_tile() -> None:
    from number_compiler.sequences.antihydra.mahler_cf_reciprocal_tile import (
        ReciprocalTile,
    )

    ledger = ResourceLedger(max_nodes=10_000)
    with Pow5OrderedBlockSource(ledger, reciprocal=True) as source:
        block = source.next_block(1, 1)
        tile = object.__getattribute__(source, "_tile")
        assert type(tile) is ReciprocalTile
        object.__setattr__(tile, "quotient", 6)
        with pytest.raises(ValueError, match="source binding changed"):
            _ = block.product
    assert ledger.nodes == ledger.entries == 0


def test_reciprocal_source_rejects_a_forged_same_width_cursor() -> None:
    ledger = ResourceLedger(max_nodes=10_000)
    with Pow5OrderedBlockSource(ledger, reciprocal=True) as source:
        first = source.next_block(1, 1)
        expected = first.product
        reserved = ledger.nodes
        object.__setattr__(source, "_value", 6)
        with pytest.raises(ValueError, match="cursor binding changed"):
            source.next_block(1, 1)
        assert first.product == expected
        assert ledger.nodes == reserved
    assert ledger.nodes == ledger.entries == 0


def test_reciprocal_block_rejects_retargeted_coefficient_ring() -> None:
    ledger = ResourceLedger(max_nodes=10_000)
    with Pow5OrderedBlockSource(ledger, reciprocal=True) as source:
        block = source.next_block(1, 1)
        product = block.product
        object.__setattr__(product, "modulus", 7)
        with pytest.raises(ValueError, match="source binding changed"):
            _ = block.product
    assert ledger.nodes == ledger.entries == 0


def test_reciprocal_block_rejects_forged_source_phase() -> None:
    from number_compiler.sequences.antihydra.mahler_cf_reciprocal_tile import (
        ReciprocalTile,
    )

    ledger = ResourceLedger(max_nodes=10_000)
    with Pow5OrderedBlockSource(ledger, reciprocal=True) as source:
        block = source.next_block(3, 20)
        tile = object.__getattribute__(source, "_tile")
        assert type(tile) is ReciprocalTile and tile.first_exponent is not None
        object.__setattr__(tile, "first_exponent", tile.first_exponent + 1)
        with pytest.raises(ValueError, match="source binding changed"):
            _ = block.product


def test_initial_reciprocal_cut_uses_issued_source_directly() -> None:
    from number_compiler.sequences.antihydra.mahler_cf_reciprocal_tile import (
        reciprocal_row_interval,
    )

    class IssuedInitialRow(int):
        def __mul__(self, other: object) -> int:
            raise AssertionError("initial reciprocal row multiplied the issued source")

    source = IssuedInitialRow(390625)
    assert reciprocal_row_interval(source, 0, 6, 0, 2) == 39
    assert reciprocal_row_interval(source, 0, 6, 2, 2) == 6
    assert reciprocal_row_interval(source, 0, 6, 4, 2) == 25
