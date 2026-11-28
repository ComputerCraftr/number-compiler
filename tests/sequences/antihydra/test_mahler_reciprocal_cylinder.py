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
from tests.sequences.antihydra.test_mahler_continued_fraction import literal_matrix


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


def test_upper_cuts_cancel_the_dyadic_inlet_before_row_construction() -> None:
    from number_compiler.sequences.antihydra.mahler_cf_reciprocal_tile import (
        reciprocal_row_interval,
    )

    class Inlet(int):
        def __mul__(self, other: object) -> int:
            raise AssertionError("upper-band selection multiplied the full inlet")

    for source in (19999, 20000, 39999, 40000, 79999, 80000, 390625):
        for tick in range(5):
            row = str(source * 5**tick)
            for start in range(len(row)):
                for end in range(start + 1, len(row) + 1):
                    inlet = Inlet(source) if len(row) - end >= tick else source
                    assert reciprocal_row_interval(
                        inlet, tick, len(row), start, end - start
                    ) == int(row[start:end])


def test_completed_row_prefix_skips_reopening_the_upper_band(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.antihydra import mahler_cf_reciprocal_tile as tiles
    from tests.sequences.antihydra.test_mahler_pow5_ordered_blocks import literal_action

    source = 5**38
    tile = tiles.ReciprocalTile(source, (27, 28), 0, 55, 38)
    expected = literal_action(str(source))

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("the completed row prefix must not reopen its physical cut")

    monkeypatch.setattr(tiles, "reciprocal_row_interval", forbidden)
    assert tile.segment(0, 27) == expected
    assert tile.segment(0, 0).entries == (1, 0, 0, 1)


def test_reciprocal_owner_rejects_forged_completed_row_prefix() -> None:
    from number_compiler.sequences.antihydra.mahler_cf_reciprocal_tile import (
        ReciprocalTile,
    )

    ledger = ResourceLedger(max_nodes=10_000)
    with Pow5OrderedBlockSource(ledger, reciprocal=True) as source:
        block = source.next_block(2, 100)
        tile = object.__getattribute__(source, "_tile")
        assert type(tile) is ReciprocalTile and tile.first_row_prefix is not None
        object.__setattr__(tile, "first_row_prefix", None)
        with pytest.raises(ValueError, match="source binding changed"):
            block.prefix(1)
    assert ledger.nodes == ledger.entries == 0


def test_reciprocal_owner_rejects_unsealed_row_action() -> None:
    ledger = ResourceLedger(max_nodes=10_000)
    with Pow5OrderedBlockSource(ledger, reciprocal=True) as source:
        block = source.next_block(2, 100)
        tile = object.__getattribute__(source, "_tile")
        object.__setattr__(tile, "_building", True)
        with pytest.raises(ValueError, match="source binding changed"):
            block.prefix(1)
    assert ledger.nodes == ledger.entries == 0


def test_reciprocal_leading_cut_conservative_bit_bound() -> None:
    from number_compiler.sequences.antihydra.mahler_cf_reciprocal_tile import (
        reciprocal_row_interval,
    )

    assert 2**83 < 10**25
    for width in range(1, 33):
        for count in range(1, width + 1):
            for t in range(4):
                for value in (0, 5**width, 10**width - 1, 10 ** (width + 2), -1):
                    whole = value * 5**t
                    skip = width - count
                    expected = (whole // 10**skip) % 10**count
                    assert (
                        reciprocal_row_interval(value, t, width, 0, count) == expected
                    )


def enable_prefix_bank(monkeypatch: pytest.MonkeyPatch) -> None:
    from struct import pack

    from number_compiler.arithmetic.fields.ordered_matrix import (
        ordered_decimal_continuant,
    )
    from number_compiler.sequences.antihydra import mahler_cf_reciprocal_tile as tiles

    class Native:
        @staticmethod
        def ordered_product(value: int, width: int) -> tuple[int, int, int, int]:
            return ordered_decimal_continuant(map(int, f"{value:0{width}d}")).entries

        @staticmethod
        def ordered_prefix_bank(value: int, width: int) -> bytes:
            word = f"{value:0{width}d}"
            return b"".join(
                pack("=4Q", *ordered_decimal_continuant(map(int, word[:i])).entries)
                for i in range(width + 1)
            )

    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_CF_CONTINUANT", "1")
    monkeypatch.setattr(tiles, "_native_continuant", Native)


def test_issued_last_row_actions_cover_every_clipped_segment(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    enable_prefix_bank(monkeypatch)
    from number_compiler.sequences.antihydra.mahler_cf_reciprocal_tile import (
        ReciprocalTile,
    )
    from tests.sequences.antihydra.test_mahler_pow5_ordered_blocks import literal_action

    for first in (9, 10, 18, 26, 30, 38):
        first_value = 5**first
        last = str(first_value * 5)
        for offset in (0, 3):
            first_width = len(str(first_value))
            tile = ReciprocalTile(
                first_value,
                (first_width, len(last)),
                offset,
                first_width - offset + len(last),
                first,
                True,
            )
            assert tile.last_prefixes is not None
            for start in range(len(last) + 1):
                for end in range(start, len(last) + 1):
                    assert tile.segment(
                        first_width - offset + start, end - start
                    ) == literal_action(last[start:end])


def test_indexed_prefixes_are_bound_to_the_receiving_owner(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    enable_prefix_bank(monkeypatch)
    ledger = ResourceLedger()
    with Pow5OrderedBlockSource(ledger, reciprocal=True) as source:
        for _ in range(9):
            source.next_block(4, 1000)
        source.next_block(1, 1000)
        block = source.next_block(2, 1000)
        tile = object.__getattribute__(source, "_tile")
        assert tile.last_prefixes is not None
        object.__setattr__(tile, "last_prefixes", tile.last_prefixes[:-1])
        with pytest.raises(ValueError, match="source binding changed"):
            block.prefix(1)
    assert ledger.nodes == ledger.entries == 0


@pytest.mark.parametrize(("horizon", "count"), ((2048, 269), (4096, 540)))
def test_live_cylinder_uses_indexed_final_row_without_reopening_digits(
    horizon: int,
    count: int,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    import json

    from number_compiler.api.cli import main
    from number_compiler.arithmetic.fields.ordered_matrix import Matrix2
    from number_compiler.sequences.antihydra import mahler_cf_reciprocal_tile as tiles

    enable_prefix_bank(monkeypatch)
    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_CF_RECIPROCAL", "1")
    original = tiles.ReciprocalTile.segment
    hits: list[tuple[int, int]] = []

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("indexed segment reopened physical digits")

    def segment(tile: tiles.ReciprocalTile, begin: int, length: int) -> Matrix2:
        if (
            not tile.sealed
            or tile.last_prefixes is None
            or begin < tile.widths[0] - tile.start
            or length == 0
        ):
            return original(tile, begin, length)
        with monkeypatch.context() as patch:
            patch.setattr(tiles, "reciprocal_row_interval", forbidden)
            result = original(tile, begin, length)
        hits.append((begin, length))
        return result

    monkeypatch.setattr(tiles.ReciprocalTile, "segment", segment)
    assert (
        main(
            [
                "antihydra",
                "--nth",
                "0",
                "--no-value",
                "--format",
                "json",
                "--info",
                "arithmetic.continued-fraction",
                "--safety-horizon",
                str(horizon),
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)["info"][
        "arithmetic.continued-fraction"
    ]
    stream = "".join(str(5**n) for n in range(1, 50))
    assert packet["coefficient_count"] == count
    assert packet["matrix"] == [
        list(row) for row in literal_matrix(list(map(int, stream[:count])))
    ]
    assert hits
    if horizon == 2048:
        # At 5**27 the 13-digit irregular head ends inside the length-five
        # probe. It consumes the hit and a clipped settled action in order.
        assert (28, 5) in hits


@pytest.mark.parametrize(("exponent", "ordinary_nodes"), ((26, 608), (38, 808)))
def test_indexed_prefix_admission_falls_back_before_opening_row(
    exponent: int,
    ordinary_nodes: int,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    enable_prefix_bank(monkeypatch)
    from tests.sequences.antihydra.test_mahler_pow5_ordered_blocks import literal_action

    ledger = ResourceLedger()
    with Pow5OrderedBlockSource(ledger, reciprocal=True) as source:
        for _ in range((exponent - 2) // 4):
            source.next_block(4, 1000)
        source.next_block(1, 1000)
        # Exactly enough capacity for the regular two-row reservation.
        ledger.tighten_limits(ledger.nodes + ordinary_nodes, None)
        block = source.next_block(2, 1000)
        tile = object.__getattribute__(source, "_tile")
        assert not tile.index_last and tile.last_prefixes is None
        first, second = str(5**exponent), str(5 ** (exponent + 1))
        assert block.product == literal_action(first + second)
        assert block.segment(len(first), 4) == literal_action(second[:4])
    assert ledger.nodes == ledger.entries == 0


def test_native_first_head_does_not_multiply_the_identity(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.fields.ordered_matrix import (
        MatrixEntries,
        multiply_entries,
    )
    from number_compiler.sequences.antihydra import mahler_cf_reciprocal_tile as tiles
    from tests.sequences.antihydra.test_mahler_pow5_ordered_blocks import literal_action

    enable_prefix_bank(monkeypatch)

    def multiply(left: MatrixEntries, right: MatrixEntries) -> MatrixEntries:
        assert left != (1, 0, 0, 1)
        return multiply_entries(left, right)

    monkeypatch.setattr(tiles, "multiply_entries", multiply)
    value = 5**18
    word = str(value)
    tile = tiles.ReciprocalTile(value, (len(word),), 0, len(word))
    assert tile.product == literal_action(word)
