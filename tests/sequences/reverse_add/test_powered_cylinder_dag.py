"""Finite powered consumer and shared-tile polynomial laws."""

from __future__ import annotations

from collections.abc import Callable, Iterator
from typing import Never, cast

import pytest

import number_compiler.hashlife.observation.tile_cylinder as tile_cylinder
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.polynomials.twisted_observer import (
    TwistedCylinderProjection,
    first_mirror_obstruction,
)
from number_compiler.hashlife.tiles.tiles import TileAlphabet, TileArena, TileID
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.stores import LedgerList
from number_compiler.sequences.reverse_add import power as powered_module
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from tests.support.private_attributes import private_test_attribute
from tests.support.reverse_cutover import (
    assert_mirror_scratch_released,
    assert_q19_output_authority,
)

_sheet = cast(
    Callable[[TileArena, TileID, int, int, int], TwistedCylinderProjection],
    private_test_attribute(tile_cylinder, "_sheet"),
)


@pytest.mark.parametrize("seed", (196, 89, 99, 121))
def test_powered_mirror_consumes_tiles_without_point_queries(
    seed: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    expected = seed
    for _ in range(3):
        expected += int(str(expected)[::-1])
    digits = tuple(int(x) for x in reversed(str(expected)))
    reference = first_mirror_obstruction(len(digits), digits.__getitem__)
    term = ReverseAddPoweredTerm(seed, 3)

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("powered cylinder replayed scalar point queries")

    monkeypatch.setattr(ReverseAddPoweredTerm, "digit", forbidden)
    assert term.mirror_obstruction() == reference
    counters = term.resource_ledger.counters
    # The Q19 pair grammar is the completed output authority; its digit stream
    # feeds the measured output consumer without point or tile-sheet visits.
    assert counters["reverse_output_stream_emitted_digits"] == len(digits)
    # The third digit word normalizes the pair field after two transitions.
    assert counters.get("reverse_q19_punctured_t2_applications", 0) == 1
    assert counters.get("reverse_q19_punctured_t4_applications", 0) == 0
    assert (
        2 * counters.get("reverse_q19_punctured_t2_applications", 0)
        + 4 * counters.get("reverse_q19_punctured_t4_applications", 0)
        == 2
    )
    assert counters.get("source_image_primitive_applications", 0) == 0
    assert counters.get("reverse_q19_primitive_pair_applications", 0) == 0
    # The demanded observer consumes the completed output grammar directly;
    # this is the stream traversal counter (pair-output section visits belong
    # to the separately instrumented primitive evaluator).
    assert counters["recursive_output_stream_node_visits"] > 0
    assert_q19_output_authority(term)
    assert counters.get("temporal_point_requests", 0) == 0
    assert counters.get("point_response_requests", 0) == 0
    for account in term.resource_ledger.inventory():
        if account.name.startswith("tile-cylinder-"):
            assert account.entries == account.nodes == 0
            assert account.observed_entries == account.observed_nodes == 0
    assert collect_ledger_metrics(term.resource_ledger).resource_audit_complete == 1
    assert term.metrics().resource_audit_complete == 1
    assert term.metrics().forbidden_future_payloads == 0
    assert_mirror_scratch_released(term)
    owners = len(term.resource_ledger.inventory())
    assert term.mirror_obstruction(first_width=2) == first_mirror_obstruction(
        len(digits), digits.__getitem__, first_width=2
    )
    assert len(term.resource_ledger.inventory()) == owners


def test_powered_mirror_closes_and_accounts_for_cancelled_output(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = ReverseAddPoweredTerm(196, 3)

    def abort_after_one_digit(
        _width: int,
        digits: Iterator[int],
        *,
        ledger: ResourceLedger,
        scratch: LedgerList[int],
        first_width: int = 1,
    ) -> Never:
        assert ledger is term.resource_ledger
        assert not scratch
        _ = first_width
        next(digits)
        raise RuntimeError("observer stopped after its first output digit")

    monkeypatch.setattr(
        powered_module,
        "mirror_obstruction_from_output",
        abort_after_one_digit,
    )
    with pytest.raises(RuntimeError, match="observer stopped"):
        term.mirror_obstruction()

    counters = term.resource_ledger.counters
    assert counters["reverse_output_stream_requests"] == 1
    assert counters["reverse_output_stream_emitted_digits"] == 1
    assert counters["reverse_output_stream_cancellations"] == 1
    assert counters["reverse_output_stream_failures"] == 0
    assert counters.get("temporal_point_requests", 0) == 0


def test_powered_mirror_budget_refusal_leaves_scratch_empty() -> None:
    term = ReverseAddPoweredTerm(196, 3)
    width = term.width()
    ledger = term.resource_ledger
    before = ledger.entries, ledger.nodes
    ledger.max_nodes = ledger.nodes + 2 * width - 1

    with pytest.raises(BlockContextBudgetExceeded):
        term.mirror_obstruction()

    scratch = cast(
        LedgerList[int] | None,
        object.__getattribute__(term, "_mirror_output_scratch"),
    )
    assert scratch is not None and not scratch
    scratch_account = next(
        item for item in ledger.inventory() if item.owner == scratch.owner
    )
    assert scratch_account.entries == scratch_account.nodes == 0
    assert (ledger.entries, ledger.nodes) == before
    assert ledger.counters["reverse_output_stream_requests"] == 0
    assert ledger.counters["reverse_output_stream_emitted_digits"] == 0
    assert collect_ledger_metrics(ledger).resource_audit_complete == 1


def test_plain_output_does_not_allocate_mirror_scratch() -> None:
    term = ReverseAddPoweredTerm(196, 0)
    assert object.__getattribute__(term, "_mirror_output_scratch") is None
    assert tuple(term.iter_digits()) == (6, 9, 1)
    assert object.__getattribute__(term, "_mirror_output_scratch") is None


def test_powered_mirror_validates_sheet_before_width_discovery(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = ReverseAddPoweredTerm(196, 3)

    def forbidden(_term: ReverseAddPoweredTerm) -> int:
        raise AssertionError("invalid mirror sheet requested output width")

    monkeypatch.setattr(ReverseAddPoweredTerm, "width", forbidden)
    with pytest.raises(ValueError, match="first sheet width"):
        term.mirror_obstruction(first_width=0)
    assert term.published_workspace is None


@pytest.mark.parametrize("width,sign", ((1, 1), (2, -1), (3, -1), (4, 1)))
def test_sheet_append_matches_independent_concatenation(width: int, sign: int) -> None:
    for left in ((), (3,), (2, 5, 1), (0, 1, 8, 9)):
        for right in ((), (7,), (4, 0, 6)):
            a = TwistedCylinderProjection.observe(left, width=width, sign=sign)
            b = TwistedCylinderProjection.observe(right, width=width, sign=sign)
            assert a.append(b, span=len(left)) == TwistedCylinderProjection.observe(
                left + right, width=width, sign=sign
            )


def test_tile_fold_shares_uniform_subtrees_and_clips_partial_prefix() -> None:
    ledger = ResourceLedger()
    tiles = TileArena(ledger)
    alphabet = tiles.intern_alphabet(
        TileAlphabet(
            11,
            10,
            10,
            4,
            "unsigned-radix-cell-with-explicit-blank",
            "canonical-tile-alphabet-v1",
        )
    )
    root = tiles.leaf(alphabet, 7)
    for _ in range(16):
        parent = tiles.join(root.tile, root.tile)
        root.close()
        root = parent
    try:
        assert not _sheet(tiles, root.tile, 65536, 3, -1).nonzero
        assert ledger.counters["tile_cylinder_node_evaluations"] == 17
        assert ledger.counters["tile_cylinder_leaf_reads"] == 1
        assert ledger.counters["tile_cylinder_cache_hits"] == 16
        assert not _sheet(tiles, root.tile, 12345, 5, -1).nonzero
    finally:
        root.close()


def test_tile_fold_preserves_nonpalindromic_clipped_boundary_and_budget_cleanup() -> (
    None
):
    ledger = ResourceLedger()
    tiles = TileArena(ledger)
    alphabet = tiles.intern_alphabet(
        TileAlphabet(
            11,
            10,
            10,
            4,
            "unsigned-radix-cell-with-explicit-blank",
            "canonical-tile-alphabet-v1",
        )
    )
    with (
        tiles.leaf(alphabet, 3) as a,
        tiles.leaf(alphabet, 8) as b,
        tiles.join(a.tile, b.tile) as pair,
        tiles.join(pair.tile, pair.tile) as root,
    ):
        result = _sheet(tiles, root.tile, 3, 2, -1)
        expected = first_mirror_obstruction(3, (3, 8, 3).__getitem__, first_width=2)
        assert not result.nonzero and expected is None
        result = _sheet(tiles, root.tile, 2, 2, -1)
        assert result.coefficients == (-5, 5)
        old = ledger.max_nodes
        ledger.max_nodes = ledger.nodes + 1
        try:
            with pytest.raises(BlockContextBudgetExceeded):
                _sheet(tiles, root.tile, 4, 2, -1)
        finally:
            ledger.max_nodes = old
        assert all(
            account.entries == account.nodes == 0
            for account in ledger.inventory()
            if account.name.startswith("tile-cylinder-")
        )
    with (
        tiles.leaf(alphabet, 10) as padding,
        pytest.raises(ValueError, match="interior padding"),
    ):
        _sheet(tiles, padding.tile, 1, 1, 1)
    assert all(
        account.entries == account.nodes == 0
        for account in ledger.inventory()
        if account.name.startswith("tile-cylinder-")
    )
