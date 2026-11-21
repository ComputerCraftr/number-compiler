"""Source-checked SLP execution of padded reflected multiplication."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp_walks import symbol_at
from number_compiler.arithmetic.automata.temporal_cone import (
    CarrySpacetimePower,
    TemporalSquareScratchReservation,
)
from number_compiler.arithmetic.carry.reflected_h_power import (
    normalize_reflected_cell_slp,
    padded_h_cell,
    padded_h_publish,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.owned_memo import LedgerReservation


@pytest.mark.parametrize("multiplier", [2, 5])
@pytest.mark.parametrize("span", [1, 2, 4, 8, 16])
@pytest.mark.parametrize("cells", [(50,), (0, 14, 20), (12, 90, 30, 45)])
def test_slp_cells_match_exact_tuple_action(
    multiplier: int, span: int, cells: tuple[int, ...]
) -> None:
    ledger = ResourceLedger()
    owner = ledger.register("reflected-test", "scratch")
    arena = LedgerSLPArena(ledger, "reflected-cells", "grammar")
    try:
        root = arena.word(cells)
        with TemporalSquareScratchReservation(
            LedgerReservation(ledger, owner)
        ) as scratch:
            bank = CarrySpacetimePower(
                scratch,
                None,
                None,
                cell_action=lambda a, b: padded_h_cell(a, b, multiplier),
            )
            try:
                actual = bank.advance_blocks_slp(arena, root, span)
                assert arena.materialize(actual) == bank.advance_blocks(cells, span)
            finally:
                bank.release_temporary_storage()
        assert ledger.account_usage(owner) == (0, 0)
    finally:
        arena.dispose()
        ledger.mark_disposed(owner)


def test_slp_tile_reuse_checks_arena_and_generation() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("reflected-test", "scratch")
    first = LedgerSLPArena(ledger, "reflected-first", "grammar")
    second = LedgerSLPArena(ledger, "reflected-second", "grammar")
    try:
        with TemporalSquareScratchReservation(
            LedgerReservation(ledger, owner)
        ) as scratch:
            bank = CarrySpacetimePower(
                scratch, None, None, cell_action=lambda a, b: padded_h_cell(a, b, 2)
            )
            try:
                checkpoint = len(first.nodes)
                a = first.word((12, 34))
                b = second.word((56, 78))
                assert a == b
                assert first.materialize(
                    bank.advance_blocks_slp(first, a, 1)
                ) == bank.advance_blocks((12, 34), 1)
                assert second.materialize(
                    bank.advance_blocks_slp(second, b, 1)
                ) == bank.advance_blocks((56, 78), 1)
                first.rollback_unpublished_suffix(checkpoint)
                c = first.word((90, 21))
                assert c == a
                assert first.materialize(
                    bank.advance_blocks_slp(first, c, 1)
                ) == bank.advance_blocks((90, 21), 1)
            finally:
                bank.release_temporary_storage()
        assert ledger.account_usage(owner) == (0, 0)
    finally:
        first.dispose()
        second.dispose()
        ledger.mark_disposed(owner)


def test_normalization_skips_zero_repetitions(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.carry import reflected_h_power

    ledger = ResourceLedger()
    owner = ledger.register("reflected-test", "scratch")
    arena = LedgerSLPArena(ledger, "reflected-zeros", "grammar")
    visits = 0

    def counted(cells: LedgerSLPArena, root: int, position: int) -> int:
        nonlocal visits
        visits += 1
        return symbol_at(cells, root, position)

    try:
        zeros = arena.repeat(arena.terminal(0), 1_000_000)
        root = arena.concat_many((zeros, arena.terminal(13), zeros))
        monkeypatch.setattr(reflected_h_power, "symbol_at", counted)
        result = normalize_reflected_cell_slp(arena, root, ledger, owner)
        assert arena.materialize(result) == (13,)
        assert visits <= 1
        assert ledger.account_usage(owner) == (0, 0)
    finally:
        arena.dispose()
        ledger.mark_disposed(owner)


def test_zero_edge_search_skips_nonzero_interior(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.carry import reflected_h_power

    ledger = ResourceLedger()
    owner = ledger.register("reflected-edge-test", "scratch")
    arena = LedgerSLPArena(ledger, "reflected-edge-test", "grammar")
    try:
        zeros = arena.repeat(arena.terminal(0), 1_000_000)
        interior = arena.repeat(arena.word((4, 0, 8, 0)), 100_000)
        root = arena.concat_many((zeros, interior, zeros))

        def forbidden(*args: object, **kwargs: object) -> object:
            raise AssertionError("edge search must not fold the entire DAG")

        monkeypatch.setattr(reflected_h_power, "fold_slp_dag", forbidden)
        result = normalize_reflected_cell_slp(arena, root, ledger, owner)
        assert arena.nodes[result].length == 399_999
        assert symbol_at(arena, result, 0) == 4
        assert symbol_at(arena, result, 399_998) == 8
        assert ledger.account_usage(owner) == (0, 0)
    finally:
        arena.dispose()
        ledger.mark_disposed(owner)


def test_normalization_reuses_shared_zero_dag(monkeypatch: pytest.MonkeyPatch) -> None:
    ledger = ResourceLedger()
    owner = ledger.register("reflected-zero-dag", "scratch")
    arena = LedgerSLPArena(ledger, "reflected-zero-dag", "grammar")
    try:
        left = arena.terminal(0)
        right = arena.concat(left, left)
        for _ in range(28):
            left, right = right, arena.concat(left, right)
        reserve = LedgerReservation.reserve
        visits = 0

        def counted(
            scope: LedgerReservation, *, entries: int = 0, nodes: int = 0
        ) -> None:
            nonlocal visits
            visits += 1
            reserve(scope, entries=entries, nodes=nodes)

        monkeypatch.setattr(LedgerReservation, "reserve", counted)
        result = normalize_reflected_cell_slp(arena, right, ledger, owner)
        assert symbol_at(arena, result, 0) == 0
        assert arena.nodes[result].length == 1
        assert visits < 2_000
        assert ledger.account_usage(owner) == (0, 0)
    finally:
        arena.dispose()
        ledger.mark_disposed(owner)


def test_repeated_cell_slab_reuses_semantic_tiles() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("reflected-test", "scratch")
    arena = LedgerSLPArena(ledger, "reflected-slab", "grammar")
    try:
        root = arena.repeat(arena.word((13, 47)), 256)
        with TemporalSquareScratchReservation(
            LedgerReservation(ledger, owner)
        ) as scratch:
            bank = CarrySpacetimePower(
                scratch, None, None, cell_action=lambda a, b: padded_h_cell(a, b, 5)
            )
            try:
                result = bank.advance_blocks_slp(arena, root, 64)
                assert arena.materialize(result) == bank.advance_blocks(
                    (13, 47) * 256, 64
                )
                assert bank.stats.source_traversal_tasks < 64
            finally:
                bank.release_temporary_storage()
        assert ledger.account_usage(owner) == (0, 0)
    finally:
        arena.dispose()
        ledger.mark_disposed(owner)


def test_slp_publisher_rolls_back_after_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.carry import reflected_h_power

    ledger = ResourceLedger()
    owner = ledger.register("reflected-test", "scratch")
    arena = LedgerSLPArena(ledger, "reflected-output", "grammar")
    checkpoint = len(arena.nodes)

    def fail(*_args: object, **_kwargs: object) -> int:
        raise RuntimeError("injected output failure")

    try:
        monkeypatch.setattr(reflected_h_power, "_decimal_slp_from_cells", fail)
        with pytest.raises(RuntimeError, match="injected output failure"):
            padded_h_publish(
                73,
                128,
                5,
                arena=arena,
                scratch_owner=owner,
                max_state_bits=4096,
                use_slp_power=True,
            )
        assert len(arena.nodes) == checkpoint
        assert ledger.account_usage(owner) == (0, 0)
    finally:
        arena.dispose()
        ledger.mark_disposed(owner)


@pytest.mark.parametrize("multiplier", [2, 5])
@pytest.mark.parametrize("seed", [0, 50, 73, 196])
@pytest.mark.parametrize("steps", [128, 129])
def test_slp_publisher_matches_literal(seed: int, steps: int, multiplier: int) -> None:
    ledger = ResourceLedger()
    owner = ledger.register("reflected-test", "scratch")
    arena = LedgerSLPArena(ledger, "reflected-output", "grammar")
    try:
        expected = seed
        for _ in range(steps):
            expected = multiplier * int(str(expected)[::-1])
        root = padded_h_publish(
            seed,
            steps,
            multiplier,
            arena=arena,
            scratch_owner=owner,
            max_state_bits=4096,
            use_slp_power=True,
        )
        assert "".join(map(str, arena.materialize(root))) == str(expected)
        assert ledger.account_usage(owner) == (0, 0)
    finally:
        arena.dispose()
        ledger.mark_disposed(owner)


def test_even_slp_publisher_uses_single_edge_cut(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.carry import reflected_h_power

    ledger = ResourceLedger()
    owner = ledger.register("reflected-even-cut", "scratch")
    arena = LedgerSLPArena(ledger, "reflected-even-cut", "grammar")
    original = symbol_at

    def reject_output_probe(source: LedgerSLPArena, root: int, position: int) -> int:
        if source is arena:
            raise AssertionError("even publication should use one edge cut")
        return original(source, root, position)

    try:
        expected = 50
        for _ in range(128):
            expected = 2 * int(str(expected)[::-1])
        monkeypatch.setattr(reflected_h_power, "symbol_at", reject_output_probe)
        root = padded_h_publish(
            50,
            128,
            2,
            arena=arena,
            scratch_owner=owner,
            max_state_bits=4096,
            use_slp_power=True,
        )
        assert "".join(map(str, arena.materialize(root))) == str(expected)
        assert ledger.account_usage(owner) == (0, 0)
    finally:
        arena.dispose()
        ledger.mark_disposed(owner)
