"""Exact packed-diagonal fastpath: no moving-front period assumption.

A moving-band agreement is a finite pair-of-sources certificate; it cannot
license dropping unknown future carry masks from a cold full-word nth query.
These tests instead verify the native exact cone computations accelerated on
that path, with the existing stencil as the independent arithmetic oracle.
"""

from __future__ import annotations

import random
from collections.abc import Iterator, Sized

import pytest

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.owned_memo import LedgerReservation
from number_compiler.sequences.double_reverse import temporal_packed_diagonal
from number_compiler.sequences.double_reverse.stencil_moore import stencil_cell
from number_compiler.sequences.double_reverse.temporal_packed_diagonal import (
    TemporalSquareScratchCapacityRefused,
    TemporalSquareScratchReservation,
    TemporalSquareStats,
    pack_source_window,
    packed_diagonal_middle,
    packed_digit_predicates,
)


@pytest.fixture
def packed_source_workspace() -> Iterator[tuple[ResourceLedger, LedgerSLPArena, int]]:
    ledger = ResourceLedger()
    arena = LedgerSLPArena(ledger, "packed-source-test", "double_reverse_test")
    owner = ledger.register("packed-source-scratch", "workspace")
    try:
        yield ledger, arena, owner
    finally:
        arena.dispose()
        ledger.retire_unpublished_owner(owner)


def test_predicate_planes_are_exact_on_the_admitted_decimal_alphabet() -> None:
    for digit in range(10):
        assert packed_digit_predicates(digit, 1) == (
            int(digit in (3, 4, 8, 9)),
            int(digit in (1, 4, 6, 9)),
            int(digit in (2, 7)),
            int(digit >= 5),
        )
    rng = random.Random(196)
    for width in (4, 32, 512, 4096):
        word = 0
        digits = [rng.randrange(10) for _ in range(width)]
        for digit in digits:
            word = (word << 4) | digit
        mask = ((1 << (4 * width)) - 1) // 15
        planes = packed_digit_predicates(word, mask)
        for position, digit in enumerate(reversed(digits)):
            bit = 1 << (4 * position)
            assert tuple(int(bool(row & bit)) for row in planes) == (
                int(digit in (3, 4, 8, 9)),
                int(digit in (1, 4, 6, 9)),
                int(digit in (2, 7)),
                int(digit >= 5),
            )


@pytest.mark.parametrize("steps", (1, 2, 3, 4, 8, 16, 32, 64))
def test_packed_diagonal_agrees_with_exact_cell_recurrence(steps: int) -> None:
    rng = random.Random(1000 + steps)
    digits = [rng.randrange(10) for _ in range(4 * steps)]
    packed = 0
    for digit in digits:
        packed = (packed << 4) | digit
    found = packed_diagonal_middle(packed, steps)
    for _ in range(steps):
        digits = [
            stencil_cell(digits[i], digits[i + 1], digits[i + 2])
            for i in range(len(digits) - 2)
        ]
    expected = 0
    for digit in digits:
        expected = (expected << 4) | digit
    assert found == expected


def test_bulk_source_window_packing_works_for_repeated_spatial_macros(
    packed_source_workspace: tuple[ResourceLedger, LedgerSLPArena, int],
) -> None:
    ledger, arena, owner = packed_source_workspace
    motif = (1, 2, 3, 4, 9, 0, 8, 5)
    source = arena.repeat(arena.word(motif), 1024)
    width = arena.nodes[source].length
    expected = int("".join(format(d, "x") for d in motif) * 1024, 16)
    odd_width_source = arena.word((1, 2, 3, 4, 5))
    stats = TemporalSquareStats(0, 0, 0, 0, 0)
    with TemporalSquareScratchReservation(LedgerReservation(ledger, owner)) as scratch:
        assert (
            pack_source_window(arena, source, width, scratch, None, stats) == expected
        )
        assert (
            pack_source_window(arena, odd_width_source, 5, scratch, None, stats)
            == 0x12345
        )
    charge = next(item for item in ledger.inventory() if item.owner == owner)
    assert charge.nodes == charge.entries == 0


def test_bulk_source_pack_cleans_up_after_visitor_error(
    packed_source_workspace: tuple[ResourceLedger, LedgerSLPArena, int],
) -> None:
    ledger, arena, owner = packed_source_workspace
    source = arena.repeat(arena.word((1, 9, 6, 8)), 200)
    stats = TemporalSquareStats(0, 0, 0, 0, 0)

    def reject(_node: bool) -> None:
        raise RuntimeError("injected source visitor failure")

    with pytest.raises(RuntimeError, match="visitor failure") as raised:
        with TemporalSquareScratchReservation(
            LedgerReservation(ledger, owner)
        ) as scratch:
            pack_source_window(arena, source, 800, scratch, reject, stats)
    frame = _pack_source_window_frame(raised.value)
    assert isinstance(frame["packed_bytes"], bytearray)
    assert len(frame["packed_bytes"]) == 0
    charge = next(item for item in ledger.inventory() if item.owner == owner)
    assert charge.nodes == charge.entries == 0


def test_packed_publication_clears_traceback_retained_buffers(
    monkeypatch: pytest.MonkeyPatch,
    packed_source_workspace: tuple[ResourceLedger, LedgerSLPArena, int],
) -> None:
    ledger, arena, owner = packed_source_workspace
    source = arena.word((1, 2, 3, 4))
    checkpoint = len(arena.nodes)

    def fail_concat(_arena: LedgerSLPArena, _left: int, _right: int) -> int:
        raise RuntimeError("injected packed publication failure")

    monkeypatch.setattr(LedgerSLPArena, "concat", fail_concat)
    stats = TemporalSquareStats(0, 0, 0, 0, 0)
    with TemporalSquareScratchReservation(LedgerReservation(ledger, owner)) as scratch:
        with pytest.raises(RuntimeError, match="packed publication failure") as raised:
            temporal_packed_diagonal.publish_packed_diagonal(
                arena, source, 1, scratch, None, stats
            )

    frame = _publish_packed_diagonal_frame(raised.value)
    digits = frame["digits"]
    assert isinstance(digits, Sized)
    assert len(digits) == 0
    concat_frame = _concat_many_frame(raised.value)
    assert concat_frame["row"] == []
    assert concat_frame["nxt"] == []
    assert len(arena.nodes) == checkpoint
    charge = next(item for item in ledger.inventory() if item.owner == owner)
    assert charge.nodes == charge.entries == 0


def _pack_source_window_frame(error: BaseException) -> dict[str, object]:
    traceback = error.__traceback__
    while traceback is not None:
        frame = traceback.tb_frame
        if frame.f_code.co_name == "pack_source_window":
            return frame.f_locals
        traceback = traceback.tb_next
    raise AssertionError("exception did not retain the source-window frame")


def _publish_packed_diagonal_frame(error: BaseException) -> dict[str, object]:
    traceback = error.__traceback__
    while traceback is not None:
        frame = traceback.tb_frame
        if frame.f_code.co_name == "publish_packed_diagonal":
            return frame.f_locals
        traceback = traceback.tb_next
    raise AssertionError("exception did not retain the packed-publication frame")


def _concat_many_frame(error: BaseException) -> dict[str, object]:
    traceback = error.__traceback__
    while traceback is not None:
        frame = traceback.tb_frame
        if frame.f_code.co_name == "concat_many" and {
            "row",
            "nxt",
        }.issubset(frame.f_locals):
            return frame.f_locals
        traceback = traceback.tb_next
    raise AssertionError("exception did not retain the SLP concatenation frame")


@pytest.mark.parametrize(
    ("buffer_credit", "expect_buffer"),
    ((-1, False), (0, True)),
    ids=("before-allocation", "after-allocation"),
)
def test_pack_scratch_refusal_clears_buffer_and_traceback(
    monkeypatch: pytest.MonkeyPatch,
    packed_source_workspace: tuple[ResourceLedger, LedgerSLPArena, int],
    buffer_credit: int,
    expect_buffer: bool,
) -> None:
    ledger, arena, owner = packed_source_workspace
    source = arena.repeat(arena.word((1, 9, 6, 8)), 200)
    width = arena.nodes[source].length
    buffer_bytes = (width + 1) // 2
    ledger.tighten_limits(
        max_nodes=ledger.nodes + buffer_bytes + buffer_credit,
        max_cache_entries=ledger.entries + buffer_bytes + buffer_credit,
    )
    real_bytearray = bytearray
    allocated: list[bytearray] = []

    def record_allocation(size: int) -> bytearray:
        result = real_bytearray(size)
        allocated.append(result)
        return result

    monkeypatch.setattr(
        temporal_packed_diagonal, "bytearray", record_allocation, raising=False
    )
    stats = TemporalSquareStats(0, 0, 0, 0, 0)
    with TemporalSquareScratchReservation(LedgerReservation(ledger, owner)) as scratch:
        with pytest.raises(TemporalSquareScratchCapacityRefused) as raised:
            pack_source_window(arena, source, width, scratch, None, stats)
    assert len(allocated) == int(expect_buffer)
    if expect_buffer:
        assert len(allocated[0]) == 0
    frame = _pack_source_window_frame(raised.value)
    if expect_buffer:
        assert isinstance(frame["packed_bytes"], bytearray)
        assert len(frame["packed_bytes"]) == 0
    else:
        assert "packed_bytes" not in frame
    charge = next(item for item in ledger.inventory() if item.owner == owner)
    assert charge.nodes == charge.entries == 0
