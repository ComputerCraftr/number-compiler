from __future__ import annotations

from collections.abc import Generator
from contextlib import AbstractContextManager, contextmanager

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.ordered_output import OrderedSourceCoverage
from number_compiler.arithmetic.fields.ordered_band import (
    OrderedDigitBandFrame,
    ordered_digit_band_frame,
    ordered_digit_band_output,
)


def test_frame_generator_is_closed_before_reservation_release_on_failure() -> None:
    reserved = False
    closed = False

    @contextmanager
    def reserve(entries: int, nodes: int) -> Generator[None, None, None]:
        nonlocal reserved
        assert entries > 0 and nodes >= entries
        reserved = True
        try:
            yield
        finally:
            reserved = False

    def frames() -> Generator[OrderedDigitBandFrame, None, None]:
        nonlocal closed
        assert reserved
        try:
            yield OrderedDigitBandFrame(1, (2,), (3,), 1, 1)
        finally:
            closed = True

    with pytest.raises(ValueError, match="chronologically adjacent"):
        ordered_digit_band_output(
            12,
            2,
            1,
            97,
            frames,
            reserve,
            source_coverage=OrderedSourceCoverage.SCHEDULER_WINDOW,
        )
    assert closed
    assert not reserved


def test_reservation_refusal_happens_before_frame_generation() -> None:
    started = False

    def refuse(_entries: int, _nodes: int) -> AbstractContextManager[object]:
        raise BlockContextBudgetExceeded("injected reservation refusal")

    def frames() -> Generator[OrderedDigitBandFrame, None, None]:
        nonlocal started
        started = True
        yield OrderedDigitBandFrame(0, (1,), (1,), 1, 1)

    with pytest.raises(BlockContextBudgetExceeded, match="injected"):
        ordered_digit_band_output(
            12,
            1,
            1,
            97,
            frames,
            refuse,
            source_coverage=OrderedSourceCoverage.SCHEDULER_WINDOW,
        )
    assert not started


def test_ordered_band_preflights_modulus_before_reserving() -> None:
    reserved = False

    @contextmanager
    def reserve(_entries: int, _nodes: int) -> Generator[None, None, None]:
        nonlocal reserved
        reserved = True
        yield

    def frames() -> Generator[OrderedDigitBandFrame, None, None]:
        yield OrderedDigitBandFrame(0, (1,), (1,), 1, 1)

    with pytest.raises(ValueError, match="4096 bits"):
        ordered_digit_band_output(
            12,
            1,
            1,
            1 << 4096,
            frames,
            reserve,
            source_coverage=OrderedSourceCoverage.SCHEDULER_WINDOW,
        )
    assert not reserved


@pytest.mark.parametrize("width", [1, 3, 6])
def test_source_frames_read_little_endian_positions_with_exact_padding(
    width: int,
) -> None:
    digits = (3, 2, 1, 0)
    visited: list[int] = []

    def read(position: int) -> int:
        visited.append(position)
        return digits[position]

    frame = ordered_digit_band_frame(7, len(digits), width, read)
    assert frame.tick_offset == 7
    assert frame.lower_digits == tuple(
        digits[i] if i < len(digits) else 0 for i in range(width - 1, -1, -1)
    )
    assert frame.upper_digits == tuple(
        digits[len(digits) - 1 - i] if i < len(digits) else 0 for i in range(width)
    )
    assert frame.lower_source_letters == frame.upper_source_letters == min(width, 4)
    assert len(visited) == 2 * min(width, 4)
