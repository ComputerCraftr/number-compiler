from __future__ import annotations

from collections.abc import Generator
from contextlib import AbstractContextManager, contextmanager
from functools import partial

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.ordered_output import OrderedSourceCoverage
from number_compiler.arithmetic.fields.ordered_band import (
    OrderedDigitBandFrame,
    ordered_digit_band_frame,
    ordered_digit_band_output,
)
from number_compiler.arithmetic.fields.ordered_matrix import (
    Matrix2,
    compile_dyadic_ordered_band,
    ordered_decimal_continuant,
)


def _record_reservation(
    calls: list[tuple[int, int, int]], q: int, count: int, retained: int
) -> None:
    calls.append((q, count, retained))


@pytest.mark.parametrize("modulus", [None, 2, 97, 1000])
def test_ordered_continuant_matches_independent_matrix_products(
    modulus: int | None,
) -> None:
    for digits in ((), (0,), (1, 4, 2, 9), (8, 3, 8, 3, 8)):
        expected = Matrix2.identity(modulus)
        for digit in digits:
            expected = expected.multiply(Matrix2.digit(digit + 1, modulus))
        assert ordered_decimal_continuant(digits, modulus) == expected


@pytest.mark.parametrize("shared", [False, True])
def test_dyadic_band_matches_direct_shifted_rows(shared: bool) -> None:
    for width in (1, 2, 5):
        base = 10**width
        for source in (0, 9, 76123, 10**16 + 1285):
            for rows in (1, 2, 3, 7, 16):
                calls: list[tuple[int, int, int]] = []

                observed = compile_dyadic_ordered_band(
                    source,
                    rows,
                    width,
                    partial(_record_reservation, calls),
                    use_memo=shared,
                )
                expected = Matrix2.identity()
                for row in range(rows):
                    digits = f"{(source >> row) % base:0{width}d}"
                    for digit in digits:
                        expected = expected.multiply(Matrix2.digit(int(digit) + 1))
                assert observed == expected
                assert calls


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


def test_rotated_dyadic_repeat_reserves_and_folds_only_primitive_rows(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.fields import ordered_matrix as owner

    count = 512
    original = owner.fold_dyadic_leaf
    leaves: list[tuple[int, int]] = []

    def checked(q: int, rows: int, width: int, base: int) -> Matrix2:
        assert rows <= 2, "repeated row occurrences were opened"
        leaves.append((q, rows))
        return original(q, rows, width, base)

    monkeypatch.setattr(owner, "fold_dyadic_leaf", checked)
    primitive_ids: set[tuple[int, int]] = set()
    for phase in (0, 1):
        digits = (6, 3) if phase == 0 else (3, 6)
        q = (digits[1] << (count - 1)) + sum(
            (digits[t % 2] & 1) << t for t in range(count - 1)
        )
        calls: list[tuple[int, int, int]] = []
        leaves.clear()
        observed = compile_dyadic_ordered_band(
            q, count, 1, partial(_record_reservation, calls), use_memo=True
        )
        expected = ordered_decimal_continuant(digits).power(count // 2)
        assert observed == expected
        assert len(calls) == 1
        assert len(leaves) <= 2
        primitive_ids.add(leaves[0])
    assert len(primitive_ids) == 1


def test_completed_leaf_is_probed_before_period_rediscovery(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.fields import ordered_matrix as owner

    leaf = 5 * 12345678901234567
    source = leaf * (1 + 2**64)
    period = owner.dyadic_band_period
    calls: list[tuple[int, int]] = []

    def observe(q: int, rows: int, width: int, odd_base: int) -> int:
        calls.append((q, rows))
        return period(q, rows, width, odd_base)

    monkeypatch.setattr(owner, "dyadic_band_period", observe)
    reservations: list[tuple[int, int, int]] = []
    actual = owner.compile_dyadic_ordered_band(
        source, 128, 1, partial(_record_reservation, reservations), use_memo=True
    )
    rows = ((source >> i) % 10 for i in range(128))
    expected = owner.ordered_decimal_continuant(rows)
    assert actual == expected
    assert calls.count((leaf, 64)) == 1


def test_long_physical_return_compiles_one_body(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.fields import ordered_matrix as owner

    exponent = 9364999200344104145518958726158206032905098070
    rows, cut = 148, 8
    q = 10 * pow(5, exponent - cut, 1 << (cut + rows - 1)) >> cut
    literal = [(q >> index) % 10 for index in range(rows)]
    assert owner.dyadic_band_period(q, rows, 1, 5) == 37
    # The binary overlap survives this change to the high odd coordinate.
    assert owner.dyadic_band_period(q ^ (1 << rows), rows, 1, 5) != 37
    worked = 0
    leaf = owner.fold_dyadic_leaf

    def count_leaf(source: int, size: int, width: int, base: int) -> Matrix2:
        nonlocal worked
        worked += size
        return leaf(source, size, width, base)

    monkeypatch.setattr(owner, "fold_dyadic_leaf", count_leaf)
    for clipped in (rows, rows - 1):
        worked = 0
        reservations: list[tuple[int, int, int]] = []
        action = owner.compile_dyadic_ordered_band(
            q, clipped, 1, partial(_record_reservation, reservations), use_memo=False
        )
        assert action == owner.ordered_decimal_continuant(literal[:clipped])
        assert worked <= 37 + clipped % 37
        assert len(reservations) == 1


def test_long_probe_scratch_refusal_preserves_exact_band(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.fields import ordered_matrix as owner

    def refuse_optional(_q: int, _rows: int, extra_bits: int) -> None:
        if extra_bits:
            raise BlockContextBudgetExceeded("optional source probe exceeds capacity")

    def forbid(*_args: int) -> int:
        pytest.fail("unreserved long-overlap probe was opened")

    monkeypatch.setattr(owner, "_long_dyadic_band_period", forbid)
    count, q = 256, 123456789
    assert owner.compile_dyadic_ordered_band(
        q, count, 1, refuse_optional, use_memo=False
    ) == owner.ordered_decimal_continuant((q >> i) % 10 for i in range(count))
