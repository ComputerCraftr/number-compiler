"""Shared finite digit-band matrix publication without source authority.

Family adapters authenticate a source and lazily provide one exact band frame
per physical tick. This module owns the repeated digit-to-matrix fold only.
"""

from __future__ import annotations

from collections.abc import Callable, Generator
from contextlib import AbstractContextManager
from dataclasses import dataclass

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.contracts.ordered_output import (
    OrderedBandChannel,
    OrderedBandOutput,
    OrderedSourceCoverage,
)
from number_compiler.arithmetic.fields.ordered_matrix import Matrix2, OrderedCovector


@dataclass(frozen=True, slots=True)
class OrderedDigitBandFrame:
    """One exact pair of fixed-width digit words at a physical offset."""

    tick_offset: int
    lower_digits: tuple[int, ...]
    upper_digits: tuple[int, ...]
    lower_source_letters: int
    upper_source_letters: int


def ordered_digit_band_output(
    source_index: int,
    steps: int,
    width: int,
    modulus: int,
    frame_factory: Callable[[], Generator[OrderedDigitBandFrame, None, None]],
    reserve: Callable[[int, int], AbstractContextManager[object]],
    *,
    source_coverage: OrderedSourceCoverage,
    coefficients: tuple[int, ...] | None = None,
    trace: bool = False,
) -> OrderedBandOutput:
    """Fold a checked finite source window into two chronological matrices.

    The reservation is entered before the frame iterator is advanced and
    before any matrix, covector, or trace output is allocated.
    """

    source_index = require_integer(source_index, "ordered band source index", 0)
    steps = require_integer(steps, "ordered band physical ticks", 1, 4096)
    width = require_integer(width, "ordered band digit width", 1, 90)
    modulus = require_integer(modulus, "ordered band modulus", 2)
    if not callable(frame_factory) or not callable(reserve):
        raise TypeError("ordered band needs frame and reservation providers")
    if type(source_coverage) is not OrderedSourceCoverage:
        raise TypeError("ordered band needs a declared finite source coverage")
    entries, node_reservation = ordered_band_scratch_cost(
        steps,
        width,
        modulus,
        coefficients,
        trace=trace,
        matrix_channels=2,
    )
    with reserve(entries, node_reservation):
        covector = (
            None if coefficients is None else OrderedCovector(coefficients, modulus)
        )
        lower_total = Matrix2.identity(modulus)
        upper_total = Matrix2.identity(modulus)
        trace_rows: list[tuple[Matrix2, ...]] = []
        matrix_multiplications = 0
        source_letters_read = 0
        frames = frame_factory()
        try:
            for expected_offset in range(steps):
                try:
                    frame = next(frames)
                except StopIteration as exc:
                    raise ValueError(
                        "ordered band window ended before its declared horizon"
                    ) from exc
                if type(frame) is not OrderedDigitBandFrame:
                    raise TypeError("ordered band provider returned an invalid frame")
                tick_offset = require_integer(
                    frame.tick_offset, "ordered band tick offset", 0, steps - 1
                )
                if tick_offset != expected_offset:
                    raise ValueError(
                        "ordered band frames are not chronologically adjacent"
                    )
                for digits in (frame.lower_digits, frame.upper_digits):
                    if type(digits) is not tuple or len(digits) != width:
                        raise ValueError("ordered band frame has the wrong digit width")
                    if any(
                        type(digit) is not int or not 0 <= digit <= 9
                        for digit in digits
                    ):
                        raise ValueError(
                            "ordered band frame contains a nondecimal digit"
                        )
                lower_count = require_integer(
                    frame.lower_source_letters, "lower source letters", 0, width
                )
                upper_count = require_integer(
                    frame.upper_source_letters, "upper source letters", 0, width
                )

                lower_action = _digit_word_matrix(frame.lower_digits, modulus)
                upper_action = _digit_word_matrix(frame.upper_digits, modulus)
                lower_total = lower_total.then(lower_action)
                upper_total = upper_total.then(upper_action)
                matrix_multiplications += 2 * (width + 1)
                source_letters_read += lower_count + upper_count
                if trace:
                    trace_rows.append((lower_action, upper_action))

            try:
                next(frames)
            except StopIteration:
                pass
            else:
                raise ValueError("ordered band window exceeded its declared horizon")

            matrices = (lower_total, upper_total)
            covectors = (
                ()
                if covector is None
                else tuple(covector.pullback(matrix) for matrix in matrices)
            )
            return OrderedBandOutput(
                source_index=source_index,
                physical_ticks=steps,
                start_phase=None,
                terminal_phase=None,
                channels=(
                    OrderedBandChannel.LOWER_DIGITS,
                    OrderedBandChannel.UPPER_DIGITS,
                ),
                matrices=matrices,
                covectors=covectors,
                source_coverage=source_coverage,
                matrix_multiplications=matrix_multiplications,
                source_letters_read=source_letters_read,
                trace=tuple(trace_rows),
            )
        finally:
            frames.close()


def _digit_word_matrix(digits: tuple[int, ...], modulus: int) -> Matrix2:
    """Build an MSD-first fixed-width decimal continuant."""

    result = Matrix2.identity(modulus)
    for digit in digits:
        result = result.multiply(Matrix2.digit(digit + 1, modulus))
    return result


def _limbs(bits: int) -> int:
    return max(1, (bits + 63) // 64)


def ordered_band_scratch_cost(
    steps: int,
    width: int,
    modulus: int,
    coefficients: tuple[int, ...] | None,
    *,
    trace: bool,
    matrix_channels: int,
) -> tuple[int, int]:
    """Preflight a digit-band allocation envelope in entries and 64-bit limbs."""

    steps = require_integer(steps, "ordered band physical ticks", 1, 4096)
    width = require_integer(width, "ordered band digit width", 1, 90)
    modulus = require_integer(modulus, "ordered band modulus", 2)
    if modulus.bit_length() > 4096:
        raise ValueError("ordered band modulus exceeds 4096 bits")
    if type(trace) is not bool:
        raise TypeError("ordered band trace demand must be Boolean")
    if trace and steps > 128:
        raise ValueError("ordered matrix trace exceeds 128 physical ticks")
    matrix_channels = require_integer(matrix_channels, "matrix channels", 1, 2)

    coefficient_count = 0
    coefficient_limb_scratch = 0
    if coefficients is not None:
        if type(coefficients) is not tuple or not 1 <= len(coefficients) <= 9:
            raise ValueError("matrix coefficients require degree 0..8")
        if any(
            type(coefficient) is not int or coefficient.bit_length() > 128
            for coefficient in coefficients
        ):
            raise ValueError("matrix coefficients must be exact 128-bit integers")
        coefficient_count = len(coefficients)
        coefficient_bits = max(value.bit_length() for value in coefficients)
        degree = coefficient_count - 1
        # A degree-d pullback can transiently multiply d modulus-sized powers
        # by one admitted coefficient before reducing the accumulated row.
        largest_polynomial_temporary = (
            degree * modulus.bit_length() + coefficient_bits + 16
        )
        coefficient_limb_scratch = 12 * _limbs(
            largest_polynomial_temporary
        ) + 32 * _limbs(modulus.bit_length())

    entries = (
        matrix_channels * width
        + 2 * matrix_channels
        + 2
        + (matrix_channels + 1) * steps * int(trace)
        + matrix_channels * coefficient_count
    )
    modulus_bits = modulus.bit_length()
    # Matrix multiplication can hold two full-width products and their sum
    # per output cell. Trace rows retain four entries per matrix and tick.
    trace_limb_scratch = (
        4 * matrix_channels * steps * _limbs(modulus_bits) if trace else 0
    )
    working_limb_scratch = 16 * _limbs(2 * modulus_bits + 2)
    retained_matrix_limb_scratch = 8 * matrix_channels * _limbs(modulus_bits)
    node_reservation = (
        entries
        + working_limb_scratch
        + retained_matrix_limb_scratch
        + coefficient_limb_scratch
        + trace_limb_scratch
    )
    return entries, node_reservation
