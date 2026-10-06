"""Output stream counters follow values delivered to their consumers."""

from __future__ import annotations

from collections.abc import Generator, Iterator

import pytest

from number_compiler.api.number_api import (
    AntihydraTermPayload,
    PoweredCollatzTermPayload,
)
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.output_stream_metrics import (
    initialize_output_stream_metrics,
    measured_output_stream,
)
from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def test_collatz_partial_binary_stream_counts_only_pulled_digits() -> None:
    term = PoweredCollatzTerm(27, 1)
    counters = term._ledger.counters
    assert counters["collatz_output_stream_requests"] == 0
    stream = term.iter_digits()
    assert counters["collatz_output_stream_requests"] == 0

    assert next(stream) == 0
    assert counters["collatz_output_stream_requests"] == 1
    assert counters["collatz_output_stream_emitted_digits"] == 1
    assert isinstance(stream, Generator)
    stream.close()

    assert counters["collatz_output_stream_cancellations"] == 1
    assert counters["collatz_output_stream_failures"] == 0


def test_collatz_radix_conversion_has_separate_operand_and_output_counts() -> None:
    term = PoweredCollatzTerm(27, 1)
    payload = PoweredCollatzTermPayload(term, radix=10)

    assert tuple(payload.iter_digits()) == tuple(digits_lsd(82, 10))
    counters = term._ledger.counters
    assert counters["collatz_output_stream_requests"] == 1
    assert counters["collatz_output_stream_emitted_digits"] == 2
    assert counters["collatz_radix_conversion_requests"] == 1
    assert counters["collatz_radix_conversion_emitted_digits"] == 2
    assert counters["collatz_radix_conversion_operand_bits"] == (82).bit_length()


def test_reverse_output_stream_counts_terminal_output_and_partial_close() -> None:
    term = ReverseAddPoweredTerm(196, 1)
    stream = term.iter_digits()
    assert next(stream) == 7
    assert isinstance(stream, Generator)
    stream.close()

    counters = term._ledger.counters
    assert counters["reverse_output_stream_requests"] == 1
    assert counters["reverse_output_stream_emitted_digits"] == 1
    assert counters["reverse_output_stream_cancellations"] == 1
    assert counters["reverse_output_stream_failures"] == 0


def test_antihydra_eager_digits_count_actual_conversion_output() -> None:
    term = AntihydraArithmeticTerm(0)
    payload = AntihydraTermPayload(term)
    digits = payload.digits()

    counters = term.ledger.counters
    assert digits == tuple(digits_lsd(term.value(), 2))
    assert counters["antihydra_output_stream_requests"] == 1
    assert counters["antihydra_output_stream_emitted_digits"] == len(digits)
    assert counters["antihydra_output_stream_cancellations"] == 0
    assert counters["antihydra_digit_conversion_requests"] == 1
    assert counters["antihydra_digit_conversion_emitted_digits"] == len(digits)
    assert (
        counters["antihydra_digit_conversion_operand_bits"] == term.value().bit_length()
    )


def test_failed_output_source_records_failure_without_cancellation() -> None:
    ledger = ResourceLedger()
    initialize_output_stream_metrics(ledger, "test_output_stream")

    def source() -> Iterator[int]:
        yield 3
        raise RuntimeError("source failed")

    stream = measured_output_stream(ledger, "test_output_stream", source)
    assert next(stream) == 3
    with pytest.raises(RuntimeError, match="source failed"):
        next(stream)

    assert ledger.counters["test_output_stream_emitted_digits"] == 1
    assert ledger.counters["test_output_stream_cancellations"] == 0
    assert ledger.counters["test_output_stream_failures"] == 1


def test_reverse_final_stream_metrics_include_terminal_carry() -> None:
    from number_compiler.resources.temporal_diagnostics import (
        collect_temporal_diagnostics_snapshot,
    )
    from tests.support.reference_arithmetic import reverse_add_digit_step

    expected: tuple[int, ...] = (6, 9, 1)
    for _ in range(8):
        expected, _ = reverse_add_digit_step(expected, 10)
    term = ReverseAddPoweredTerm(196, 8)
    assert tuple(term.iter_digits()) == expected
    counters = dict(term._ledger.counters)
    report = collect_temporal_diagnostics_snapshot(term._ledger)
    assert report.stream.requests == 1
    assert report.stream.emitted == len(expected) == 7
    assert report.stream.cancellations == report.stream.failures == 0
    # Q19's paired recurrence emits six pair digits here and the authenticated
    # final carry supplies the seventh public digit.
    assert counters["recursive_output_stream_emitted_digits"] == len(expected) == 7
    assert term._ledger.counters == counters
