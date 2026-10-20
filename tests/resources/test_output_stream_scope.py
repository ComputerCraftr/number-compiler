"""Scoped output cleanup preserves failures without inheriting caller errors."""

from collections.abc import Generator, Iterator
from typing import cast

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.output_stream_metrics import (
    closing_output_stream,
    measured_output_stream,
)
from number_compiler.sequences.reverse_add.source_chamber import (
    iter_admitted_same_carry_digits,
)
from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts


class _ClosableDigits(Iterator[int]):
    def __init__(self, *, fail_close: bool = False) -> None:
        self.values = iter((1, 2))
        self.fail_close = fail_close
        self.closes = 0

    def __next__(self) -> int:
        return next(self.values)

    def close(self) -> None:
        self.closes += 1
        if self.fail_close:
            raise RuntimeError("cleanup failed")


@pytest.mark.parametrize("complete", (False, True))
def test_output_scope_closes_once_on_partial_or_complete_consumption(
    complete: bool,
) -> None:
    source = _ClosableDigits()
    with closing_output_stream(source) as stream:
        assert next(stream) == 1
        if complete:
            assert tuple(stream) == (2,)
    assert source.closes == 1


def test_output_scope_preserves_consumer_failure_during_failed_cleanup() -> None:
    source = _ClosableDigits(fail_close=True)
    failure = ValueError("consumer failed")
    with pytest.raises(ValueError) as caught, closing_output_stream(source):
        raise failure
    assert caught.value is failure
    assert failure.__notes__ == [
        "Output iterator cleanup failed: RuntimeError: cleanup failed"
    ]
    assert source.closes == 1


def test_measured_stream_retains_both_errors_and_counts_one_failed_request() -> None:
    source = _ClosableDigits(fail_close=True)
    ledger = ResourceLedger()
    stream = measured_output_stream(ledger, "test", lambda: source)
    assert next(stream) == 1
    failure = ValueError("consumer failed")
    with pytest.raises(ValueError) as caught:
        stream.throw(failure)
    assert caught.value is failure
    assert failure.__notes__ == [
        "Output iterator cleanup failed: RuntimeError: cleanup failed"
    ]
    assert source.closes == 1
    assert ledger.counters["test_failures"] == 1
    assert ledger.counters["test_emitted_digits"] == 1


def test_measured_stream_cancel_records_close_failure() -> None:
    source = _ClosableDigits(fail_close=True)
    ledger = ResourceLedger()
    stream = measured_output_stream(ledger, "test", lambda: source)
    assert next(stream) == 1
    stream.close()
    assert source.closes == 1
    assert ledger.counters["test_cancellations"] == 1
    assert ledger.counters["test_failures"] == 1


@pytest.mark.parametrize("consumer_failure", (False, True))
def test_failed_instrumentation_preserves_output_and_cleanup_errors(
    consumer_failure: bool, monkeypatch: pytest.MonkeyPatch
) -> None:
    source = _ClosableDigits(fail_close=True)
    ledger = ResourceLedger()
    stream = measured_output_stream(ledger, "test", lambda: source)
    assert next(stream) == 1
    original = ledger.bump

    def fail_recording(name: str, amount: int = 1) -> None:
        if name == "test_failures":
            raise LookupError("counter failed")
        original(name, amount)

    monkeypatch.setattr(ledger, "bump", fail_recording)
    primary: BaseException
    if consumer_failure:
        primary = ValueError("consumer failed")
        with pytest.raises(ValueError) as caught:
            stream.throw(primary)
        assert caught.value is primary
        assert any("cleanup failed" in note for note in primary.__notes__)
    else:
        with pytest.raises(RuntimeError, match="cleanup failed") as cleanup:
            tuple(stream)
        primary = cleanup.value
    assert any("counter failed" in note for note in primary.__notes__)
    assert source.closes == 1


@pytest.mark.parametrize("measured", (False, True))
def test_successful_consumption_does_not_hide_cleanup_error_in_outer_except(
    measured: bool,
) -> None:
    source = _ClosableDigits(fail_close=True)
    ledger = ResourceLedger()
    try:
        raise ValueError("unrelated caller error")
    except ValueError:
        with pytest.raises(RuntimeError, match="cleanup failed"):
            if measured:
                assert tuple(measured_output_stream(ledger, "test", lambda: source))
            else:
                with closing_output_stream(source) as stream:
                    assert tuple(stream) == (1, 2)
    assert source.closes == 1
    if measured:
        assert ledger.counters["test_failures"] == 1
        assert ledger.counters["test_emitted_digits"] == 2


def test_output_scope_accepts_iterators_without_close() -> None:
    with closing_output_stream((3, 4)) as stream:
        assert tuple(stream) == (3, 4)


@pytest.mark.parametrize("second_pairs", (False, True))
def test_reverse_cancellation_closes_both_ports_when_one_cleanup_fails(
    second_pairs: bool,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ports = SourceCarryPorts(
        ExactSource((1,), 10, orbit="reverse-add"), ResourceLedger()
    )
    closed: list[bool] = []

    def first_ports(
        self: SourceCarryPorts, *, reflected: bool = False
    ) -> Generator[tuple[int, int], None, None]:
        try:
            yield 0, 0
        finally:
            closed.append(reflected)
            if not reflected:
                raise RuntimeError("forward cleanup failed")

    monkeypatch.setattr(SourceCarryPorts, "iter_first_ports", first_ports)
    stream = cast(
        Generator[int, None, None],
        ports.iter_second_pairs()
        if second_pairs
        else iter_admitted_same_carry_digits(ports, 2),
    )
    assert isinstance(stream, Generator)
    assert next(stream) == 4
    stream.close()
    assert sorted(closed) == [False, True]
    ports.dispose()
