"""Shared consumer-side instrumentation for public output streams."""

from __future__ import annotations

from collections.abc import Callable, Generator, Iterable, Iterator
from contextlib import contextmanager
from typing import TypeVar

from number_compiler.resources.ledger import ResourceLedger

_T = TypeVar("_T")


def _record_failure_without_masking(
    error: BaseException, record: Callable[[], None]
) -> None:
    try:
        record()
    except BaseException as recording_error:
        error.add_note(
            f"Output instrumentation failed: {type(recording_error).__name__}: "
            f"{recording_error}"
        )
        raise error from recording_error


def _close_output_iterator(
    stream: Iterator[_T] | None,
    on_failure: Callable[[], None] | None = None,
    *,
    preserve_exception: BaseException | None = None,
) -> None:
    close = None if stream is None else getattr(stream, "close", None)
    if close is None:
        return
    try:
        close()
    except BaseException as cleanup_error:
        if preserve_exception is not None:
            preserve_exception.add_note(
                f"Output iterator cleanup failed: {type(cleanup_error).__name__}: "
                f"{cleanup_error}"
            )
        if on_failure is not None:
            _record_failure_without_masking(
                cleanup_error if preserve_exception is None else preserve_exception,
                on_failure,
            )
        if preserve_exception is None:
            raise


@contextmanager
def closing_output_stream(source: Iterable[_T]) -> Iterator[Iterator[_T]]:
    """Close partially consumed output on conversion/consumer exceptions too."""
    stream = iter(source)
    try:
        yield stream
    except BaseException as error:
        _close_output_iterator(stream, preserve_exception=error)
        raise
    else:
        _close_output_iterator(stream)


def initialize_output_stream_metrics(ledger: ResourceLedger, prefix: str) -> None:
    """Publish measured zeroes when an output owner is created."""
    for suffix in ("requests", "emitted_digits", "cancellations", "failures"):
        ledger.bump(f"{prefix}_{suffix}", 0)


def measured_output_stream(
    ledger: ResourceLedger,
    prefix: str,
    source: Callable[[], Iterator[_T]],
) -> Generator[_T, None, None]:
    """Measure values as they reach the consumer, including partial closes.

    The source factory and request counter are deferred until the first pull.
    Emissions are counted immediately before each value is yielded. Closing an
    incomplete stream records one cancellation; any exception records one
    failure and is re-raised unchanged.
    """

    def observed() -> Generator[_T, None, None]:
        ledger.bump(f"{prefix}_requests")
        stream: Iterator[_T] | None = None
        failed = False
        primary_error: BaseException | None = None
        try:
            stream = iter(source())
            while True:
                try:
                    value = next(stream)
                except StopIteration:
                    return
                ledger.bump(f"{prefix}_emitted_digits")
                yield value
        except GeneratorExit as error:
            primary_error = error
            _record_failure_without_masking(
                error, lambda: ledger.bump(f"{prefix}_cancellations")
            )
            raise
        except BaseException as error:
            primary_error = error
            failed = True
            _record_failure_without_masking(
                error, lambda: ledger.bump(f"{prefix}_failures")
            )
            raise
        finally:
            _close_output_iterator(
                stream,
                None if failed else lambda: ledger.bump(f"{prefix}_failures"),
                preserve_exception=primary_error,
            )

    return observed()


__all__ = [
    "closing_output_stream",
    "initialize_output_stream_metrics",
    "measured_output_stream",
]
