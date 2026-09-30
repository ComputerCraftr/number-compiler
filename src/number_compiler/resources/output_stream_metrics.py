"""Shared consumer-side instrumentation for public output streams."""

from __future__ import annotations

from collections.abc import Callable, Generator, Iterable, Iterator
from contextlib import contextmanager
from typing import TypeVar

from number_compiler.resources.ledger import ResourceLedger

_T = TypeVar("_T")


def _close_output_iterator(
    stream: Iterator[_T] | None,
    on_failure: Callable[[], None] | None = None,
    *,
    preserve_exception: bool = False,
) -> None:
    close = None if stream is None else getattr(stream, "close", None)
    if close is None:
        return
    try:
        close()
    except BaseException:
        if on_failure is not None:
            on_failure()
        if not preserve_exception:
            raise


@contextmanager
def closing_output_stream(source: Iterable[_T]) -> Iterator[Iterator[_T]]:
    """Close partially consumed output on conversion/consumer exceptions too."""
    stream = iter(source)
    try:
        yield stream
    except BaseException:
        _close_output_iterator(stream, preserve_exception=True)
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
        cancelled = False
        try:
            stream = iter(source())
            while True:
                try:
                    value = next(stream)
                except StopIteration:
                    return
                ledger.bump(f"{prefix}_emitted_digits")
                yield value
        except GeneratorExit:
            cancelled = True
            ledger.bump(f"{prefix}_cancellations")
            raise
        except BaseException:
            failed = True
            ledger.bump(f"{prefix}_failures")
            raise
        finally:
            _close_output_iterator(
                stream,
                None if failed else lambda: ledger.bump(f"{prefix}_failures"),
                preserve_exception=failed or cancelled,
            )

    return observed()


__all__ = [
    "closing_output_stream",
    "initialize_output_stream_metrics",
    "measured_output_stream",
]
