"""Measured workload assertions, independent of the shared validation watchdog."""

from collections.abc import Generator
from contextlib import contextmanager
from time import monotonic


@contextmanager
def performance_bound(seconds: float, description: str) -> Generator[None, None, None]:
    """Preserve an existing performance assertion without installing a timer."""
    started = monotonic()
    yield
    elapsed = monotonic() - started
    assert elapsed <= seconds, (
        f"{description} took {elapsed:g}s, exceeding its {seconds:g}s workload bound"
    )
