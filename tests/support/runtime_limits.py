"""Hard execution deadlines for preserved release regressions."""

import signal
from collections.abc import Iterator
from contextlib import contextmanager
from time import monotonic
from types import FrameType
from typing import Never


@contextmanager
def deadline(seconds: float, description: str) -> Iterator[None]:
    """Fail, never skip, when a release observation exceeds its existing cap."""

    def expired(signum: int, frame: FrameType | None) -> Never:
        raise TimeoutError(
            f"{description} exceeded its {seconds:g}-second execution gate"
        )

    old_handler = signal.getsignal(signal.SIGALRM)
    old_delay, old_interval = signal.getitimer(signal.ITIMER_REAL)
    if old_delay:
        raise RuntimeError("release deadline must not replace another active watchdog")
    started = monotonic()
    signal.signal(signal.SIGALRM, expired)
    signal.setitimer(signal.ITIMER_REAL, seconds)
    try:
        yield
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, old_handler)
        if old_interval:
            signal.setitimer(
                signal.ITIMER_REAL,
                max(0, old_delay - (monotonic() - started)),
                old_interval,
            )
