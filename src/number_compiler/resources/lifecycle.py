"""Small shared helpers for deterministic owner teardown."""

from __future__ import annotations

from collections.abc import Callable, Iterable, Iterator
from contextlib import ExitStack, contextmanager


@contextmanager
def cleanup_on_exit(cleanup: Callable[[], object]) -> Iterator[None]:
    """Expose the active exception to a cleanup callback for chaining."""
    try:
        yield
    finally:
        cleanup()


@contextmanager
def cleanup_on_error(cleanup: Callable[[], object]) -> Iterator[None]:
    """Run rollback with the construction error active for exception chaining."""
    try:
        yield
    except BaseException as error:
        try:
            cleanup()
        except BaseException as cleanup_error:
            raise cleanup_error from error
        raise


def cleanup_all(cleanups: Iterable[Callable[[], object]]) -> None:
    """Run every cleanup and preserve failures through exception chaining.

    Owners use this when several independently owned stores must be released.
    A broken cleanup must not prevent later owners from being closed, while
    cleanup errors remain visible through ``ExitStack`` exception chaining.
    """
    callbacks = tuple(cleanups)
    with ExitStack() as stack:
        for cleanup in reversed(callbacks):
            stack.enter_context(cleanup_on_exit(cleanup))
