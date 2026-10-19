"""Small shared helpers for deterministic owner teardown."""

from __future__ import annotations

import sys
from collections.abc import Callable, Generator, Iterable
from contextlib import ExitStack, contextmanager
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from number_compiler.resources.ledger import ResourceLedger


@contextmanager
def cleanup_on_exit(cleanup: Callable[[], object]) -> Generator[None, None, None]:
    """Expose the active exception to a cleanup callback for chaining."""
    try:
        yield
    finally:
        cleanup()


@contextmanager
def cleanup_on_error(cleanup: Callable[[], object]) -> Generator[None, None, None]:
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
    active_error = sys.exception()
    callbacks = tuple(cleanups)
    try:
        with ExitStack() as stack:
            for cleanup in reversed(callbacks):
                stack.enter_context(cleanup_on_exit(cleanup))
    except BaseException as cleanup_error:
        if active_error is not None and cleanup_error is not active_error:
            raise cleanup_error from active_error
        raise


def clear_accounted_store(
    ledger: ResourceLedger,
    owner: int,
    clear_store: Callable[[], object],
    measure: Callable[[], tuple[int, int]],
    pending: tuple[int, int],
    record_pending: Callable[[int, int], object],
) -> None:
    """Clear retained data while making accounting retries exact and idempotent."""
    old_entries, old_nodes = measure()
    try:
        clear_store()
    finally:
        # An interrupted clear may have removed some or all data. Retain the
        # exact unreleased delta, and keep the original error active while
        # accounting cleanup is attempted.
        entries, nodes = measure()
        release_entries = pending[0] + old_entries - entries
        release_nodes = pending[1] + old_nodes - nodes
        if release_entries < 0 or release_nodes < 0:
            raise RuntimeError("store clear produced an invalid retained-store delta")
        record_pending(release_entries, release_nodes)
        account = ledger._account(owner)
        if (
            account.entries != entries + release_entries
            or account.nodes != nodes + release_nodes
        ):
            raise RuntimeError("store clear differs from its owner reservation")
        try:
            if release_entries or release_nodes:
                ledger.release(owner, entries=release_entries, nodes=release_nodes)
        except BaseException as error:
            account = ledger._account(owner)
            remaining_entries = account.entries - entries
            remaining_nodes = account.nodes - nodes
            if not (
                0 <= remaining_entries <= release_entries
                and 0 <= remaining_nodes <= release_nodes
            ):
                raise RuntimeError(
                    "store clear release changed unrelated accounting"
                ) from error
            record_pending(remaining_entries, remaining_nodes)
            raise
        record_pending(0, 0)
