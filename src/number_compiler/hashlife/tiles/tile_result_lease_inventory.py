"""Charged bookkeeping for boundary operands retained by result leases."""

from __future__ import annotations

from collections.abc import Callable

from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict


class BoundaryOperandLeaseInventory:
    """A non-semantic multiset of exact views retained by issued leases."""

    def __init__(self, ledger: ResourceLedger, prefix: str) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("boundary lease inventory requires one resource ledger")
        self.ledger = ledger
        self.owner = ledger.register(
            prefix + "-boundary-operands",
            "completed_result_boundary_operand_leases",
        )
        self.records: LedgerDict[BoundaryTileView, int] = ledger.make_dict(self.owner)
        ledger.register_container(
            self.owner,
            self.records,
            payloads=self.records.items,
        )
        self.pending_release_entries = 0

    @staticmethod
    def _validate_views(views: tuple[BoundaryTileView, ...]) -> None:
        if type(views) is not tuple or any(
            type(view) is not BoundaryTileView for view in views
        ):
            raise TypeError("boundary lease operands require exact immutable views")
        if len(set(views)) != len(views):
            raise ValueError("boundary lease operands must be canonicalized")

    def acquire(self, views: tuple[BoundaryTileView, ...]) -> None:
        """Record one issued lease after validating its unique operand views."""
        self._validate_views(views)
        self.retry_release()
        additions = sum(view not in self.records for view in views)
        self.ledger.reserve(self.owner, entries=additions)
        previous = tuple((view, self.records.get(view)) for view in views)
        try:
            for view, count in previous:
                if count is not None and (type(count) is not int or count < 1):
                    raise ValueError("boundary lease operand count is corrupt")
                self.records[view] = 1 if count is None else count + 1
        except BaseException as error:
            try:
                for view, count in previous:
                    if count is None:
                        self.records.pop(view, None)
                    else:
                        self.records[view] = count
                self._release_entries(additions)
            except BaseException as cleanup_error:
                raise cleanup_error from error
            raise

    def release(
        self,
        views: tuple[BoundaryTileView, ...],
        *,
        on_mutated: Callable[[], object] | None = None,
    ) -> None:
        """Release exactly one issued lease's operand-view references."""
        self._validate_views(views)
        self.retry_release()
        counts = tuple((view, self.records.get(view)) for view in views)
        if any(type(count) is not int or count < 1 for _, count in counts):
            raise ValueError("boundary lease operand is not retained")
        removed = sum(count == 1 for _, count in counts)
        try:
            for view, count in counts:
                if type(count) is not int:
                    raise ValueError("boundary lease operand count is corrupt")
                if count == 1:
                    del self.records[view]
                else:
                    self.records[view] = count - 1
        except BaseException as error:
            try:
                for view, count in counts:
                    if type(count) is int:
                        self.records[view] = count
            except BaseException as cleanup_error:
                raise cleanup_error from error
            raise
        if not removed:
            if on_mutated is not None:
                on_mutated()
            return
        self.pending_release_entries = removed
        if on_mutated is not None:
            on_mutated()
        self.retry_release()

    def retry_release(self) -> None:
        entries = self.pending_release_entries
        if not entries:
            return
        self.pending_release_entries = 0
        self._release_entries(entries)

    def _release_entries(self, entries: int) -> None:
        if entries <= 0:
            return
        before = self.ledger.account_usage(self.owner)[0]
        try:
            self.ledger.release(self.owner, entries=entries)
        except BaseException as error:
            applied = before - self.ledger.account_usage(self.owner)[0]
            if not 0 <= applied <= entries:
                raise RuntimeError(
                    "boundary operand release changed unrelated accounting"
                ) from error
            self.pending_release_entries += entries - applied
            raise


__all__ = ["BoundaryOperandLeaseInventory"]
