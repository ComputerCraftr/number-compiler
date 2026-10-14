"""Owned rollback state for completed-result tile acquisitions."""

from __future__ import annotations

from collections.abc import Callable
from functools import partial

from number_compiler.hashlife.tiles.tiles import TileArena, TileID, TileLease
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.lifecycle import cleanup_all, clear_accounted_store
from number_compiler.resources.stores import LedgerList


class ResultAcquisitionLeaseOwner:
    """Ledger-owned retry records for partial completed-result acquisitions."""

    def __init__(self, ledger: ResourceLedger, tiles: TileArena, prefix: str) -> None:
        self.ledger, self.tiles = ledger, tiles
        self.owner = ledger.register(
            prefix + "-acquisition-cleanup", "completed_result_acquisition_cleanup"
        )
        self.records: LedgerList[TileLease | int | None] = ledger.make_list(
            self.owner, nodes_per_entry=1, append_only=False
        )
        self.clear_entries = self.clear_nodes = 0
        self.pending_tile_reservations = 0

    def acquire(
        self,
        tile_ids: tuple[TileID, ...],
        *,
        reserved: bool,
        after_acquire: Callable[[], object],
    ) -> tuple[TileLease, ...]:
        count = len(tile_ids)
        tile_reservation_owned = reserved
        try:
            self.retry()
            if not reserved:
                self.ledger.reserve(self.tiles._lease_owner, entries=count)
                tile_reservation_owned = True
            self._prepare(count)
        except BaseException:
            if tile_reservation_owned:
                self._release_reservation(count)
            raise
        leases: list[TileLease] = []
        try:
            for index, tile in enumerate(tile_ids):
                lease = self.tiles._acquire_reserved(tile)
                leases.append(lease)
                self.records[index] = lease
            result = tuple(leases)
            self._clear()
            after_acquire()
            return result
        except BaseException:
            cleanups: list[Callable[[], object]] = []
            if leases and not self.records:
                cleanups.append(lambda: self._restore_leases(leases))
            cleanups.extend((self._rollback, lambda: self._close_unrecorded(leases)))
            cleanup_all(cleanups)
            raise

    def _prepare(self, count: int) -> None:
        if self.records or self.clear_entries:
            raise RuntimeError("tile acquisition cleanup records were not drained")
        if not count:
            return
        self.ledger.reserve(self.owner, entries=count, nodes=count)
        try:
            self.records.extend(1 for _ in range(count))
        except BaseException:
            unwritten = count - len(self.records)
            self.clear_entries = unwritten
            self.clear_nodes = unwritten
            self._clear()
            raise

    def _clear(self) -> None:
        def measure() -> tuple[int, int]:
            entries = len(self.records)
            return entries, entries

        def record(entries: int, nodes: int) -> None:
            self.clear_entries, self.clear_nodes = entries, nodes

        clear_accounted_store(
            self.ledger,
            self.owner,
            self.records.clear,
            measure,
            (self.clear_entries, self.clear_nodes),
            record,
        )

    def _restore_leases(self, leases: list[TileLease]) -> None:
        account = self.ledger._account(self.owner)
        count = len(leases)
        if self.records or account.entries > count or account.nodes > count:
            raise RuntimeError(
                "tile acquisition cleanup reservation cannot be restored"
            )
        self.ledger.reserve(
            self.owner,
            entries=count - account.entries,
            nodes=count - account.nodes,
        )
        self.clear_entries = self.clear_nodes = 0
        try:
            self.records.extend(leases)
        finally:
            # A failed append still owns the reserved but unwritten suffix.
            # Rollback releases written leases and drains this exact remainder.
            self.clear_entries = self.clear_nodes = count - len(self.records)

    def _rollback(self) -> None:
        callbacks: list[Callable[[], object]] = []
        for index in reversed(range(len(self.records))):
            record = self.records[index]
            if type(record) is TileLease:
                callbacks.append(partial(self._close_lease, index, record))
            elif type(record) is int and record == 1:
                callbacks.append(partial(self._release_slot, index))
            elif record is not None:
                raise RuntimeError("tile acquisition cleanup record is malformed")
        try:
            cleanup_all(callbacks)
        finally:
            if all(record is None for record in self.records):
                self._clear()

    def _close_unrecorded(self, leases: list[TileLease]) -> None:
        recorded = {id(record) for record in self.records if type(record) is TileLease}
        cleanup_all(
            tuple(
                lease.close
                for lease in leases
                if id(lease) not in recorded and not lease._closed
            )
        )

    def _close_lease(self, index: int, lease: TileLease) -> None:
        try:
            lease.close()
        except BaseException:
            if lease._closed:
                self.records[index] = None
            raise
        self.records[index] = None

    def _release_slot(self, index: int) -> None:
        owner = self.tiles._lease_owner
        before = self.ledger._account(owner).entries
        try:
            self.ledger.release(owner, entries=1)
        except BaseException as error:
            applied = before - self.ledger._account(owner).entries
            if applied == 1:
                self.records[index] = None
            elif applied != 0:
                raise RuntimeError(
                    "tile lease rollback accounting changed unexpectedly"
                ) from error
            raise
        self.records[index] = None

    def _release_reservation(self, entries: int) -> None:
        if entries <= 0:
            return
        owner = self.tiles._lease_owner
        before = self.ledger._account(owner).entries
        try:
            self.ledger.release(owner, entries=entries)
        except BaseException as error:
            applied = before - self.ledger._account(owner).entries
            if not 0 <= applied <= entries:
                raise RuntimeError(
                    "tile lease rollback accounting changed unexpectedly"
                ) from error
            self.pending_tile_reservations += entries - applied
            raise

    def _retry_tile_reservations(self) -> None:
        entries = self.pending_tile_reservations
        if not entries:
            return
        self.pending_tile_reservations = 0
        self._release_reservation(entries)

    def retry(self) -> None:
        cleanups: list[Callable[[], object]] = [self._retry_tile_reservations]
        if self.records or self.clear_entries:
            cleanups.append(self._rollback)
        cleanup_all(cleanups)
