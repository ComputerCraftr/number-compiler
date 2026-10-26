"""Charged query workspace for iterative fused-interface traversal."""

from __future__ import annotations

from collections.abc import Generator
from contextlib import contextmanager
from functools import partial
from typing import TYPE_CHECKING

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.lifecycle import cleanup_all
from number_compiler.resources.metric_keys import resources as _resources_keys
from number_compiler.resources.metric_keys import shared as _shared_keys
from number_compiler.resources.stores import LedgerList

if TYPE_CHECKING:
    from number_compiler.resources.tile_runtime_audit_contracts import (
        FusedTraversalWorkspaceAuditSnapshot,
    )


def fused_traversal_workspace_owner_names(
    prefix: str,
) -> tuple[str, str, str]:
    """Return the three distinct ledger names owned by one workspace."""
    if type(prefix) is not str:
        raise TypeError("fused traversal owner prefix must be a string")
    return (
        prefix + "-fused-workspace",
        prefix + "-fused-frames",
        prefix + "-fused-values",
    )


class FusedTraversalWorkspace:
    """Own visible O(depth) frame and result stacks for one fused query."""

    def __init__(self, ledger: ResourceLedger, prefix: str) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("fused traversal workspace requires one resource ledger")
        self.ledger = ledger
        owner_names = fused_traversal_workspace_owner_names(prefix)
        ledger.require_fresh_owner_names(owner_names)
        self.owner = ledger.register(owner_names[0], "fused_interface_workspace")
        self.frame_owner = ledger.register(owner_names[1], "fused_interface_workspace")
        self.value_owner = ledger.register(owner_names[2], "fused_interface_workspace")
        self.frames: LedgerList[object] = ledger.make_list(
            self.frame_owner, nodes_per_entry=0, append_only=False
        )
        self.values: LedgerList[object] = ledger.make_list(
            self.value_owner, nodes_per_entry=0, append_only=False
        )
        self.nodes = 0
        self.active = False
        self._closing = False
        self._disposed = False
        self.max_frames = 0
        self.max_values = 0
        ledger.register_container(
            self.owner,
            self,
            node_count=lambda: self.nodes,
            payloads=lambda: (),
        )

    def __len__(self) -> int:
        return 0

    def audit_snapshot(self) -> FusedTraversalWorkspaceAuditSnapshot:
        """Return immutable scratch values and exact backing-store identities."""
        from number_compiler.resources.tile_runtime_audit_contracts import (
            FusedTraversalWorkspaceAuditSnapshot,
        )

        return FusedTraversalWorkspaceAuditSnapshot(
            ledger=self.ledger,
            workspace_identity=id(self),
            owner=self.owner,
            frame_owner=self.frame_owner,
            value_owner=self.value_owner,
            frame_store_identity=id(self.frames),
            value_store_identity=id(self.values),
            frames=tuple(self.frames),
            values=tuple(self.values),
            nodes=self.nodes,
            active=self.active,
            disposed=self._disposed,
            max_frames=self.max_frames,
            max_values=self.max_values,
        )

    def _check_open(self) -> None:
        if self._closing or self._disposed:
            raise RuntimeError("fused traversal workspace is closing or disposed")

    def _append(self, owner: int, store: LedgerList[object], value: object) -> None:
        prior_size = len(store)
        self.ledger.reserve(owner, entries=1)
        try:
            store.append(value)
        except BaseException:
            if len(store) != prior_size:
                store.rollback_unpublished(prior_size)
            self.ledger.release(owner, entries=1)
            raise
        count = len(self.frames) + len(self.values)
        peak = self.ledger.counters.get(_shared_keys.TILE_FUSED_WORKSPACE_PEAK, 0)
        if count > peak:
            self.ledger.bump(_shared_keys.TILE_FUSED_WORKSPACE_PEAK, count - peak)
        backing = self.frames.backing_size_bytes + self.values.backing_size_bytes
        old_backing = self.ledger.counters.get(
            _resources_keys.TILE_FUSED_WORKSPACE_BACKING_PEAK_BYTES, 0
        )
        if backing > old_backing:
            self.ledger.bump(
                _resources_keys.TILE_FUSED_WORKSPACE_BACKING_PEAK_BYTES,
                backing - old_backing,
            )

    def append_frame(self, value: object) -> None:
        self._check_open()
        if not self.active:
            raise RuntimeError("fused traversal frame requires an active scope")
        if len(self.frames) >= self.max_frames:
            raise RuntimeError("fused traversal exceeded its frame bound")
        self._append(self.frame_owner, self.frames, value)

    def append_value(self, value: object) -> None:
        self._check_open()
        if not self.active:
            raise RuntimeError("fused traversal value requires an active scope")
        if len(self.values) >= self.max_values:
            raise RuntimeError("fused traversal exceeded its value bound")
        self._append(self.value_owner, self.values, value)

    def _pop(self, owner: int, store: LedgerList[object]) -> object:
        self._check_open()
        if not self.active:
            raise RuntimeError("fused traversal pop requires an active scope")
        prior_size = len(store)
        value = store[-1]
        try:
            store.pop()
            self.ledger.release(owner, entries=1)
        except BaseException:
            try:
                if len(store) != prior_size:
                    charged = self.ledger.account_status(owner).entries
                    if charged == prior_size:
                        store.append(value)
                    elif charged != len(store):
                        raise RuntimeError(
                            "failed fused pop changed unrelated accounting"
                        )
            finally:
                value = None
            raise
        return value

    def pop_frame(self) -> object:
        return self._pop(self.frame_owner, self.frames)

    def pop_value(self) -> object:
        return self._pop(self.value_owner, self.values)

    def _clear_stack(self, owner: int, store: LedgerList[object]) -> None:
        """Release removed entries, including a previous interrupted release.

        Each stack has an exclusive ledger owner. Its remaining charge is the
        retry record when clearing or release fails; no parallel counter is
        needed, and surviving entries remain charged after a partial clear.
        """
        try:
            if store:
                store.clear()
        finally:
            charged = self.ledger.account_status(owner).entries
            retained = len(store)
            if charged < retained:
                raise RuntimeError("fused stack exceeds its owner reservation")
            if charged > retained:
                self.ledger.release(owner, entries=charged - retained)

    def _cleanup(self) -> None:
        try:
            cleanup_all(
                (
                    partial(self._clear_stack, self.frame_owner, self.frames),
                    partial(self._clear_stack, self.value_owner, self.values),
                )
            )
        finally:
            self.active = False
            self.max_frames = self.max_values = 0
            # Retain the workspace charge until both stacks are gone and
            # their entry charges released. A failed cleanup blocks reuse;
            # dispose can retry it without releasing any charge twice.
            if (
                not self.frames
                and not self.values
                and not self.ledger.account_status(self.frame_owner).entries
                and not self.ledger.account_status(self.value_owner).entries
            ):
                try:
                    self.ledger.release(self.owner, nodes=self.nodes)
                finally:
                    self.nodes = self.ledger.account_status(self.owner).nodes

    @contextmanager
    def scope(self, level: int, port_count: int) -> Generator[None, None, None]:
        self._check_open()
        if any(type(value) is not int for value in (level, port_count)):
            raise TypeError("fused traversal bounds require exact integers")
        if level < 0 or port_count < 0:
            raise ValueError("fused traversal bounds must be nonnegative")
        if self.active or self.nodes or self.frames or self.values:
            raise RuntimeError("fused traversal workspace is already active")
        # At depth d there are at most 2d+1 frames and d+1 result values.
        # A frame owns one list reference, three tuple fields, one ports tuple,
        # and that tuple's finite values.  A result owns its list reference and
        # ID.  The final term covers the two child contexts and one request key
        # that exist transiently while a parent is expanded or published.
        frame_slots = (2 * level + 1) * (port_count + 5)
        value_slots = 2 * (level + 1)
        transient_slots = 4 * port_count + 32
        nodes = frame_slots + value_slots + transient_slots
        self.ledger.reserve(self.owner, nodes=nodes)
        try:
            self.nodes, self.active = nodes, True
            self.max_frames, self.max_values = 2 * level + 1, level + 1
            peak = self.ledger.counters.get(
                _resources_keys.TILE_FUSED_WORKSPACE_RESERVED_REFERENCE_PEAK, 0
            )
            if nodes > peak:
                self.ledger.bump(
                    _resources_keys.TILE_FUSED_WORKSPACE_RESERVED_REFERENCE_PEAK,
                    nodes - peak,
                )
            yield
        finally:
            self._cleanup()

    def dispose(self) -> None:
        """Close the three auditable owners after all scoped work is cleared."""
        if self._disposed:
            return
        if self.active:
            raise RuntimeError("cannot dispose an active fused traversal workspace")
        self._closing = True
        self._cleanup()
        self.ledger.mark_disposed(self.frame_owner)
        self.ledger.mark_disposed(self.value_owner)
        self.ledger.mark_disposed(self.owner)
        self._disposed = True


__all__ = ["FusedTraversalWorkspace", "fused_traversal_workspace_owner_names"]
