"""Charged iterative workspace and frames for source image applications."""

from __future__ import annotations

from collections.abc import Hashable
from dataclasses import dataclass
from types import MappingProxyType
from typing import TYPE_CHECKING

from number_compiler.hashlife.execution.source_bound_image_audit import (
    SourceImageApplyFrameAuditRecord,
    SourceImageWorkspaceAuditSnapshot,
)
from number_compiler.hashlife.execution.source_image_inventory import SourceImageID
from number_compiler.hashlife.execution.source_image_seals import TypedPayloadKey
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.source_bound_images import (
        SourceImageRelativeKey,
    )


@dataclass(slots=True)
class SourceImageApplyFrame:
    source: SourceImageID
    action: Hashable
    stage: int = 0
    children: tuple[Hashable, Hashable] | None = None
    before: SourceImageID | None = None
    relative_key: SourceImageRelativeKey | None = None
    before_source: SourceImageID | None = None
    after_source: SourceImageID | None = None


class SourceImageWorkspace:
    """Actual charged postorder storage, empty between source-image calls."""

    def __init__(self, ledger: ResourceLedger, owner: int) -> None:
        self._storage: LedgerDict[tuple[str, object], object] = ledger.make_dict(
            owner, nodes_per_entry=1
        )
        self._frame_count = 0
        self._value_count = 0
        self.running = False

    def __len__(self) -> int:
        return len(self._storage)

    @property
    def frames(self) -> tuple[SourceImageApplyFrame, ...]:
        return tuple(self._frame(index) for index in range(self._frame_count))

    @property
    def values(self) -> tuple[SourceImageID, ...]:
        return tuple(self._value(index) for index in range(self._value_count))

    def _frame(self, index: int) -> SourceImageApplyFrame:
        frame = self._storage["frame", index]
        if type(frame) is not SourceImageApplyFrame:
            raise AssertionError("source image workspace contains another frame sort")
        return frame

    def _value(self, index: int) -> SourceImageID:
        value = self._storage["value", index]
        if type(value) is not SourceImageID:
            raise AssertionError("source image workspace contains another value sort")
        return value

    def push_frame(self, frame: SourceImageApplyFrame) -> None:
        self._storage["frame", self._frame_count] = frame
        self._frame_count += 1

    def pop_frame(self) -> SourceImageApplyFrame:
        if not self._frame_count:
            raise IndexError("pop from empty source image frame stack")
        index = self._frame_count - 1
        frame = self._frame(index)
        del self._storage["frame", index]
        self._frame_count = index
        return frame

    def has_frames(self) -> bool:
        return self._frame_count > 0

    def push_value(self, value: SourceImageID) -> None:
        self._storage["value", self._value_count] = value
        self._value_count += 1

    def pop_value(self) -> SourceImageID:
        if not self._value_count:
            raise IndexError("pop from empty source image value stack")
        index = self._value_count - 1
        value = self._value(index)
        del self._storage["value", index]
        self._value_count = index
        return value

    def has_values(self) -> bool:
        return self._value_count > 0

    def value_count(self) -> int:
        return self._value_count

    @staticmethod
    def _active_key(action: tuple[str, str, Hashable]) -> tuple[str, object]:
        return "active", (action[0], action[1], TypedPayloadKey(action[2]))

    def audit_snapshot(self) -> SourceImageWorkspaceAuditSnapshot:
        """Return typed retained state without counters or cache mutation."""
        return SourceImageWorkspaceAuditSnapshot(
            owner=self._storage.owner,
            running=self.running,
            frame_count=self._frame_count,
            value_count=self._value_count,
            frames=tuple(
                SourceImageApplyFrameAuditRecord(
                    identity=id(frame),
                    source=frame.source,
                    action=frame.action,
                    stage=frame.stage,
                    children=frame.children,
                    before=frame.before,
                    relative_key=frame.relative_key,
                    before_source=frame.before_source,
                    after_source=frame.after_source,
                )
                for frame in self.frames
            ),
            values=self.values,
            entries=MappingProxyType(self._storage.backing_store),
            store_identity=self._storage,
        )

    def contains_active(self, action: tuple[str, str, Hashable]) -> bool:
        return self._active_key(action) in self._storage

    def add_active(self, action: tuple[str, str, Hashable]) -> None:
        key = self._active_key(action)
        if key in self._storage:
            raise ValueError("source image action is already active")
        self._storage[key] = None

    def remove_active(self, action: tuple[str, str, Hashable]) -> None:
        key = self._active_key(action)
        if key not in self._storage:
            raise KeyError(action)
        del self._storage[key]

    def clear(self) -> None:
        self._storage.clear()
        self._frame_count = 0
        self._value_count = 0
        self.running = False
