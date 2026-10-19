"""Typed, read-only forensic views for the source-bound image owner."""

from __future__ import annotations

from collections.abc import Hashable, Mapping
from dataclasses import dataclass
from typing import TYPE_CHECKING, Generic, TypeVar

from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageCoreAuditSnapshot,
    SourceImageNodeView,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.source_bound_images import (
        SourceImageApplyKey,
        SourceImageProjectionRecord,
        SourceImageRelativeApplication,
        SourceImageRelativeKey,
    )
    from number_compiler.hashlife.execution.source_image_inventory import (
        SourceImageDemand,
        SourceImageID,
    )
    from number_compiler.hashlife.execution.source_image_seals import (
        PublicationSeal,
        TypedPayloadKey,
    )

NodeT = TypeVar("NodeT")
AdapterT = TypeVar("AdapterT")


@dataclass(frozen=True, slots=True)
class SourceImageApplyFrameAuditRecord:
    """Immutable field snapshot for one mutable postorder frame."""

    identity: int
    source: SourceImageID
    action: Hashable
    stage: int
    children: tuple[Hashable, Hashable] | None
    before: SourceImageID | None
    relative_key: SourceImageRelativeKey | None
    before_source: SourceImageID | None
    after_source: SourceImageID | None


@dataclass(frozen=True, slots=True)
class SourceImageWorkspaceAuditSnapshot:
    """Counter-free view of the reusable workspace's current retained state."""

    owner: int
    running: bool
    frame_count: int
    value_count: int
    frames: tuple[SourceImageApplyFrameAuditRecord, ...]
    values: tuple[SourceImageID, ...]
    entries: Mapping[tuple[str, object], object]
    store_identity: object


@dataclass(frozen=True, slots=True)
class SourceBoundSchedulerCoreAuditSnapshot(
    SourceImageCoreAuditSnapshot[NodeT, AdapterT], Generic[NodeT, AdapterT]
):
    """Exact read-only views of source-image publications and their stores."""

    origins: Mapping[tuple[tuple[str, str], TypedPayloadKey], SourceImageID]
    origin_store: object
    applications: Mapping[SourceImageApplyKey, SourceImageID]
    application_store: object
    relative: Mapping[SourceImageRelativeKey, SourceImageRelativeApplication]
    relative_store: object
    projections: Mapping[
        tuple[SourceImageID, SourceImageDemand], SourceImageProjectionRecord
    ]
    projection_store: object
    image_seals: SourceImageNodeView[PublicationSeal]
    image_seal_store: object
    projection_seals: Mapping[Hashable, PublicationSeal]
    projection_seal_store: object
    node_owner: int
    adapter_owner: int
    origin_owner: int
    application_owner: int
    relative_owner: int
    projection_owner: int
    image_seal_owner: int
    projection_seal_owner: int
    workspace: SourceImageWorkspaceAuditSnapshot
