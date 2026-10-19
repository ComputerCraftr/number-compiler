"""Read-only inventory for request-scoped source-image scheduler storage."""

from __future__ import annotations

from collections.abc import Hashable, Iterator, Mapping
from dataclasses import dataclass
from types import MappingProxyType
from typing import Final, Generic, TypeVar

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.hashlife.execution.source_image_seals import (
    TypedPayloadKey,
    require_immutable_key,
)
from number_compiler.resources.ledger import ResourceInventory, ResourceLedger
from number_compiler.resources.stores import LedgerDict, LedgerList

NodeT = TypeVar("NodeT")
AdapterT = TypeVar("AdapterT")


SOURCE_IMAGE_CANDIDATE_VERSION: Final[str] = "candidate-v1"


@dataclass(frozen=True, slots=True)
class SourceImageID(ArenaHandle):
    """Scheduler-scoped identity of one admitted reachable image."""


@dataclass(frozen=True, slots=True)
class SourceImageBinding:
    """Complete semantic and geometric authority for a reachable image."""

    family: str
    semantic_version: str
    source: Hashable
    action: Hashable
    extent: int
    boundary_ports: tuple[Hashable, ...] = ()
    orientation: int = 1
    radix: int = 2
    precision: int | None = None

    def __post_init__(self) -> None:
        if type(self.family) is not str or not self.family:
            raise ValueError("source image family must be a nonempty string")
        if type(self.semantic_version) is not str or not self.semantic_version:
            raise ValueError("source image semantic version must be nonempty")
        require_immutable_key(self.source, "source image source")
        require_immutable_key(self.action, "source image action")
        if type(self.extent) is not int or self.extent < 0:
            raise ValueError("source image extent must be a nonnegative integer")
        if type(self.boundary_ports) is not tuple:
            raise TypeError("source image boundary ports must be immutable keys")
        for port in self.boundary_ports:
            require_immutable_key(port, "source image boundary port")
        if type(self.orientation) is not int or self.orientation not in (-1, 1):
            raise ValueError("source image orientation must be -1 or 1")
        if type(self.radix) is not int or self.radix < 2:
            raise ValueError("source image radix must be at least two")
        if self.precision is not None and (
            type(self.precision) is not int or self.precision < 0
        ):
            raise ValueError("source image precision must be nonnegative")


@dataclass(frozen=True, slots=True)
class SourceImageCandidate:
    payload: Hashable
    extent: int
    boundary_ports: tuple[Hashable, ...] = ()
    orientation: int = 1
    radix: int = 2
    precision: int | None = None
    failure_prefix: int | None = None

    def __post_init__(self) -> None:
        require_immutable_key(self.payload, "source image payload")
        SourceImageBinding(
            "candidate",
            SOURCE_IMAGE_CANDIDATE_VERSION,
            self.payload,
            self.payload,
            self.extent,
            self.boundary_ports,
            self.orientation,
            self.radix,
            self.precision,
        )
        if self.failure_prefix is not None and (
            type(self.failure_prefix) is not int or self.failure_prefix < 0
        ):
            raise ValueError("source image failure prefix must be nonnegative")


@dataclass(frozen=True, slots=True, eq=False)
class SourceImageDemand:
    name: str
    parameters: tuple[Hashable, ...] = ()

    def __post_init__(self) -> None:
        if type(self.name) is not str or not self.name:
            raise ValueError("source image demand name must be nonempty")
        if type(self.parameters) is not tuple:
            raise TypeError("source image demand parameters must be immutable")
        for value in self.parameters:
            require_immutable_key(value, "source image demand parameter")

    def __hash__(self) -> int:
        return hash((self.name, TypedPayloadKey(self.parameters)))

    def __eq__(self, other: object) -> bool:
        return (
            type(other) is SourceImageDemand
            and self.name == other.name
            and TypedPayloadKey(self.parameters) == TypedPayloadKey(other.parameters)
        )


@dataclass(frozen=True, slots=True)
class SourceImageProjection:
    value: Hashable

    def __post_init__(self) -> None:
        require_immutable_key(self.value, "source image projection")


@dataclass(frozen=True, slots=True)
class SourceImageView:
    identity: SourceImageID
    binding: SourceImageBinding
    payload: Hashable
    failure_prefix: int | None


class SourceImageNodeView(Generic[NodeT]):
    """Non-copying, read-only sequence view over a ledger-owned node store."""

    __slots__ = ("_store",)

    def __init__(self, store: LedgerList[NodeT]) -> None:
        self._store = store

    def __getitem__(self, index: int) -> NodeT:
        return self._store[index]

    def __len__(self) -> int:
        return len(self._store)

    def __iter__(self) -> Iterator[NodeT]:
        return iter(self._store)


@dataclass(frozen=True, slots=True)
class SourceImageCoreAuditSnapshot(Generic[NodeT, AdapterT]):
    """Shallow, read-only view of one source-image core's current authority."""

    ledger: ResourceLedger
    owner: ArenaToken
    kind: str
    closed: bool
    nodes: SourceImageNodeView[NodeT]
    node_store: object
    adapters: Mapping[tuple[str, str], AdapterT]
    adapter_store: object
    node_owner: int
    adapter_owner: int


class SourceImageInventoryMixin(Generic[NodeT, AdapterT]):
    """Expose the transient stores owned by a source-image scheduler core."""

    ledger: ResourceLedger
    owner: ArenaToken
    _KIND: str
    _closed: bool
    _nodes: LedgerList[NodeT]
    _adapters: LedgerDict[tuple[str, str], AdapterT]
    _node_owner: int
    _adapter_owner: int
    _origin_owner: int
    _apply_owner: int
    _projection_owner: int
    _relative_owner: int
    _workspace_owner: int

    def audit_snapshot(self) -> SourceImageCoreAuditSnapshot[NodeT, AdapterT]:
        """Expose current stores without constructing or copying their contents."""
        return SourceImageCoreAuditSnapshot(
            ledger=self.ledger,
            owner=self.owner,
            kind=self._KIND,
            closed=self._closed,
            nodes=SourceImageNodeView(self._nodes),
            node_store=self._nodes,
            adapters=MappingProxyType(self._adapters.backing_store),
            adapter_store=self._adapters,
            node_owner=self._node_owner,
            adapter_owner=self._adapter_owner,
        )

    def transient_inventory(self) -> tuple[ResourceInventory, ...]:
        """Snapshot request-scoped stores, excluding reusable adapter registration."""
        return tuple(
            self.ledger.inventory_owner(owner)
            for owner in (
                self._node_owner,
                self._origin_owner,
                self._apply_owner,
                self._projection_owner,
                self._relative_owner,
                self._workspace_owner,
            )
        )


__all__ = [
    "SOURCE_IMAGE_CANDIDATE_VERSION",
    "SourceImageBinding",
    "SourceImageCandidate",
    "SourceImageCoreAuditSnapshot",
    "SourceImageDemand",
    "SourceImageID",
    "SourceImageInventoryMixin",
    "SourceImageNodeView",
    "SourceImageProjection",
    "SourceImageView",
]
