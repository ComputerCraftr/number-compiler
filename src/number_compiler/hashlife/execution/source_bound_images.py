"""Authenticated source-bound images owned by the canonical tile scheduler."""

from __future__ import annotations

from collections.abc import Hashable, Mapping
from dataclasses import dataclass
from types import MappingProxyType
from typing import Protocol, runtime_checkable

from number_compiler.arithmetic.contracts.input_validation import (
    is_exact_object_tuple,
)
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.execution.source_bound_image_audit import (
    SourceBoundSchedulerCoreAuditSnapshot,
)
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageBinding,
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageID,
    SourceImageInventoryMixin,
    SourceImageNodeView,
    SourceImageProjection,
    SourceImageView,
)
from number_compiler.hashlife.execution.source_image_seals import (
    PublicationSeal,
    PublicationSeals,
    TypedPayloadKey,
    publication_matches,
    publication_matches_readonly,
    publication_seal,
    require_immutable_key,
    typed_payload_equal,
)
from number_compiler.hashlife.execution.source_image_workspace import (
    SourceImageApplyFrame as SourceImageApplyFrame,
)
from number_compiler.hashlife.execution.source_image_workspace import (
    SourceImageWorkspace,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)
from number_compiler.resources.stores import LedgerDict, LedgerList


class SourceBoundImageAdapter(Protocol):
    """Family laws consumed by the scheduler's common chronological driver."""

    ledger: ResourceLedger
    family: str
    semantic_version: str

    def validate_source(self, source: Hashable) -> None: ...

    def validate_action(self, action: Hashable) -> None: ...

    def validate_payload(self, payload: Hashable) -> None: ...

    def identity_action(self, source: Hashable) -> Hashable: ...

    def action_children(self, action: Hashable) -> tuple[Hashable, Hashable] | None: ...

    def compose_actions(self, before: Hashable, after: Hashable) -> Hashable: ...

    def admit_source(self, source: Hashable) -> SourceImageCandidate: ...

    def apply_primitive(
        self, action: Hashable, source: SourceImageView
    ) -> SourceImageCandidate: ...

    def compose_chronological(
        self,
        action: Hashable,
        source: SourceImageView,
        before: SourceImageView,
        after: SourceImageView,
    ) -> SourceImageCandidate: ...

    def admitted_input_key(
        self, action: Hashable, source: SourceImageView
    ) -> Hashable | None:
        """Return complete relative state only where transport is exact."""
        ...

    def transport_reuse(
        self,
        action: Hashable,
        cached_source: SourceImageView,
        cached_result: SourceImageView,
        source: SourceImageView,
    ) -> SourceImageCandidate:
        """Rebind one equal admitted relative transfer to this exact source."""
        ...

    def project(
        self, image: SourceImageView, demand: SourceImageDemand
    ) -> SourceImageProjection: ...

    def first_failure(self, image: SourceImageView) -> object | None: ...


@runtime_checkable
class SourceBoundImageBindingAuditor(Protocol):
    """Optional pure audit for one already-published image binding.

    Resource audits use this extension when a family can validate the complete
    source/action/payload/geometry relationship without mutating execution
    state or charging query work. It is deliberately separate from the
    scheduler protocol so existing adapters need not invent a redundant
    checker when their ownership is already audited elsewhere. Returned frozen
    records must be sealed boundary-port members or direct payload members;
    they mark only those exact owner-bound records as checked metadata in
    resource audits.
    """

    def audit_image_binding(
        self,
        binding: SourceImageBinding,
        payload: Hashable,
        failure_prefix: Hashable | None,
    ) -> tuple[Hashable, ...] | None: ...


_SOURCE_BOUND_ADAPTER_METHODS = (
    "validate_source",
    "validate_action",
    "validate_payload",
    "identity_action",
    "action_children",
    "compose_actions",
    "admit_source",
    "apply_primitive",
    "compose_chronological",
    "admitted_input_key",
    "transport_reuse",
    "project",
    "first_failure",
)


def source_bound_adapter_shape(
    adapter: SourceBoundImageAdapter, ledger: ResourceLedger
) -> bool:
    """Check the exact callable surface admitted by source-image registration."""
    try:
        if adapter.ledger is not ledger:
            return False
        if type(adapter.family) is not str or not adapter.family:
            return False
        if type(adapter.semantic_version) is not str or not adapter.semantic_version:
            return False
        if any(
            not callable(getattr(adapter, name, None))
            for name in _SOURCE_BOUND_ADAPTER_METHODS
        ):
            return False
        auditor = getattr(adapter, "audit_image_binding", None)
        return auditor is None or callable(auditor)
    except (AttributeError, RuntimeError, TypeError, ValueError):
        return False


@runtime_checkable
class SourceBoundCompositeAdapter(Protocol):
    """Construct a complete image using a demand to select the construction.

    Every returned candidate must support subsequent actions, projections and
    failure descent, independently of the demand that selected this constructor.
    Applications are memoized by source and action, not observer demand: a
    demand-specific projection alone must never be published as an image.

    ``None`` requests the image itself. Returning ``None`` delegates to the
    scheduler's child traversal; a family may refuse instead if that traversal
    cannot construct an admitted image.
    """

    def apply_composite(
        self,
        action: Hashable,
        source: SourceImageView,
        demand: SourceImageDemand | None,
    ) -> SourceImageCandidate | None: ...


@dataclass(frozen=True, slots=True)
class SourceImageRecord:
    adapter_key: tuple[str, str]
    adapter: SourceBoundImageAdapter
    binding_audit_required: bool
    binding: SourceImageBinding
    payload: Hashable
    failure_prefix: int | None
    publication_owner: object
    publication_snapshot: PublicationSeal
    publication_provenance: tuple[str, object, object | None]


_IMAGE_RECORD_SEAL = object()


@dataclass(frozen=True, slots=True)
class SourceImageProjectionRecord:
    image: SourceImageID
    demand: SourceImageDemand
    projection: SourceImageProjection
    publication_owner: object
    publication_snapshot: PublicationSeal


@dataclass(frozen=True, slots=True, eq=False)
class SourceImageApplyKey:
    adapter_key: tuple[str, str]
    source: SourceImageID
    action: Hashable

    def __hash__(self) -> int:
        return hash((self.adapter_key, self.source, TypedPayloadKey(self.action)))

    def __eq__(self, other: object) -> bool:
        return (
            type(other) is SourceImageApplyKey
            and self.adapter_key == other.adapter_key
            and self.source == other.source
            and TypedPayloadKey(self.action) == TypedPayloadKey(other.action)
        )


@dataclass(frozen=True, slots=True, eq=False)
class SourceImageRelativeKey:
    adapter_key: tuple[str, str]
    action: Hashable
    admitted_input: Hashable

    def __hash__(self) -> int:
        return hash(
            (
                self.adapter_key,
                TypedPayloadKey(self.action),
                TypedPayloadKey(self.admitted_input),
            )
        )

    def __eq__(self, other: object) -> bool:
        return (
            type(other) is SourceImageRelativeKey
            and self.adapter_key == other.adapter_key
            and TypedPayloadKey(self.action) == TypedPayloadKey(other.action)
            and TypedPayloadKey(self.admitted_input)
            == TypedPayloadKey(other.admitted_input)
        )


@dataclass(frozen=True, slots=True)
class SourceImageRelativeApplication:
    source: SourceImageID
    result: SourceImageID


class SourceBoundSchedulerCore(
    SourceImageInventoryMixin[SourceImageRecord, SourceBoundImageAdapter]
):
    _KIND = "source-bound-image"

    def __init__(self, ledger: ResourceLedger) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("source image authority requires a resource ledger")
        self.ledger = ledger
        # Declare exact instruments before the first origin or application.
        # An absent key after this point is missing evidence, not zero work.
        for counter in (
            _execution_keys.SOURCE_IMAGE_APPLICATION_REQUESTS,
            _execution_keys.SOURCE_IMAGE_APPLICATION_ATTEMPTS,
            _execution_keys.SOURCE_IMAGE_APPLICATION_HITS,
            _execution_keys.SOURCE_IMAGE_RELATIVE_TRANSFER_HITS,
            _execution_keys.SOURCE_IMAGE_APPLICATION_MISSES,
            _execution_keys.SOURCE_IMAGE_APPLICATION_PUBLICATIONS,
            _execution_keys.SOURCE_IMAGE_ORIGIN_PUBLICATIONS,
            _execution_keys.SOURCE_IMAGE_PUBLICATIONS,
            _execution_keys.SOURCE_IMAGE_PROJECTION_REQUESTS,
            _execution_keys.SOURCE_IMAGE_PROJECTION_HITS,
            _execution_keys.SOURCE_IMAGE_PROJECTION_MISSES,
            _execution_keys.SOURCE_IMAGE_PROJECTION_PUBLICATIONS,
            _execution_keys.SOURCE_IMAGE_POSTORDER_FRAMES,
            _execution_keys.SOURCE_IMAGE_PRIMITIVE_APPLICATIONS,
            _execution_keys.SOURCE_IMAGE_CHRONOLOGICAL_COMPOSITIONS,
            "source_image_composite_applications",
            "source_image_demanded_composite_applications",
        ):
            self.ledger.bump(counter, 0)
        self.owner = ArenaToken("tile-source-images")
        self._closed = False
        prefix = f"tile-source-images-{len(self.ledger.inventory())}"
        self._adapter_owner = self.ledger.register(
            prefix + "-adapters", "source_image_adapter"
        )
        self._node_owner = self.ledger.register(prefix + "-nodes", "source_image")
        self._origin_owner = self.ledger.register(
            prefix + "-origins", "source_image_origin"
        )
        self._apply_owner = self.ledger.register(
            prefix + "-applications", "source_image_application"
        )
        self._projection_owner = self.ledger.register(
            prefix + "-projections", "source_image_projection"
        )
        self._relative_owner = self.ledger.register(
            prefix + "-relative", "source_image_relative_transfer"
        )
        self._workspace_owner = self.ledger.register(
            prefix + "-workspace", "source_image_workspace"
        )
        self._workspace = SourceImageWorkspace(self.ledger, self._workspace_owner)
        self._adapters: LedgerDict[tuple[str, str], SourceBoundImageAdapter] = (
            self.ledger.make_dict(self._adapter_owner)
        )
        self._nodes: LedgerList[SourceImageRecord] = self.ledger.make_list(
            self._node_owner, append_only=False
        )
        self._origins: LedgerDict[
            tuple[tuple[str, str], TypedPayloadKey], SourceImageID
        ] = self.ledger.make_dict(self._origin_owner)
        self._applications: LedgerDict[SourceImageApplyKey, SourceImageID] = (
            self.ledger.make_dict(self._apply_owner)
        )
        self._relative: LedgerDict[
            SourceImageRelativeKey, SourceImageRelativeApplication
        ] = self.ledger.make_dict(self._relative_owner)
        self._projections: LedgerDict[
            tuple[SourceImageID, SourceImageDemand], SourceImageProjectionRecord
        ] = self.ledger.make_dict(self._projection_owner, nodes_per_entry=1)
        self._publication_seals = PublicationSeals(self.ledger, prefix)
        self.ledger.register_execution_root(self)

    @staticmethod
    def _adapter_key(adapter: SourceBoundImageAdapter) -> tuple[str, str]:
        if type(adapter.family) is not str or not adapter.family:
            raise ValueError("source image adapter family must be nonempty")
        if type(adapter.semantic_version) is not str or not adapter.semantic_version:
            raise ValueError("source image adapter version must be nonempty")
        return adapter.family, adapter.semantic_version

    def register(self, adapter: SourceBoundImageAdapter) -> None:
        if self._closed:
            raise ValueError("disposed source image scheduler")
        if adapter.ledger is not self.ledger:
            raise ValueError("source image adapter belongs to another ledger")
        key = self._adapter_key(adapter)
        found = self._adapters.get(key)
        if found is adapter:
            return
        if found is not None:
            raise ValueError("source image semantic domain already has another owner")
        if not source_bound_adapter_shape(adapter, self.ledger):
            raise TypeError("source image adapter has an incomplete family contract")
        self.ledger.reserve(self._adapter_owner, entries=1)
        try:
            self._adapters[key] = adapter
        except BaseException:
            self.ledger.release(self._adapter_owner, entries=1)
            raise
        self.ledger.bump(_execution_keys.SOURCE_IMAGE_ADAPTER_REGISTRATIONS)

    def registered_adapter_key(
        self, adapter: SourceBoundImageAdapter
    ) -> tuple[str, str]:
        if self._closed:
            raise ValueError("disposed source image scheduler")
        key = self._adapter_key(adapter)
        if self._adapters.get(key) is not adapter:
            raise ValueError("source image adapter is foreign or unregistered")
        if adapter.ledger is not self.ledger:
            raise ValueError("source image adapter belongs to another ledger")
        return key

    @property
    def application_workspace(self) -> SourceImageWorkspace:
        return self._workspace

    @property
    def application_workspace_owner(self) -> int:
        return self._workspace_owner

    @property
    def application_results(self) -> Mapping[SourceImageApplyKey, SourceImageID]:
        return MappingProxyType(self._applications)

    @property
    def relative_applications(
        self,
    ) -> Mapping[SourceImageRelativeKey, SourceImageRelativeApplication]:
        return MappingProxyType(self._relative)

    def audit_snapshot(
        self,
    ) -> SourceBoundSchedulerCoreAuditSnapshot[
        SourceImageRecord, SourceBoundImageAdapter
    ]:
        """Expose retained source state through non-creating read-only views."""
        base = super().audit_snapshot()
        return SourceBoundSchedulerCoreAuditSnapshot(
            ledger=base.ledger,
            owner=base.owner,
            kind=base.kind,
            closed=base.closed,
            nodes=base.nodes,
            node_store=base.node_store,
            adapters=base.adapters,
            adapter_store=base.adapter_store,
            origins=MappingProxyType(self._origins.backing_store),
            origin_store=self._origins,
            applications=MappingProxyType(self._applications.backing_store),
            application_store=self._applications,
            relative=MappingProxyType(self._relative.backing_store),
            relative_store=self._relative,
            projections=MappingProxyType(self._projections.backing_store),
            projection_store=self._projections,
            image_seals=SourceImageNodeView(self._publication_seals.images),
            image_seal_store=self._publication_seals.images,
            projection_seals=MappingProxyType(
                self._publication_seals.projections.backing_store
            ),
            projection_seal_store=self._publication_seals.projections,
            node_owner=self._node_owner,
            adapter_owner=self._adapter_owner,
            origin_owner=self._origin_owner,
            application_owner=self._apply_owner,
            relative_owner=self._relative_owner,
            projection_owner=self._projection_owner,
            image_seal_owner=self._publication_seals.images.owner,
            projection_seal_owner=self._publication_seals.projections.owner,
            workspace=self._workspace.audit_snapshot(),
        )

    def clear(self) -> None:
        """Drop query images and invalidate every previously issued image ID."""
        if self._closed:
            raise ValueError("disposed source image scheduler")
        if self._workspace.running or len(self._workspace):
            raise RuntimeError(
                "cannot clear source images during an active application"
            )
        projections = len(self._projections)
        applications = len(self._applications)
        relative = len(self._relative)
        origins = len(self._origins)
        nodes = len(self._nodes)
        self._projections.clear()
        self._applications.clear()
        self._relative.clear()
        self._origins.clear()
        self._nodes.clear()
        self._publication_seals.clear()
        self.ledger.release(
            self._projection_owner, entries=projections, nodes=projections
        )
        self.ledger.release(self._apply_owner, entries=applications)
        self.ledger.release(self._relative_owner, entries=relative)
        self.ledger.release(self._origin_owner, entries=origins)
        self.ledger.release(self._node_owner, entries=nodes, nodes=nodes)
        self.owner = ArenaToken("tile-source-images-cleared")
        self.ledger.bump(_execution_keys.SOURCE_IMAGE_CACHE_CLEARS)

    def dispose(self) -> None:
        """Release all retained authority; the core cannot be reused."""
        if self._closed:
            return
        self.clear()
        adapters = len(self._adapters)
        self._adapters.clear()
        self.ledger.release(self._adapter_owner, entries=adapters)
        self._closed = True
        self.ledger.bump(_execution_keys.SOURCE_IMAGE_SCHEDULER_DISPOSALS)

    def validate_key(self, value: object, label: str) -> None:
        work = require_immutable_key(value, label)
        self.ledger.bump(_execution_keys.SOURCE_IMAGE_KEY_VALIDATION_WORK, work)

    def _issued_record(self, image: SourceImageID) -> SourceImageRecord:
        if type(image) is not SourceImageID:
            raise TypeError("expected a source-bound image ID")
        image.validate(self.owner, self._KIND, size=len(self._nodes))
        return self._nodes[image.local_id]

    def resolve(self, image: SourceImageID) -> SourceImageRecord:
        record = self._issued_record(image)
        if (
            type(record) is not SourceImageRecord
            or record.publication_owner is not _IMAGE_RECORD_SEAL
            or record.publication_snapshot
            is not self._publication_seals.images[image.local_id]
            or not publication_matches(
                (
                    record.binding,
                    record.payload,
                    record.failure_prefix,
                    record.publication_provenance,
                    id(record.adapter),
                    record.binding_audit_required,
                ),
                record.publication_snapshot,
                self.ledger,
            )
        ):
            raise ValueError("source image publication record was altered")
        if self._adapters.get(
            record.adapter_key
        ) is not record.adapter or record.binding_audit_required is not callable(
            getattr(record.adapter, "audit_image_binding", None)
        ):
            raise ValueError("source image lost its semantic adapter")
        if (
            record.binding.family,
            record.binding.semantic_version,
        ) != record.adapter_key:
            raise ValueError("source image binding has another semantic adapter")
        return record

    def resolve_readonly(self, image: SourceImageID) -> SourceImageRecord:
        """Authenticate a retained image without charging runtime seal work."""
        record = self._issued_record(image)
        if (
            type(record) is not SourceImageRecord
            or record.publication_owner is not _IMAGE_RECORD_SEAL
            or record.publication_snapshot
            is not self._publication_seals.images[image.local_id]
            or not publication_matches_readonly(
                (
                    record.binding,
                    record.payload,
                    record.failure_prefix,
                    record.publication_provenance,
                    id(record.adapter),
                    record.binding_audit_required,
                ),
                record.publication_snapshot,
            )
        ):
            raise ValueError("source image publication record was altered")
        if self._adapters.get(record.adapter_key) is not record.adapter:
            raise ValueError("source image lost its semantic adapter")
        if record.binding_audit_required is not callable(
            getattr(record.adapter, "audit_image_binding", None)
        ):
            raise ValueError("source image lost its semantic adapter")
        if (
            record.binding.family,
            record.binding.semantic_version,
        ) != record.adapter_key:
            raise ValueError("source image binding has another semantic adapter")
        return record

    def resolve_projection_readonly(
        self, key: object, candidate: object
    ) -> SourceImageProjectionRecord:
        """Authenticate a retained projection without charging seal work."""
        if (
            not is_exact_object_tuple(key)
            or len(key) != 2
            or type(candidate) is not SourceImageProjectionRecord
            or key[0] is not candidate.image
            or key[1] is not candidate.demand
            or candidate.publication_owner is not _IMAGE_RECORD_SEAL
            or candidate.publication_snapshot
            is not self._publication_seals.projections.get(
                (candidate.image, candidate.demand)
            )
            or not publication_matches_readonly(
                (candidate.image, candidate.demand, candidate.projection),
                candidate.publication_snapshot,
            )
        ):
            raise ValueError("source projection publication was altered")
        self.resolve_readonly(candidate.image)
        return candidate

    def view(self, image: SourceImageID) -> SourceImageView:
        record = self.resolve(image)
        return self._view_record(image, record)

    def view_for_adapter(
        self, adapter: SourceBoundImageAdapter, image: SourceImageID
    ) -> SourceImageView:
        """Return an issued image view only through its registered adapter."""
        if adapter.ledger is not self.ledger:
            raise ValueError("source image adapter belongs to another ledger")
        record = self.resolve(image)
        if (
            record.adapter_key != self._adapter_key(adapter)
            or record.adapter is not adapter
            or self._adapters.get(record.adapter_key) is not adapter
        ):
            raise ValueError("source image was not issued for this adapter")
        return self._view_record(image, record)

    def _view_record(
        self, image: SourceImageID, record: SourceImageRecord
    ) -> SourceImageView:
        adapter = self._adapters[record.adapter_key]
        adapter.validate_source(record.binding.source)
        adapter.validate_action(record.binding.action)
        adapter.validate_payload(record.payload)
        return SourceImageView(
            image,
            record.binding,
            record.payload,
            record.failure_prefix,
        )

    def _publish(
        self,
        adapter_key: tuple[str, str],
        source: Hashable,
        cumulative_action: Hashable,
        candidate: SourceImageCandidate,
        publication_provenance: tuple[str, object, object | None],
        *,
        reserved: bool = False,
    ) -> SourceImageID:
        if type(candidate) is not SourceImageCandidate:
            raise TypeError("source image adapter returned another candidate sort")
        candidate.__post_init__()
        adapter = self._adapters[adapter_key]
        adapter.validate_source(source)
        adapter.validate_action(cumulative_action)
        adapter.validate_payload(candidate.payload)
        binding = SourceImageBinding(
            adapter_key[0],
            adapter_key[1],
            source,
            cumulative_action,
            candidate.extent,
            candidate.boundary_ports,
            candidate.orientation,
            candidate.radix,
            candidate.precision,
        )
        snapshot = publication_seal(
            (
                binding,
                candidate.payload,
                candidate.failure_prefix,
                publication_provenance,
                id(adapter),
                callable(getattr(adapter, "audit_image_binding", None)),
            ),
            self.ledger,
        )
        record = SourceImageRecord(
            adapter_key,
            adapter,
            callable(getattr(adapter, "audit_image_binding", None)),
            binding,
            candidate.payload,
            candidate.failure_prefix,
            _IMAGE_RECORD_SEAL,
            snapshot,
            publication_provenance,
        )
        if not reserved:
            self.ledger.reserve(self._node_owner, entries=1, nodes=1)
        local_id = len(self._nodes)
        try:
            self._nodes.append(record)
            self._publication_seals.append_image(snapshot)
        except BaseException:
            if len(self._publication_seals.images) > local_id:
                self._publication_seals.pop_image()
            if len(self._nodes) > local_id:
                self._nodes.pop()
            if not reserved:
                self.ledger.release(self._node_owner, entries=1, nodes=1)
            raise
        self.ledger.bump(_execution_keys.SOURCE_IMAGE_PUBLICATIONS)
        return SourceImageID(self.owner, self._KIND, local_id)

    def origin(
        self, adapter: SourceBoundImageAdapter, source: Hashable
    ) -> SourceImageID:
        key = self.registered_adapter_key(adapter)
        self.validate_key(source, "source image source")
        adapter.validate_source(source)
        origin_key = key, TypedPayloadKey(source)
        found = self._origins.get(origin_key)
        if found is not None:
            found_view = self.view(found)
            if not typed_payload_equal(
                found_view.binding.source, source
            ) or not typed_payload_equal(
                found_view.binding.action, adapter.identity_action(source)
            ):
                raise ValueError("source image origin binding was altered")
            self.ledger.bump(_execution_keys.SOURCE_IMAGE_ORIGIN_HITS)
            return found
        identity = adapter.identity_action(source)
        adapter.validate_action(identity)
        candidate = adapter.admit_source(source)
        candidate.__post_init__()
        self.ledger.reserve_many(((self._node_owner, 1, 1), (self._origin_owner, 1, 0)))
        image: SourceImageID | None = None
        try:
            image = self._publish(
                key,
                source,
                identity,
                candidate,
                ("origin", (key, source), None),
                reserved=True,
            )
            self._origins[origin_key] = image
        except BaseException:
            self._origins.pop(origin_key, None)
            if image is not None and image.local_id == len(self._nodes) - 1:
                self._nodes.pop()
                self._publication_seals.pop_image()
            self.ledger.release(self._node_owner, entries=1, nodes=1)
            self.ledger.release(self._origin_owner, entries=1)
            raise
        self.ledger.bump(_execution_keys.SOURCE_IMAGE_ORIGIN_PUBLICATIONS)
        return image

    def apply(
        self,
        adapter: SourceBoundImageAdapter,
        source: Hashable,
        action: Hashable,
    ) -> SourceImageID:
        """Apply one action with an explicit chronological postorder stack."""
        return self._apply(adapter, source, action, demand=None)

    def apply_demanded(
        self,
        adapter: SourceBoundImageAdapter,
        source: Hashable,
        action: Hashable,
        demand: SourceImageDemand,
    ) -> SourceImageID:
        """Apply a complete image, letting the demand choose its construction route."""
        if type(demand) is not SourceImageDemand:
            raise TypeError(
                "source image demanded application requires an exact demand"
            )
        demand.__post_init__()
        return self._apply(adapter, source, action, demand=demand)

    def _apply(
        self,
        adapter: SourceBoundImageAdapter,
        source: Hashable,
        action: Hashable,
        *,
        demand: SourceImageDemand | None,
    ) -> SourceImageID:
        from number_compiler.hashlife.execution.source_image_application import (
            apply_source_image,
        )

        return apply_source_image(self, adapter, source, action, demand=demand)

    def publish_application_result(
        self,
        key: SourceImageApplyKey,
        source: Hashable,
        cumulative_action: Hashable,
        candidate: SourceImageCandidate,
        *,
        relative_key: SourceImageRelativeKey | None,
    ) -> SourceImageID:
        if key in self._applications:
            raise ValueError("source image application was concurrently published")
        candidate.__post_init__()
        source_failure = self.view(key.source).failure_prefix
        if source_failure is not None and candidate.failure_prefix != source_failure:
            raise ValueError("source image application discarded its first failure")
        publish_relative = (
            relative_key is not None and relative_key not in self._relative
        )
        reservations = [
            (self._node_owner, 1, 1),
            (self._apply_owner, 1, 0),
        ]
        if publish_relative:
            reservations.append((self._relative_owner, 1, 0))
        self.ledger.reserve_many(reservations)
        image: SourceImageID | None = None
        try:
            image = self._publish(
                key.adapter_key,
                source,
                cumulative_action,
                candidate,
                ("application", key, relative_key if publish_relative else None),
                reserved=True,
            )
            self._applications[key] = image
            if publish_relative:
                assert relative_key is not None
                self._relative[relative_key] = SourceImageRelativeApplication(
                    key.source, image
                )
        except BaseException:
            self._applications.pop(key, None)
            if image is not None and image.local_id == len(self._nodes) - 1:
                self._nodes.pop()
                self._publication_seals.pop_image()
            self.ledger.release(self._node_owner, entries=1, nodes=1)
            self.ledger.release(self._apply_owner, entries=1)
            if publish_relative:
                assert relative_key is not None
                self._relative.pop(relative_key, None)
                self.ledger.release(self._relative_owner, entries=1)
            raise
        if publish_relative:
            self.ledger.bump(
                _execution_keys.SOURCE_IMAGE_RELATIVE_TRANSFER_PUBLICATIONS
            )
        self.ledger.bump(_execution_keys.SOURCE_IMAGE_APPLICATION_PUBLICATIONS)
        return image

    def validate_application_binding(
        self,
        adapter: SourceBoundImageAdapter,
        key: SourceImageApplyKey,
        image: SourceImageID,
    ) -> None:
        source = self.view(key.source)
        result = self.view(image)
        expected = adapter.compose_actions(source.binding.action, key.action)
        if (
            result.binding.family != key.adapter_key[0]
            or result.binding.semantic_version != key.adapter_key[1]
            or not typed_payload_equal(result.binding.source, source.binding.source)
            or not typed_payload_equal(result.binding.action, expected)
        ):
            raise ValueError("source image application binding was altered")

    def cached_projection(
        self,
        adapter: SourceBoundImageAdapter,
        image: SourceImageID,
        demand: SourceImageDemand,
    ) -> SourceImageProjection | None:
        """Authenticate a retained projection without constructing on a miss."""
        adapter_key = self.registered_adapter_key(adapter)
        record = self.resolve(image)
        if record.adapter_key != adapter_key:
            raise ValueError("source image belongs to another family adapter")
        if type(demand) is not SourceImageDemand:
            raise TypeError("source image projection requires an exact demand")
        demand.__post_init__()
        self.ledger.bump(_execution_keys.SOURCE_IMAGE_PROJECTION_REQUESTS)
        key = image, demand
        found = self._projections.get(key)
        if found is not None:
            if (
                type(found) is not SourceImageProjectionRecord
                or found.publication_owner is not _IMAGE_RECORD_SEAL
                or found.image != image
                or found.demand != demand
                or found.publication_snapshot
                is not self._publication_seals.projections.get(key)
                or not publication_matches(
                    (found.image, found.demand, found.projection),
                    found.publication_snapshot,
                    self.ledger,
                )
            ):
                raise ValueError("source image projection record was altered")
            # A seal authenticates the published record, but the adapter may
            # revoke a backing source, action, or payload arena after the
            # projection was cached. Apply the same authority checks as a
            # cold demand before reporting a usable hit.
            self._view_record(image, record)
            found.projection.__post_init__()
            self.ledger.bump(_execution_keys.SOURCE_IMAGE_PROJECTION_HITS)
            return found.projection
        return None

    def projection(
        self,
        adapter: SourceBoundImageAdapter,
        image: SourceImageID,
        demand: SourceImageDemand,
    ) -> SourceImageProjection:
        found = self.cached_projection(adapter, image, demand)
        if found is not None:
            return found
        record = self.resolve(image)
        key = image, demand
        self.ledger.bump(_execution_keys.SOURCE_IMAGE_PROJECTION_MISSES)
        projected = adapter.project(self._view_record(image, record), demand)
        if type(projected) is not SourceImageProjection:
            raise TypeError("source image adapter returned another projection sort")
        projected.__post_init__()
        snapshot = publication_seal((image, demand, projected), self.ledger)
        self.ledger.reserve(self._projection_owner, entries=1, nodes=1)
        try:
            self._publication_seals.put_projection(key, snapshot)
            self._projections[key] = SourceImageProjectionRecord(
                image,
                demand,
                projected,
                _IMAGE_RECORD_SEAL,
                snapshot,
            )
        except BaseException:
            self._projections.pop(key, None)
            if key in self._publication_seals.projections:
                self._publication_seals.drop_projection(key)
            self.ledger.release(self._projection_owner, entries=1, nodes=1)
            raise
        self.ledger.bump(_execution_keys.SOURCE_IMAGE_PROJECTION_PUBLICATIONS)
        return projected

    def first_failure(
        self,
        adapter: SourceBoundImageAdapter,
        image: SourceImageID,
    ) -> Hashable | None:
        adapter_key = self.registered_adapter_key(adapter)
        view = self.view(image)
        if self.resolve(image).adapter_key != adapter_key:
            raise ValueError("source image belongs to another family adapter")
        failure = adapter.first_failure(view)
        if view.failure_prefix is None and failure is not None:
            raise ValueError("adapter fabricated failure outside the image ledger")
        if view.failure_prefix is not None and failure is None:
            raise ValueError("adapter failed to descend its recorded failure")
        if failure is not None:
            if not isinstance(failure, Hashable):
                raise TypeError("source image failure witness must be immutable")
        self.ledger.bump(_execution_keys.SOURCE_IMAGE_FAILURE_DESCENTS)
        return failure
