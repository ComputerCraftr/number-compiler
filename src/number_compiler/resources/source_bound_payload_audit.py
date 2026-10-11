"""Independent retained-publication audit for source-bound scheduler cores."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass, field, fields, is_dataclass

from number_compiler.hashlife.execution.source_bound_images import (
    _IMAGE_RECORD_SEAL,
    SourceBoundImageBindingAuditor,
    SourceBoundSchedulerCore,
    SourceImageID,
    _ApplyKey,
    _ImageRecord,
    _ProjectionRecord,
    _RelativeApplication,
    _RelativeKey,
    source_bound_adapter_shape,
)
from number_compiler.hashlife.execution.source_image_seals import (
    _typed_equal,
    _TypedKey,
    publication_matches_readonly,
)
from number_compiler.resources.ledger import ResourceLedger


def _resolve_readonly(core: SourceBoundSchedulerCore, image: object) -> _ImageRecord:
    if type(image) is not SourceImageID:
        raise TypeError("expected an exact source image ID")
    image.validate(core.owner, core._KIND, size=len(core._nodes))
    record = core._nodes[image.local_id]
    if (
        type(record) is not _ImageRecord
        or record.publication_owner is not _IMAGE_RECORD_SEAL
        or record.publication_snapshot
        is not core._publication_seals.images[image.local_id]
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
        or core._adapters.get(record.adapter_key) is not record.adapter
        or not source_bound_adapter_shape(record.adapter, core.ledger)
        or record.binding_audit_required
        is not callable(getattr(record.adapter, "audit_image_binding", None))
        or (record.binding.family, record.binding.semantic_version)
        != record.adapter_key
    ):
        raise ValueError("source image publication record was altered")
    return record


def _provenance(
    record: _ImageRecord, kind: str, primary: object
) -> tuple[str, object, object | None]:
    provenance = record.publication_provenance
    if (
        type(provenance) is not tuple
        or len(provenance) != 3
        or provenance[0] != kind
        or provenance[1] is not primary
    ):
        raise ValueError("source image has another publication provenance")
    return provenance


def _sealed_members(root: object) -> dict[int, object]:
    """Index immutable descendants of a sealed boundary value."""
    members: dict[int, object] = {}
    pending = [root]
    while pending:
        value = pending.pop()
        identity = id(value)
        if identity in members:
            continue
        members[identity] = value
        if type(value) is tuple:
            pending.extend(value)
        elif is_dataclass(value):
            params: object | None = getattr(type(value), "__dataclass_params__", None)
            if params is None or not getattr(params, "frozen", False):
                raise TypeError("sealed source image contains a mutable record")
            pending.extend(getattr(value, item.name) for item in fields(value))
    return members


def _direct_frozen_payload_members(payload: object) -> dict[int, object]:
    """Index only direct frozen-record fields approved by a family adapter."""
    if not is_dataclass(payload) or isinstance(payload, type):
        return {}
    members: dict[int, object] = {}
    for item in fields(payload):
        value = getattr(payload, item.name)
        if _is_frozen_record(value):
            members[id(value)] = value
    return members


@dataclass(frozen=True, slots=True)
class SourceBoundPayloadAudit:
    cores: tuple[SourceBoundSchedulerCore, ...]
    approved: frozenset[int]
    recognized: frozenset[int]
    invalid: frozenset[tuple[int, int]]
    payload_members_by_owner: frozenset[tuple[int, int]] = frozenset()
    _invalid_ids: frozenset[int] = field(init=False, repr=False, compare=False)

    def __post_init__(self) -> None:
        object.__setattr__(
            self,
            "_invalid_ids",
            frozenset(identity for _, identity in self.invalid),
        )

    def recognizes(self, value: object) -> bool:
        return type(value) is SourceImageID or id(value) in self.recognized

    def valid(self, value: object) -> bool:
        if type(value) is SourceImageID:
            for core in self.cores:
                try:
                    record = _resolve_readonly(core, value)
                except (TypeError, ValueError, IndexError, AttributeError):
                    continue
                return (
                    id(record) in self.approved and id(record) not in self._invalid_ids
                )
            return False
        return id(value) in self.approved and id(value) not in self._invalid_ids

    def owns_payload_member(self, owner: int, value: object) -> bool:
        """Whether a validated adapter sealed this exact direct payload member.

        This is intentionally owner-qualified and identity-based. The approved
        value is a direct frozen field of a source-image payload whose enclosing
        publication seal was checked while constructing this audit snapshot.
        It is not a type-wide exemption for records of the same class.
        """
        return (owner, id(value)) in self.payload_members_by_owner


def audit_source_bound_payloads(
    ledger: ResourceLedger,
    roots: tuple[object, ...],
    containers: Mapping[int, object],
) -> SourceBoundPayloadAudit:
    """Validate publication provenance and optional pure family binding hooks."""
    cores = tuple(
        root
        for root in roots
        if type(root) is SourceBoundSchedulerCore
        and root.ledger is ledger
        and not root._closed
    )
    approved: set[int] = set()
    recognized: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    valid_adapter_ids: set[int] = set()
    payload_members_by_owner: set[tuple[int, int]] = set()
    for core in cores:
        stores = (
            (core._adapter_owner, core._adapters),
            (core._node_owner, core._nodes),
            (core._origin_owner, core._origins),
            (core._apply_owner, core._applications),
            (core._relative_owner, core._relative),
            (core._projection_owner, core._projections),
            (core._workspace_owner, core._workspace._storage),
            (core._publication_seals._image_owner, core._publication_seals.images),
            (
                core._publication_seals._projection_owner,
                core._publication_seals.projections,
            ),
        )
        if any(containers.get(owner) is not store for owner, store in stores):
            invalid.add((core._node_owner, id(core)))
            continue
        for adapter_key, adapter in core._adapters.items():
            recognized.update((id(adapter_key), id(adapter)))
            try:
                valid_adapter = (
                    type(adapter_key) is tuple
                    and type(adapter.family) is str
                    and type(adapter.semantic_version) is str
                    and adapter_key == (adapter.family, adapter.semantic_version)
                    and source_bound_adapter_shape(adapter, ledger)
                )
            except (AttributeError, TypeError, ValueError, RuntimeError):
                valid_adapter = False
            if not valid_adapter:
                invalid.add((core._adapter_owner, id(adapter_key)))
            else:
                valid_adapter_ids.add(id(adapter))
                approved.update((id(adapter_key), id(adapter)))
        valid_nodes: dict[int, _ImageRecord] = {}
        linked_nodes: set[int] = set()
        for local_id, record in enumerate(core._nodes):
            recognized.add(id(record))
            family_approved_objects: tuple[object, ...] = ()
            family_approved_payload_objects: tuple[object, ...] = ()
            try:
                image = SourceImageID(core.owner, core._KIND, local_id)
                resolved = _resolve_readonly(core, image)
                if resolved is not record:
                    raise ValueError("source image resolution changed its record")
                record_adapter = core._adapters.get(record.adapter_key)
                if (
                    record_adapter is not record.adapter
                    or id(record_adapter) not in valid_adapter_ids
                    or record.binding_audit_required
                    is not callable(
                        getattr(record_adapter, "audit_image_binding", None)
                    )
                ):
                    raise ValueError("image record lost its exact registered adapter")
                if record.binding_audit_required:
                    if not isinstance(record_adapter, SourceBoundImageBindingAuditor):
                        raise TypeError("source adapter audit hook is not callable")
                    family_approved = record_adapter.audit_image_binding(
                        record.binding,
                        record.payload,
                        record.failure_prefix,
                    )
                    if family_approved is not None:
                        if type(family_approved) is not tuple:
                            raise TypeError(
                                "image binding audit returned untyped member approvals"
                            )
                        boundary_members = _sealed_members(
                            record.binding.boundary_ports
                        )
                        payload_members = _direct_frozen_payload_members(record.payload)
                        if len({id(value) for value in family_approved}) != len(
                            family_approved
                        ):
                            raise ValueError(
                                "image binding audit repeated a boundary object"
                            )
                        port_approved: list[object] = []
                        payload_approved: list[object] = []
                        for value in family_approved:
                            if (
                                id(value) in boundary_members
                                and boundary_members[id(value)] is value
                            ):
                                port_approved.append(value)
                            elif (
                                id(value) in payload_members
                                and payload_members[id(value)] is value
                                and _is_frozen_record(value)
                            ):
                                payload_approved.append(value)
                            else:
                                raise ValueError(
                                    "image binding audit approved an unowned object"
                                )
                        family_approved_objects = tuple(port_approved)
                        family_approved_payload_objects = tuple(payload_approved)
            except (
                TypeError,
                ValueError,
                IndexError,
                KeyError,
                AttributeError,
                RuntimeError,
            ):
                invalid.add((core._node_owner, id(record)))
            else:
                valid_nodes[local_id] = record
                values = (
                    record,
                    record.binding,
                    record.payload,
                    record.publication_snapshot,
                    record.publication_provenance,
                    image,
                )
                approved.update(map(id, values))
                recognized.update(map(id, values))
                approved.update(map(id, family_approved_objects))
                recognized.update(map(id, family_approved_objects))
                payload_members_by_owner.update(
                    (core._node_owner, id(value))
                    for value in family_approved_payload_objects
                )
        for origin_key, image in core._origins.items():
            recognized.update((id(origin_key), id(image)))
            try:
                if type(origin_key) is not tuple or len(origin_key) != 2:
                    raise TypeError("source origin contains another key sort")
                adapter_key, typed_source = origin_key
                if type(typed_source) is not _TypedKey:
                    raise TypeError("source origin lost its typed key")
                source = typed_source.value
                record = _resolve_readonly(core, image)
                provenance = record.publication_provenance
                if (
                    type(provenance) is not tuple
                    or len(provenance) != 3
                    or provenance[0] != "origin"
                    or type(provenance[1]) is not tuple
                    or len(provenance[1]) != 2
                    or provenance[1][0] != adapter_key
                    or provenance[1][1] is not source
                ):
                    raise ValueError("source image has another origin provenance")
                if (
                    provenance[2] is not None
                    or record.adapter_key != adapter_key
                    or record.binding.source is not source
                    or _TypedKey(record.binding.source) != typed_source
                ):
                    raise ValueError("source image origin binding was altered")
            except (TypeError, ValueError, KeyError, IndexError, AttributeError):
                invalid.add((core._origin_owner, id(origin_key)))
            else:
                linked_nodes.add(image.local_id)
                approved.update((id(origin_key), id(image)))
        for apply_key, image in core._applications.items():
            recognized.update((id(apply_key), id(image)))
            try:
                if type(apply_key) is not _ApplyKey:
                    raise TypeError("source application contains another key sort")
                source = _resolve_readonly(core, apply_key.source)
                result = _resolve_readonly(core, image)
                provenance = _provenance(result, "application", apply_key)
                if (
                    result.adapter_key != apply_key.adapter_key
                    or source.adapter_key != apply_key.adapter_key
                    or not _typed_equal(result.binding.source, source.binding.source)
                ):
                    raise ValueError("source image application binding was altered")
                relative_key = provenance[2]
                if relative_key is not None:
                    if type(relative_key) is not _RelativeKey:
                        raise TypeError("application has another relative key sort")
                    relative = core._relative.get(relative_key)
                    if (
                        type(relative) is not _RelativeApplication
                        or relative.source is not apply_key.source
                        or relative.result is not image
                    ):
                        raise ValueError("application lost its relative publication")
            except (TypeError, ValueError, KeyError, IndexError, AttributeError):
                invalid.add((core._apply_owner, id(apply_key)))
            else:
                linked_nodes.add(image.local_id)
                approved.update((id(apply_key), id(image)))
        for relative_key, application in core._relative.items():
            recognized.update((id(relative_key), id(application)))
            try:
                if (
                    type(relative_key) is not _RelativeKey
                    or type(application) is not _RelativeApplication
                ):
                    raise TypeError("relative transfer contains another record sort")
                result = _resolve_readonly(core, application.result)
                provenance = result.publication_provenance
                if (
                    type(provenance) is not tuple
                    or len(provenance) != 3
                    or provenance[0] != "application"
                ):
                    raise ValueError("relative transfer lost its sealed application")
                relative_apply_key = provenance[1]
                if type(relative_apply_key) is not _ApplyKey:
                    raise TypeError("relative transfer has another application key")
                if (
                    relative_apply_key.adapter_key is not relative_key.adapter_key
                    or relative_apply_key.source is not application.source
                    or relative_apply_key.action is not relative_key.action
                    or core._applications.get(relative_apply_key)
                    is not application.result
                    or provenance[2] is not relative_key
                ):
                    raise ValueError("relative transfer has another publication key")
            except (TypeError, ValueError, KeyError, IndexError, AttributeError):
                invalid.add((core._relative_owner, id(relative_key)))
            else:
                approved.update((id(relative_key), id(application)))
        for local_id, record in valid_nodes.items():
            if local_id not in linked_nodes:
                invalid.add((core._node_owner, id(record)))
        for projection_key, projection_record in core._projections.items():
            recognized.update((id(projection_key), id(projection_record)))
            try:
                if (
                    type(projection_key) is not tuple
                    or len(projection_key) != 2
                    or type(projection_record) is not _ProjectionRecord
                    or projection_key[0] is not projection_record.image
                    or projection_key[1] is not projection_record.demand
                    or projection_record.publication_owner is not _IMAGE_RECORD_SEAL
                    or projection_record.publication_snapshot
                    is not core._publication_seals.projections.get(projection_key)
                    or not publication_matches_readonly(
                        (
                            projection_record.image,
                            projection_record.demand,
                            projection_record.projection,
                        ),
                        projection_record.publication_snapshot,
                    )
                ):
                    raise ValueError("source projection publication was altered")
                _resolve_readonly(core, projection_record.image)
            except (TypeError, ValueError, KeyError, IndexError, AttributeError):
                invalid.add((core._projection_owner, id(projection_key)))
            else:
                projection_values = (
                    projection_key,
                    projection_record,
                    projection_record.publication_snapshot,
                )
                approved.update(map(id, projection_values))
                recognized.update(map(id, projection_values))
        for seal in core._publication_seals.images:
            recognized.add(id(seal))
            if id(seal) not in approved:
                invalid.add((core._publication_seals._image_owner, id(seal)))
        for seal_key, seal in core._publication_seals.projections.items():
            recognized.update((id(seal_key), id(seal)))
            if id(seal) in approved:
                approved.add(id(seal_key))
            else:
                invalid.add((core._publication_seals._projection_owner, id(seal)))
    return SourceBoundPayloadAudit(
        cores,
        frozenset(approved),
        frozenset(recognized),
        frozenset(invalid),
        frozenset(payload_members_by_owner),
    )


def _is_frozen_record(value: object) -> bool:
    params: object | None = getattr(type(value), "__dataclass_params__", None)
    return params is not None and getattr(params, "frozen", False)


__all__ = ["SourceBoundPayloadAudit", "audit_source_bound_payloads"]
