"""Authenticated source-bound images owned by the canonical tile scheduler."""

from __future__ import annotations

from collections.abc import Hashable
from dataclasses import dataclass, fields, is_dataclass
from typing import Protocol

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.hashlife.execution.source_image_seals import PublicationSeal
from number_compiler.hashlife.execution.source_image_seals import PublicationSeals
from number_compiler.hashlife.execution.source_image_seals import publication_matches
from number_compiler.hashlife.execution.source_image_seals import publication_seal
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict, LedgerList

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
        _require_immutable_key(self.source, "source image source")
        _require_immutable_key(self.action, "source image action")
        if type(self.extent) is not int or self.extent < 0:
            raise ValueError("source image extent must be a nonnegative integer")
        if type(self.boundary_ports) is not tuple:
            raise TypeError("source image boundary ports must be immutable keys")
        for port in self.boundary_ports:
            _require_immutable_key(port, "source image boundary port")
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
    """Adapter-produced payload and geometry before scheduler publication."""

    payload: Hashable
    extent: int
    boundary_ports: tuple[Hashable, ...] = ()
    orientation: int = 1
    radix: int = 2
    precision: int | None = None
    failure_prefix: int | None = None

    def __post_init__(self) -> None:
        _require_immutable_key(self.payload, "source image payload")
        SourceImageBinding(
            "candidate",
            "candidate-v1",
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


@dataclass(frozen=True, slots=True)
class SourceImageDemand:
    """One immutable requested projection, distinct from an action identity."""

    name: str
    parameters: tuple[Hashable, ...] = ()

    def __post_init__(self) -> None:
        if type(self.name) is not str or not self.name:
            raise ValueError("source image demand name must be nonempty")
        if type(self.parameters) is not tuple:
            raise TypeError("source image demand parameters must be immutable")
        for value in self.parameters:
            _require_immutable_key(value, "source image demand parameter")


@dataclass(frozen=True, slots=True)
class SourceImageProjection:
    """Adapter result retained once for one exact image and demand."""

    value: Hashable

    def __post_init__(self) -> None:
        _require_immutable_key(self.value, "source image projection")


_MAX_INLINE_KEY_NODES = 64


def _require_immutable_key(value: object, label: str) -> int:
    """Accept structural immutable keys; reject user-defined mutable hashes."""
    pending: list[tuple[object, bool]] = [(value, False)]
    active: set[int] = set()
    finished: set[int] = set()
    visited = 0
    while pending:
        current, exiting = pending.pop()
        identity = id(current)
        if exiting:
            active.remove(identity)
            finished.add(identity)
            continue
        if current is None or type(current) in (bool, int, str, bytes):
            visited += 1
            if visited > _MAX_INLINE_KEY_NODES:
                raise ValueError(
                    f"{label} exceeds the inline descriptor bound; intern it in an arena"
                )
            continue
        if isinstance(current, ArenaHandle):
            current.__post_init__()
            visited += 1
            if visited > _MAX_INLINE_KEY_NODES:
                raise ValueError(
                    f"{label} exceeds the inline descriptor bound; intern it in an arena"
                )
            continue
        if identity in active:
            raise ValueError(f"{label} contains a reference cycle")
        if identity in finished:
            continue
        visited += 1
        if visited > _MAX_INLINE_KEY_NODES:
            raise ValueError(
                f"{label} exceeds the inline descriptor bound; intern it in an arena"
            )
        active.add(identity)
        pending.append((current, True))
        if type(current) is tuple:
            pending.extend((item, False) for item in current)
            continue
        if type(current) is frozenset:
            pending.extend((item, False) for item in current)
            continue
        if is_dataclass(current) and not isinstance(current, type):
            parameters = getattr(type(current), "__dataclass_params__", None)
            if parameters is None or not parameters.frozen:
                raise TypeError(f"{label} must be structurally immutable")
            pending.extend(
                (getattr(current, item.name), False) for item in fields(current)
            )
            continue
        raise TypeError(f"{label} must be a structural immutable key")
    return visited


@dataclass(frozen=True, slots=True)
class SourceImageView:
    """Read-only authenticated image supplied to a family adapter."""

    identity: SourceImageID
    binding: SourceImageBinding
    payload: Hashable
    failure_prefix: int | None


class SourceBoundImageAdapter(Protocol):
    """Family laws consumed by the scheduler's common chronological driver."""

    ledger: ResourceLedger
    family: str
    semantic_version: str

    def validate_source(self, source: Hashable) -> None: ...

    def validate_action(self, action: Hashable) -> None: ...

    def validate_payload(self, payload: Hashable) -> None: ...

    def identity_action(self, source: Hashable) -> Hashable: ...

    def action_children(
        self, action: Hashable
    ) -> tuple[Hashable, Hashable] | None: ...

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

    def first_failure(self, image: SourceImageView) -> Hashable | None: ...


@dataclass(frozen=True, slots=True)
class _ImageRecord:
    adapter_key: tuple[str, str]
    binding: SourceImageBinding
    payload: Hashable
    failure_prefix: int | None
    publication_owner: object
    publication_snapshot: PublicationSeal


_IMAGE_RECORD_SEAL = object()


@dataclass(frozen=True, slots=True)
class _ProjectionRecord:
    image: SourceImageID
    demand: SourceImageDemand
    projection: SourceImageProjection
    publication_owner: object
    publication_snapshot: PublicationSeal


@dataclass(frozen=True, slots=True)
class _ApplyKey:
    adapter_key: tuple[str, str]
    source: SourceImageID
    action: Hashable


@dataclass(frozen=True, slots=True)
class _RelativeKey:
    adapter_key: tuple[str, str]
    action: Hashable
    admitted_input: Hashable


@dataclass(frozen=True, slots=True)
class _RelativeApplication:
    source: SourceImageID
    result: SourceImageID


@dataclass(slots=True)
class _ApplyFrame:
    source: SourceImageID
    action: Hashable
    stage: int = 0
    children: tuple[Hashable, Hashable] | None = None
    before: SourceImageID | None = None
    relative_key: _RelativeKey | None = None


class SourceBoundSchedulerCore:
    """Lightweight ledger-owned image scheduler shared by every family.

    It has no tile, sequence, or observer dependency.  ``TileScheduler`` owns
    one instance, while descriptor-only families may use this same canonical
    driver without allocating physical tile geometry.
    """

    _KIND = "source-bound-image"

    def __init__(self, ledger: ResourceLedger) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("source image authority requires a resource ledger")
        self.ledger = ledger
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
        self._adapters: LedgerDict[
            tuple[str, str], SourceBoundImageAdapter
        ] = self.ledger.make_dict(self._adapter_owner)
        self._nodes: LedgerList[_ImageRecord] = self.ledger.make_list(
            self._node_owner, append_only=False
        )
        self._origins: LedgerDict[
            tuple[tuple[str, str], Hashable], SourceImageID
        ] = self.ledger.make_dict(self._origin_owner)
        self._applications: LedgerDict[_ApplyKey, SourceImageID] = (
            self.ledger.make_dict(self._apply_owner)
        )
        self._relative: LedgerDict[_RelativeKey, _RelativeApplication] = (
            self.ledger.make_dict(self._relative_owner)
        )
        self._projections: LedgerDict[
            tuple[SourceImageID, SourceImageDemand], _ProjectionRecord
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
        methods = (
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
        if any(not callable(getattr(adapter, name, None)) for name in methods):
            raise TypeError("source image adapter has an incomplete family contract")
        self.ledger.reserve(self._adapter_owner, entries=1)
        try:
            self._adapters[key] = adapter
        except BaseException:
            self.ledger.release(self._adapter_owner, entries=1)
            raise
        self.ledger.bump("source_image_adapter_registrations")

    def _registered(self, adapter: SourceBoundImageAdapter) -> tuple[str, str]:
        if self._closed:
            raise ValueError("disposed source image scheduler")
        key = self._adapter_key(adapter)
        if self._adapters.get(key) is not adapter:
            raise ValueError("source image adapter is foreign or unregistered")
        if adapter.ledger is not self.ledger:
            raise ValueError("source image adapter belongs to another ledger")
        return key

    def clear(self) -> None:
        """Drop query images and invalidate every previously issued image ID."""
        if self._closed:
            raise ValueError("disposed source image scheduler")
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
        self.ledger.bump("source_image_cache_clears")

    def dispose(self) -> None:
        """Release all retained authority; the core cannot be reused."""
        if self._closed:
            return
        self.clear()
        adapters = len(self._adapters)
        self._adapters.clear()
        self.ledger.release(self._adapter_owner, entries=adapters)
        self._closed = True
        self.ledger.bump("source_image_scheduler_disposals")

    def _validate_key(self, value: object, label: str) -> None:
        work = _require_immutable_key(value, label)
        self.ledger.bump("source_image_key_validation_work", work)

    def resolve(self, image: SourceImageID) -> _ImageRecord:
        if type(image) is not SourceImageID:
            raise TypeError("expected a source-bound image ID")
        image.validate(self.owner, self._KIND, size=len(self._nodes))
        record = self._nodes[image.local_id]
        if (
            type(record) is not _ImageRecord
            or record.publication_owner is not _IMAGE_RECORD_SEAL
            or record.publication_snapshot
            is not self._publication_seals.images[image.local_id]
            or not publication_matches(
                (record.binding, record.payload, record.failure_prefix),
                record.publication_snapshot,
                self.ledger,
            )
        ):
            raise ValueError("source image publication record was altered")
        if self._adapters.get(record.adapter_key) is None:
            raise ValueError("source image lost its semantic adapter")
        if (
            record.binding.family,
            record.binding.semantic_version,
        ) != record.adapter_key:
            raise ValueError("source image binding has another semantic adapter")
        return record

    def view(self, image: SourceImageID) -> SourceImageView:
        record = self.resolve(image)
        return self._view_record(image, record)

    def _view_record(self, image: SourceImageID, record: _ImageRecord) -> SourceImageView:
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
            (binding, candidate.payload, candidate.failure_prefix), self.ledger
        )
        record = _ImageRecord(
            adapter_key,
            binding,
            candidate.payload,
            candidate.failure_prefix,
            _IMAGE_RECORD_SEAL,
            snapshot,
        )
        if not reserved:
            self.ledger.reserve(self._node_owner, entries=1, nodes=1)
        try:
            local_id = len(self._nodes)
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
        self.ledger.bump("source_image_publications")
        return SourceImageID(self.owner, self._KIND, local_id)

    def _origin(
        self, adapter: SourceBoundImageAdapter, source: Hashable
    ) -> SourceImageID:
        key = self._registered(adapter)
        self._validate_key(source, "source image source")
        adapter.validate_source(source)
        origin_key = key, source
        found = self._origins.get(origin_key)
        if found is not None:
            found_view = self.view(found)
            if (
                found_view.binding.source != source
                or found_view.binding.action != adapter.identity_action(source)
            ):
                raise ValueError("source image origin binding was altered")
            self.ledger.bump("source_image_origin_hits")
            return found
        identity = adapter.identity_action(source)
        adapter.validate_action(identity)
        candidate = adapter.admit_source(source)
        candidate.__post_init__()
        self.ledger.reserve_many(
            ((self._node_owner, 1, 1), (self._origin_owner, 1, 0))
        )
        image: SourceImageID | None = None
        try:
            image = self._publish(key, source, identity, candidate, reserved=True)
            self._origins[origin_key] = image
        except BaseException:
            self._origins.pop(origin_key, None)
            if image is not None and image.local_id == len(self._nodes) - 1:
                self._nodes.pop()
                self._publication_seals.pop_image()
            self.ledger.release(self._node_owner, entries=1, nodes=1)
            self.ledger.release(self._origin_owner, entries=1)
            raise
        self.ledger.bump("source_image_origin_publications")
        return image

    def apply(
        self,
        adapter: SourceBoundImageAdapter,
        source: Hashable,
        action: Hashable,
    ) -> SourceImageID:
        """Apply one action with an explicit chronological postorder stack."""
        adapter_key = self._registered(adapter)
        self._validate_key(source, "source image source")
        self._validate_key(action, "source image action")
        adapter.validate_action(action)
        origin = self._origin(adapter, source)
        frames: list[_ApplyFrame] = [_ApplyFrame(origin, action)]
        values: list[SourceImageID] = []
        active: set[tuple[str, str, Hashable]] = set()
        workspace_credit = 1
        self.ledger.reserve(self._workspace_owner, entries=1, nodes=1)

        def push_frame(frame: _ApplyFrame) -> None:
            nonlocal workspace_credit
            self.ledger.reserve(self._workspace_owner, entries=1, nodes=1)
            workspace_credit += 1
            frames.append(frame)

        def push_value(image: SourceImageID) -> None:
            nonlocal workspace_credit
            self.ledger.reserve(self._workspace_owner, entries=1, nodes=1)
            workspace_credit += 1
            values.append(image)

        def release_workspace() -> None:
            nonlocal workspace_credit
            self.ledger.release(self._workspace_owner, entries=1, nodes=1)
            workspace_credit -= 1

        try:
            while frames:
                peak = len(frames) + len(values) + len(active)
                previous = self.ledger.counters.get("source_image_workspace_peak", 0)
                if peak > previous:
                    self.ledger.bump("source_image_workspace_peak", peak - previous)
                self.ledger.bump("source_image_postorder_frames")
                frame = frames.pop()
                release_workspace()
                apply_key = _ApplyKey(adapter_key, frame.source, frame.action)
                action_key = adapter_key[0], adapter_key[1], frame.action
                if frame.stage == 0:
                    found = self._applications.get(apply_key)
                    if found is not None:
                        self._validate_application_binding(adapter, apply_key, found)
                        push_value(found)
                        self.ledger.bump("source_image_application_hits")
                        continue
                    source_view = self.view(frame.source)
                    admitted_input = adapter.admitted_input_key(
                        frame.action, source_view
                    )
                    relative_key = None
                    if admitted_input is not None:
                        self._validate_key(
                            admitted_input, "source image admitted input"
                        )
                        relative_key = _RelativeKey(
                            adapter_key, frame.action, admitted_input
                        )
                        cached = self._relative.get(relative_key)
                        if cached is not None:
                            cached_source = self.view(cached.source)
                            cached_result = self.view(cached.result)
                            if (
                                adapter.admitted_input_key(
                                    frame.action, cached_source
                                )
                                != admitted_input
                            ):
                                raise ValueError(
                                    "relative transfer has another admitted input"
                                )
                            self._validate_application_binding(
                                adapter,
                                _ApplyKey(adapter_key, cached.source, frame.action),
                                cached.result,
                            )
                            candidate = adapter.transport_reuse(
                                frame.action,
                                cached_source,
                                cached_result,
                                source_view,
                            )
                            cumulative = adapter.compose_actions(
                                source_view.binding.action, frame.action
                            )
                            result = self._publish_application_result(
                                apply_key,
                                source_view.binding.source,
                                cumulative,
                                candidate,
                                relative_key=None,
                            )
                            push_value(result)
                            self.ledger.bump("source_image_relative_transfer_hits")
                            continue
                    children = adapter.action_children(frame.action)
                    if children is None:
                        candidate = adapter.apply_primitive(frame.action, source_view)
                        cumulative = adapter.compose_actions(
                            source_view.binding.action, frame.action
                        )
                        result = self._publish_application_result(
                            apply_key,
                            source_view.binding.source,
                            cumulative,
                            candidate,
                            relative_key=relative_key,
                        )
                        push_value(result)
                        self.ledger.bump("source_image_primitive_applications")
                        continue
                    if type(children) is not tuple or len(children) != 2:
                        raise TypeError(
                            "source image action requires before/after children"
                        )
                    before, after = children
                    adapter.validate_action(before)
                    adapter.validate_action(after)
                    if frame.action in children:
                        raise ValueError(
                            "source image action cannot directly contain itself"
                        )
                    if action_key in active:
                        raise ValueError("source image action graph contains a cycle")
                    if adapter.compose_actions(before, after) != frame.action:
                        raise ValueError(
                            "source image children do not compose to their parent"
                        )
                    self.ledger.reserve(self._workspace_owner, entries=1, nodes=1)
                    workspace_credit += 1
                    active.add(action_key)
                    frame.stage, frame.children, frame.relative_key = (
                        1,
                        children,
                        relative_key,
                    )
                    push_frame(frame)
                    push_frame(_ApplyFrame(frame.source, before))
                    continue
                if frame.stage == 1:
                    if frame.children is None or not values:
                        raise AssertionError(
                            "source image frame lost its before result"
                        )
                    before_image = values.pop()
                    release_workspace()
                    frame.stage, frame.before = 2, before_image
                    push_frame(frame)
                    push_frame(_ApplyFrame(before_image, frame.children[1]))
                    continue
                if frame.children is None or frame.before is None or not values:
                    raise AssertionError(
                        "source image frame lost chronological dependencies"
                    )
                after_image = values.pop()
                release_workspace()
                source_view = self.view(frame.source)
                before_view = self.view(frame.before)
                after_view = self.view(after_image)
                expected = adapter.compose_actions(
                    source_view.binding.action, frame.action
                )
                if after_view.binding.action != expected:
                    raise ValueError(
                        "source image chronology produced another action binding"
                    )
                candidate = adapter.compose_chronological(
                    frame.action, source_view, before_view, after_view
                )
                if candidate.failure_prefix != after_view.failure_prefix:
                    raise ValueError(
                        "source image composition discarded its chronological failure"
                    )
                result = self._publish_application_result(
                    apply_key,
                    source_view.binding.source,
                    expected,
                    candidate,
                    relative_key=frame.relative_key,
                )
                if action_key not in active:
                    raise AssertionError("source image action lost its active frame")
                active.remove(action_key)
                release_workspace()
                push_value(result)
                self.ledger.bump("source_image_chronological_compositions")
            if len(values) != 1:
                raise AssertionError("source image scheduler produced multiple results")
            result = values.pop()
            release_workspace()
            return result
        finally:
            if workspace_credit:
                self.ledger.release(
                    self._workspace_owner,
                    entries=workspace_credit,
                    nodes=workspace_credit,
                )

    def _publish_application_result(
        self,
        key: _ApplyKey,
        source: Hashable,
        cumulative_action: Hashable,
        candidate: SourceImageCandidate,
        *,
        relative_key: _RelativeKey | None,
    ) -> SourceImageID:
        if key in self._applications:
            raise ValueError("source image application was concurrently published")
        candidate.__post_init__()
        source_failure = self.view(key.source).failure_prefix
        if source_failure is not None and candidate.failure_prefix != source_failure:
            raise ValueError("source image application discarded its first failure")
        publish_relative = relative_key is not None and relative_key not in self._relative
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
                reserved=True,
            )
            self._applications[key] = image
            if publish_relative:
                assert relative_key is not None
                self._relative[relative_key] = _RelativeApplication(key.source, image)
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
            self.ledger.bump("source_image_relative_transfer_publications")
        return image

    def _validate_application_binding(
        self,
        adapter: SourceBoundImageAdapter,
        key: _ApplyKey,
        image: SourceImageID,
    ) -> None:
        source = self.view(key.source)
        result = self.view(image)
        expected = adapter.compose_actions(source.binding.action, key.action)
        if (
            result.binding.family != key.adapter_key[0]
            or result.binding.semantic_version != key.adapter_key[1]
            or result.binding.source != source.binding.source
            or result.binding.action != expected
        ):
            raise ValueError("source image application binding was altered")

    def projection(
        self,
        adapter: SourceBoundImageAdapter,
        image: SourceImageID,
        demand: SourceImageDemand,
    ) -> SourceImageProjection:
        adapter_key = self._registered(adapter)
        record = self.resolve(image)
        if record.adapter_key != adapter_key:
            raise ValueError("source image belongs to another family adapter")
        if type(demand) is not SourceImageDemand:
            raise TypeError("source image projection requires an exact demand")
        demand.__post_init__()
        key = image, demand
        found = self._projections.get(key)
        if found is not None:
            if (
                type(found) is not _ProjectionRecord
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
            found.projection.__post_init__()
            self.ledger.bump("source_image_projection_hits")
            return found.projection
        projected = adapter.project(self._view_record(image, record), demand)
        if type(projected) is not SourceImageProjection:
            raise TypeError("source image adapter returned another projection sort")
        projected.__post_init__()
        snapshot = publication_seal((image, demand, projected), self.ledger)
        self.ledger.reserve(self._projection_owner, entries=1, nodes=1)
        try:
            self._publication_seals.put_projection(key, snapshot)
            self._projections[key] = _ProjectionRecord(
                image, demand, projected, _IMAGE_RECORD_SEAL,
                snapshot,
            )
        except BaseException:
            self._projections.pop(key, None)
            if key in self._publication_seals.projections:
                self._publication_seals.drop_projection(key)
            self.ledger.release(self._projection_owner, entries=1, nodes=1)
            raise
        self.ledger.bump("source_image_projection_publications")
        return projected

    def first_failure(
        self,
        adapter: SourceBoundImageAdapter,
        image: SourceImageID,
    ) -> Hashable | None:
        adapter_key = self._registered(adapter)
        view = self.view(image)
        if self.resolve(image).adapter_key != adapter_key:
            raise ValueError("source image belongs to another family adapter")
        failure = adapter.first_failure(view)
        if view.failure_prefix is None and failure is not None:
            raise ValueError("adapter fabricated failure outside the image ledger")
        if view.failure_prefix is not None and failure is None:
            raise ValueError("adapter failed to descend its recorded failure")
        if failure is not None and not isinstance(failure, Hashable):
            raise TypeError("source image failure witness must be immutable")
        self.ledger.bump("source_image_failure_descents")
        return failure


class SourceBoundImageMixin:
    """Methods inherited by ``TileScheduler`` without another executor facade."""

    ledger: ResourceLedger
    _source_images: SourceBoundSchedulerCore | None

    def _source_image_core(self) -> SourceBoundSchedulerCore:
        found = self._source_images
        if found is None:
            found = SourceBoundSchedulerCore(self.ledger)
            self._source_images = found
        return found

    def register_source_image_adapter(
        self, adapter: SourceBoundImageAdapter
    ) -> None:
        self._source_image_core().register(adapter)

    def source_image(
        self,
        adapter: SourceBoundImageAdapter,
        source: Hashable,
        action: Hashable,
    ) -> SourceImageID:
        return self._source_image_core().apply(adapter, source, action)

    def source_projection(
        self,
        adapter: SourceBoundImageAdapter,
        image: SourceImageID,
        demand: SourceImageDemand,
    ) -> SourceImageProjection:
        return self._source_image_core().projection(adapter, image, demand)

    def source_first_failure(
        self,
        adapter: SourceBoundImageAdapter,
        image: SourceImageID,
    ) -> Hashable | None:
        return self._source_image_core().first_failure(adapter, image)

    def clear_source_images(self) -> None:
        if self._source_images is not None:
            self._source_images.clear()


__all__ = [
    "SourceBoundImageAdapter",
    "SourceBoundImageMixin",
    "SourceBoundSchedulerCore",
    "SourceImageBinding",
    "SourceImageCandidate",
    "SourceImageDemand",
    "SourceImageID",
    "SourceImageProjection",
    "SourceImageView",
]
