"""Iterative parent-first construction and observation of recursive images."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING, Generic, Protocol, TypeVar

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import (
    CoordinateOutputMorphismID,
    FieldCellActionID,
    FieldGeometryID,
)
from number_compiler.hashlife.execution.field_capabilities import (
    validate_field_image_application,
    validate_field_transfer_application,
)
from number_compiler.hashlife.execution.field_images import (
    FieldImageID,
    FieldImageRecord,
    FieldImageSummaryRef,
    ImageRequestKey,
    RecursiveFieldImageArena,
    SourceBindingID,
    SourceCellArena,
    SourceCellID,
    SourceForestID,
)
from number_compiler.hashlife.execution.field_transfer import (
    FieldTransferAdapter,
    FieldTransferApplication,
    FieldTransferCandidate,
    FieldTransferExecutor,
)
from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.field_provider import (
        PoweredFieldProviderView,
    )


@dataclass(frozen=True, slots=True)
class FieldImageCandidate:
    interface: LocalInterfaceID
    output: CoordinateOutputMorphismID
    summary: FieldImageSummaryRef


@dataclass(frozen=True, slots=True)
class ParentObservation:
    """Tagged result so a cold computation can never be reported as a hit."""

    value: int
    early_hit: bool = False

    def __post_init__(self) -> None:
        if type(self.value) is not int or type(self.early_hit) is not bool:
            raise TypeError("parent observations require exact tagged values")


class FieldImageConstructionAdapter(Protocol):
    """Family law used by the shared scheduler; no occurrence cache belongs here."""

    def validate_action(self, action: FieldCellActionID) -> None: ...

    def signature(
        self,
        action: FieldCellActionID,
        geometry: FieldGeometryID,
    ) -> PortSignatureID: ...

    def action_children(
        self,
        action: FieldCellActionID,
    ) -> tuple[FieldCellActionID, FieldCellActionID] | None:
        """Return the canonical construction witness for a composed action."""
        ...

    def leaf(
        self,
        action: FieldCellActionID,
        source: SourceCellID,
        geometry: FieldGeometryID,
    ) -> FieldImageCandidate: ...

    def forest(
        self,
        action: FieldCellActionID,
        source: SourceForestID,
        geometry: FieldGeometryID,
    ) -> FieldImageCandidate:
        """Compile one complete source forest as a parametric macrocell."""
        ...

    def join(
        self,
        action: FieldCellActionID,
        source: SourceCellID,
        left: FieldImageID,
        right: FieldImageID,
        geometry: FieldGeometryID,
    ) -> FieldImageCandidate: ...

    def temporal(
        self,
        action: FieldCellActionID,
        before: FieldCellActionID,
        after: FieldCellActionID,
        source: SourceCellID,
        before_image: FieldImageID | None,
        left: FieldImageID | None,
        right: FieldImageID | None,
        geometry: FieldGeometryID,
    ) -> FieldImageCandidate:
        """Substitute ``after`` through ``before_image`` without a midpoint."""
        ...

    def point(self, image: FieldImageID, coordinate: int) -> int:
        """Explicit compatibility observation for exact-summary test adapters."""
        ...


class FieldImageAdapter(FieldImageConstructionAdapter, Protocol):
    """Construction plus bound point/extent observations for applications."""

    def validate_port(self, incoming: ArenaHandle) -> None: ...

    def point_bound(
        self,
        image: FieldImageID,
        source: SourceBindingID,
        incoming: ArenaHandle,
        coordinate: int,
    ) -> int: ...

    def width_bound(
        self,
        image: FieldImageID,
        source: SourceBindingID,
        incoming: ArenaHandle,
    ) -> int: ...


_TRANSFER_APPLICATION_SEAL = object()


AdapterT_co = TypeVar(
    "AdapterT_co", bound=FieldImageConstructionAdapter, covariant=True
)


class RecursiveFieldImageExecutor(Generic[AdapterT_co]):
    """One parent-first scheduler shared by every certified arithmetic family."""

    is_algebraic_field_action_executor = True

    def __init__(
        self,
        sources: SourceCellArena,
        images: RecursiveFieldImageArena,
        adapter: AdapterT_co,
    ) -> None:
        if images.sources is not sources:
            raise ValueError("field executor sources belong to another image arena")
        self.sources = sources
        self.images = images
        self.adapter = adapter
        self.ledger = images.ledger
        self.ledger.register_execution_root(self)

    def image(
        self,
        action: FieldCellActionID,
        source: SourceBindingID,
        geometry: FieldGeometryID,
        signature: PortSignatureID,
    ) -> FieldImageID:
        """Probe the largest source binding before constructing descendants."""
        if type(source) is SourceCellID:
            return self._cell_image(action, source, geometry, signature)
        if type(source) is SourceForestID:
            return self._forest_image(action, source, geometry, signature)
        raise TypeError("field image requires a scoped source binding")

    def _cell_image(
        self,
        action: FieldCellActionID,
        source: SourceCellID,
        geometry: FieldGeometryID,
        signature: PortSignatureID,
    ) -> FieldImageID:
        root_key = ImageRequestKey(action, source, geometry, signature)
        self.images.validate_request(root_key)
        if self.adapter.signature(action, geometry) != signature:
            raise ValueError("field image request has another normalized signature")
        found = self.images.probe(root_key)
        self.ledger.bump("recursive_field_image_requests")
        if found is not None:
            self.ledger.bump("recursive_field_image_early_hits")
            return found
        # One trampoline handles temporal and spatial dependencies.
        stack: list[
            tuple[FieldCellActionID, SourceCellID, FieldGeometryID, bool, bool]
        ] = [(action, source, geometry, False, True)]
        built: dict[tuple[int, int, int], FieldImageID] = {}
        active: set[tuple[int, int, int]] = set()
        while stack:
            current_action, current, current_geometry, ready, known_miss = stack.pop()
            built_key = (
                current_action.local_id,
                current.local_id,
                current_geometry.local_id,
            )
            current_signature = self.adapter.signature(
                current_action,
                current_geometry,
            )
            key = ImageRequestKey(
                current_action,
                current,
                current_geometry,
                current_signature,
            )
            if known_miss:
                self.images.validate_request(key)
                cached = None
            else:
                cached = self.images.probe(key)
            if not known_miss:
                self.ledger.bump("recursive_field_image_requests")
            if cached is not None:
                self.ledger.bump("recursive_field_image_early_hits")
                built[built_key] = cached
                active.discard(built_key)
                continue
            node = self.sources.resolve(current)
            action_children = self.adapter.action_children(current_action)
            direct_temporal = bool(
                getattr(self.adapter, "direct_temporal_images", False)
            )
            left = right = None
            left_geometry = right_geometry = None
            if node.level:
                left, right = self.sources.children(current)
                left_geometry = self.images.geometries.child(current_geometry, 0)
                right_geometry = self.images.geometries.child(current_geometry, 1)
            if not ready:
                if built_key in active:
                    raise ValueError("cyclic field-action construction witness")
                active.add(built_key)
                stack.append((current_action, current, current_geometry, True, True))
                if action_children is not None and not direct_temporal:
                    before, after = action_children
                    self.images.validate_action(before)
                    self.images.validate_action(after)
                    if before == current_action or after == current_action:
                        raise ValueError("field action cannot contain itself")
                    prefix_key = (
                        before.local_id,
                        current.local_id,
                        current_geometry.local_id,
                    )
                    if prefix_key not in built:
                        stack.append((before, current, current_geometry, False, False))
                if node.level:
                    assert left is not None and right is not None
                    assert left_geometry is not None and right_geometry is not None
                    right_key = (
                        current_action.local_id,
                        right.local_id,
                        right_geometry.local_id,
                    )
                    left_key = (
                        current_action.local_id,
                        left.local_id,
                        left_geometry.local_id,
                    )
                    if right_key not in built:
                        stack.append(
                            (current_action, right, right_geometry, False, False)
                        )
                    if left_key not in built:
                        stack.append(
                            (current_action, left, left_geometry, False, False)
                        )
                continue
            left_image = right_image = None
            if node.level:
                assert left is not None and right is not None
                assert left_geometry is not None and right_geometry is not None
                left_image = built[
                    (
                        current_action.local_id,
                        left.local_id,
                        left_geometry.local_id,
                    )
                ]
                right_image = built[
                    (
                        current_action.local_id,
                        right.local_id,
                        right_geometry.local_id,
                    )
                ]
            if action_children is None:
                if node.level == 0:
                    candidate = self.adapter.leaf(
                        current_action,
                        current,
                        current_geometry,
                    )
                else:
                    if left_image is None or right_image is None:
                        raise AssertionError(
                            "spatial dependencies were not constructed"
                        )
                    candidate = self.adapter.join(
                        current_action,
                        current,
                        left_image,
                        right_image,
                        current_geometry,
                    )
            else:
                before, after = action_children
                before_image = (
                    None
                    if direct_temporal
                    else built[
                        (
                            before.local_id,
                            current.local_id,
                            current_geometry.local_id,
                        )
                    ]
                )
                candidate = self.adapter.temporal(
                    current_action,
                    before,
                    after,
                    current,
                    before_image,
                    left_image,
                    right_image,
                    current_geometry,
                )
            if type(candidate) is not FieldImageCandidate:
                raise TypeError("field-image adapter returned an incomplete candidate")
            record = FieldImageRecord(
                node.level,
                left_image,
                right_image,
                candidate.interface,
                candidate.output,
                current_geometry,
                candidate.summary,
            )
            built[built_key] = self.images.publish(key, record)
            active.discard(built_key)
            if action_children is not None:
                self.ledger.bump("recursive_field_image_temporal_compositions")
            elif node.level:
                self.ledger.bump("recursive_field_image_spatial_compositions")
            else:
                self.ledger.bump("recursive_field_image_primitive_evaluations")
        result = built[(action.local_id, source.local_id, geometry.local_id)]
        self.ledger.bump("field_image_parent_evaluations")
        return result

    def _geometry_at_level(
        self,
        parent: FieldGeometryID,
        level: int,
    ) -> FieldGeometryID:
        from number_compiler.hashlife.actions.field_actions import FieldGeometry

        record = self.images.geometries.resolve(parent)
        return self.images.geometries.intern(
            FieldGeometry(
                level,
                record.orientation,
                record.phase,
                record.phase_count,
                record.halo_left,
                record.halo_right,
            )
        )

    def _forest_image(
        self,
        action: FieldCellActionID,
        source: SourceForestID,
        geometry: FieldGeometryID,
        signature: PortSignatureID,
    ) -> FieldImageID:
        """Build a balanced recursive image over a canonical dyadic cover."""
        root_key = ImageRequestKey(action, source, geometry, signature)
        self.images.validate_request(root_key)
        if self.adapter.signature(action, geometry) != signature:
            raise ValueError("field image request has another normalized signature")
        found = self.images.probe(root_key)
        self.ledger.bump("recursive_field_forest_requests")
        if found is not None:
            self.ledger.bump("recursive_field_forest_early_hits")
            return found
        forest = self.sources.resolve_forest(source)
        cells = forest.cells
        widths = tuple(self.sources.resolve(cell).width for cell in cells)
        prefix = [0]
        for width in widths:
            prefix.append(prefix[-1] + width)
        built: dict[tuple[int, int], FieldImageID] = {}
        stack: list[tuple[int, int, bool]] = [(0, len(cells), False)]
        while stack:
            low, high, ready = stack.pop()
            span = high - low
            if span == 1:
                cell = cells[low]
                level = self.sources.resolve(cell).level
                built[(low, high)] = self._cell_image(
                    action,
                    cell,
                    self._geometry_at_level(geometry, level),
                    signature,
                )
                continue
            total = prefix[high] - prefix[low]
            target = prefix[low] + total // 2
            split = low + 1
            while split < high - 1 and prefix[split + 1] <= target:
                split += 1
            if not ready:
                stack.extend(
                    ((low, high, True), (split, high, False), (low, split, False))
                )
                continue
            left, right = built[(low, split)], built[(split, high)]
            level = (
                max(
                    self.images.resolve(left).level,
                    self.images.resolve(right).level,
                )
                + 1
            )
            current_geometry = (
                geometry
                if low == 0 and high == len(cells)
                else self._geometry_at_level(geometry, level)
            )
            current_source = (
                source
                if low == 0 and high == len(cells)
                else self.sources.forest_from_cells(cells[low:high])
            )
            key = ImageRequestKey(action, current_source, current_geometry, signature)
            is_known_root_miss = low == 0 and high == len(cells)
            if is_known_root_miss:
                cached = None
            else:
                self.ledger.bump("recursive_field_forest_requests")
                cached = self.images.probe(key)
            if cached is not None:
                built[(low, high)] = cached
                self.ledger.bump("recursive_field_forest_early_hits")
                continue
            forest_join = getattr(self.adapter, "forest_join", None)
            candidate = (
                forest_join(action, current_source, left, right, current_geometry)
                if callable(forest_join)
                else self.adapter.forest(action, current_source, current_geometry)
            )
            if type(candidate) is not FieldImageCandidate:
                raise TypeError(
                    "field-image adapter returned an incomplete forest candidate"
                )
            built[(low, high)] = self.images.publish(
                key,
                FieldImageRecord(
                    level,
                    left,
                    right,
                    candidate.interface,
                    candidate.output,
                    current_geometry,
                    candidate.summary,
                ),
            )
            self.ledger.bump("recursive_field_forest_spatial_compositions")
            self.ledger.bump("source_forest_image_compositions")
        result = built[(0, len(cells))]
        # A single-cell forest still needs its own validated occurrence binding.
        if len(cells) == 1:
            child = self.images.resolve(result)
            candidate = self.adapter.forest(action, source, geometry)
            record = FieldImageRecord(
                child.level,
                child.left,
                child.right,
                candidate.interface,
                candidate.output,
                geometry,
                candidate.summary,
            )
            result = self.images.publish(root_key, record)
            self.ledger.bump("recursive_field_forest_primitive_evaluations")
        self.ledger.bump("source_forest_image_compilations")
        self.ledger.bump("field_image_parent_evaluations")
        return result

    def point(self, image: FieldImageID, coordinate: int) -> int:
        from number_compiler.hashlife.execution.field_images import (
            ParametricFieldImageSummary,
        )

        record = self.images.resolve(image)
        if type(coordinate) is not int:
            raise TypeError("field-image coordinate must be an exact integer")
        limit = (
            record.summary.extent_bound
            if isinstance(record.summary, ParametricFieldImageSummary)
            else record.summary.extent
        )
        if not 0 <= coordinate < limit:
            raise IndexError(coordinate)
        self.ledger.bump("point_observations")
        return self.adapter.point(image, coordinate)

    def width(self, image: FieldImageID) -> int:
        from number_compiler.hashlife.execution.field_images import (
            ParametricFieldImageSummary,
        )

        record = self.images.resolve(image)
        self.ledger.bump("width_observations")
        if isinstance(record.summary, ParametricFieldImageSummary):
            observe = getattr(self.adapter, "width", None)
            if not callable(observe):
                raise TypeError("parametric field image requires a width observer")
            result = observe(image)
            if (
                type(result) is not int
                or not 0 <= result <= record.summary.extent_bound
            ):
                raise ValueError(
                    "field-image width observer returned an invalid extent"
                )
            return result
        return (
            0 if record.summary.last_active is None else record.summary.last_active + 1
        )

    def application(
        self: RecursiveFieldImageExecutor[FieldImageAdapter],
        action: FieldCellActionID,
        source: SourceBindingID,
        geometry: FieldGeometryID,
        signature: PortSignatureID,
        incoming: ArenaHandle,
    ) -> FieldImageApplication:
        """Bind one source occurrence without constructing its future image."""
        self.images.validate_request(
            ImageRequestKey(action, source, geometry, signature)
        )
        self.adapter.validate_port(incoming)
        if self.adapter.signature(action, geometry) != signature:
            raise ValueError("field application has another normalized signature")
        return FieldImageApplication(
            self,
            action,
            source,
            geometry,
            signature,
            incoming,
            _APPLICATION_SEAL,
        )


_APPLICATION_SEAL = object()


class FieldImageApplication:
    """Point-lazy occurrence view backed by one verified recursive executor."""

    __slots__ = (
        "__weakref__",
        "_seal",
        "action",
        "executor",
        "geometry",
        "incoming",
        "ledger",
        "signature",
        "source",
    )

    is_algebraic_field_action_executor = True

    def __init__(
        self,
        executor: RecursiveFieldImageExecutor[FieldImageAdapter],
        action: FieldCellActionID,
        source: SourceBindingID,
        geometry: FieldGeometryID,
        signature: PortSignatureID,
        incoming: ArenaHandle,
        seal: object,
    ) -> None:
        if seal is not _APPLICATION_SEAL:
            raise TypeError("field-image applications are issued by their executor")
        self.executor = executor
        self.action = action
        self.source = source
        self.geometry = geometry
        self.signature = signature
        self.incoming = incoming
        self.ledger = executor.ledger
        self._seal = seal
        self.ledger.register_execution_root(self)
        from number_compiler.resources.metric_registry import (
            ALGEBRAIC_FIELD_WORK_COUNTERS,
        )

        for name in ALGEBRAIC_FIELD_WORK_COUNTERS:
            self.ledger.bump(name, 0)
        for name in (
            "diamond_temporal_composition_requests",
            "diamond_temporal_composition_hits",
            "diamond_temporal_composition_evaluations",
        ):
            self.ledger.bump(name, 0)
        self.ledger.bump("algebraic_executor_capability_validated")

    def _image(self) -> FieldImageID:
        self.executor.adapter.validate_port(self.incoming)
        return self.executor.image(
            self.action,
            self.source,
            self.geometry,
            self.signature,
        )

    def provider_view(self) -> PoweredFieldProviderView:
        """Return the validated recursive provider without scalar replay."""
        from number_compiler.hashlife.execution.field_provider import (
            issue_powered_provider_view,
        )

        return issue_powered_provider_view(self)

    def provider_point(self, view: PoweredFieldProviderView, position: int) -> int:
        """Observe a scalar from an issued provider after full scope validation."""
        from number_compiler.hashlife.execution.field_provider import (
            observe_provider_point,
        )

        return observe_provider_point(self, view, position)

    def provider_active_width(self, view: PoweredFieldProviderView) -> int:
        """Observe the active provider extent through its recursive image."""
        from number_compiler.hashlife.execution.field_provider import (
            observe_provider_width,
        )

        return observe_provider_width(self, view)

    def point(self, position: int) -> int:
        if type(position) is not int:
            raise TypeError("field-image coordinate must be an exact integer")
        self.executor.images.validate_request(
            ImageRequestKey(
                self.action,
                self.source,
                self.geometry,
                self.signature,
            )
        )
        self.executor.adapter.validate_port(self.incoming)
        if (
            self.executor.adapter.signature(self.action, self.geometry)
            != self.signature
        ):
            raise ValueError("field application has another normalized signature")
        observe = getattr(self.executor.adapter, "observe_parent_point", None)
        if callable(observe):
            self.ledger.bump("field_image_parent_observation_requests")
            result = observe(
                self.action,
                self.source,
                self.geometry,
                self.signature,
                self.incoming,
                position,
            )
            if result is not None:
                if type(result) is not ParentObservation:
                    raise TypeError("parent point observer returned an untagged result")
                self.ledger.bump(
                    "field_image_parent_observation_early_hits"
                    if result.early_hit
                    else "field_image_parent_observation_evaluations"
                )
                return result.value
        image = self._image()
        return self.executor.adapter.point_bound(
            image,
            self.source,
            self.incoming,
            position,
        )

    def active_width(self) -> int:
        self.executor.images.validate_request(
            ImageRequestKey(
                self.action,
                self.source,
                self.geometry,
                self.signature,
            )
        )
        self.executor.adapter.validate_port(self.incoming)
        if (
            self.executor.adapter.signature(self.action, self.geometry)
            != self.signature
        ):
            raise ValueError("field application has another normalized signature")
        observe = getattr(self.executor.adapter, "observe_parent_width", None)
        if callable(observe):
            self.ledger.bump("field_image_parent_observation_requests")
            result = observe(
                self.action,
                self.source,
                self.geometry,
                self.signature,
                self.incoming,
            )
            if result is not None:
                if type(result) is not ParentObservation or result.value < 0:
                    raise ValueError("parent width observer returned an invalid extent")
                self.ledger.bump(
                    "field_image_parent_observation_early_hits"
                    if result.early_hit
                    else "field_image_parent_observation_evaluations"
                )
                return result.value
        image = self._image()
        return self.executor.adapter.width_bound(image, self.source, self.incoming)

    def retained_entries(self) -> int:
        return self.executor.images.retained_bindings


__all__ = [
    "FieldImageAdapter",
    "FieldImageApplication",
    "FieldImageCandidate",
    "FieldTransferAdapter",
    "FieldTransferApplication",
    "FieldTransferCandidate",
    "FieldTransferExecutor",
    "ParentObservation",
    "RecursiveFieldImageExecutor",
    "validate_field_image_application",
    "validate_field_transfer_application",
]
