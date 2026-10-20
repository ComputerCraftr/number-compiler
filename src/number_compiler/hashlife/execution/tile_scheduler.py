from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from types import MappingProxyType
from typing import TYPE_CHECKING, Self

from number_compiler.hashlife.execution.source_bound_mixin import (
    SourceBoundImageMixin,
)
from number_compiler.hashlife.execution.tile_result_pinning import ResultPinning
from number_compiler.hashlife.execution.tile_scheduler_frames import (
    _APPLICATION_SEAL,
    _DirectFrame,
)
from number_compiler.hashlife.tiles.tile_boundaries import (
    EMPTY_BOUNDARY_TILES,
    BoundaryTileOperands,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)
from number_compiler.resources.metric_keys import shared as _shared_keys

if TYPE_CHECKING:
    from number_compiler.hashlife.actions.field_actions import FieldCellActionID
    from number_compiler.hashlife.execution.tile_application import TileApplication
    from number_compiler.hashlife.execution.tile_execution_adapter import (
        TileExecutionAdapter,
    )
    from number_compiler.hashlife.tiles.ordered_boolean_support import (
        OrderedBooleanSupportArena,
    )
    from number_compiler.hashlife.tiles.tile_context import (
        ChildContext,
        ResultSemantics,
    )
    from number_compiler.hashlife.tiles.tile_ports import (
        FusedBoundaryContract,
        ResultWiring,
    )
    from number_compiler.hashlife.tiles.tile_result_records import (
        PoweredResultKey,
    )
    from number_compiler.hashlife.tiles.tile_results import (
        CompletedResultArena,
        ResultLease,
    )
    from number_compiler.hashlife.tiles.tiles import TileArena, TileID
    from number_compiler.resources.causal_audit_contracts import (
        CausalSpatialWorkspaceAuditSnapshot,
        CausalTaskWorkspaceAuditSnapshot,
    )
    from number_compiler.resources.causal_types import CausalSpatialValue
    from number_compiler.resources.causal_workspace import (
        CausalSpatialWorkspace,
        CausalTaskWorkspace,
    )
    from number_compiler.resources.stores import LedgerDict
    from number_compiler.resources.tile_dependency_leases import TileDependencyLeases


@dataclass(frozen=True, slots=True)
class TileSchedulerAuditSnapshot:
    """Read-only observation of one scheduler's retained owner relationships."""

    ledger: ResourceLedger
    source_only: bool
    next_application: int | None
    pin_owner: int | None
    pins: Mapping[tuple[int, PoweredResultKey], ResultLease]
    pin_store: LedgerDict[tuple[int, PoweredResultKey], ResultLease] | None
    causal_tasks: CausalTaskWorkspaceAuditSnapshot | None
    causal_workspace: CausalSpatialWorkspaceAuditSnapshot[CausalSpatialValue] | None


@dataclass(frozen=True, slots=True)
class CausalSchedulerAuditOwners:
    """Exact causal owner objects exposed to the resource inventory audit."""

    spatial: CausalSpatialWorkspace[CausalSpatialValue]
    tasks: CausalTaskWorkspace
    pins: LedgerDict[tuple[int, PoweredResultKey], ResultLease]


class TileScheduler(SourceBoundImageMixin, ResultPinning):
    """One iterative complete-result and demand-observation executor."""

    _causal_workspace: CausalSpatialWorkspace[CausalSpatialValue]
    _causal_tasks: CausalTaskWorkspace

    def __init__(
        self,
        tiles: TileArena,
        results: CompletedResultArena,
        adapter: TileExecutionAdapter,
    ) -> None:
        from number_compiler.hashlife.execution.tile_application_authority import (
            TileApplicationRegistry,
        )
        from number_compiler.hashlife.tiles.tile_results import (
            CompletedResultArena as CompletedResultArenaType,
        )
        from number_compiler.hashlife.tiles.tiles import TileArena as TileArenaType
        from number_compiler.resources.causal_workspace import (
            CausalSpatialWorkspace,
            CausalTaskWorkspace,
        )
        from number_compiler.resources.tile_dependency_leases import (
            TileDependencyLeases,
        )

        self._source_only = False
        if (
            type(tiles) is not TileArenaType
            or type(results) is not CompletedResultArenaType
        ):
            raise TypeError("tile scheduling requires canonical tile and result arenas")
        if results.tiles is not tiles or results.ledger is not tiles.ledger:
            raise ValueError("tile scheduler stores belong to another index")
        if getattr(adapter, "ledger", tiles.ledger) is not tiles.ledger:
            raise ValueError("tile adapter belongs to another index")
        if results.causal_tasks is not None:
            raise ValueError("completed results already belong to another scheduler")
        self.tiles, self.results, self.adapter = tiles, results, adapter
        self.ledger = tiles.ledger
        prefix = f"tile-scheduler-{len(self.ledger.inventory())}"
        self._pin_owner = self.ledger.register(
            prefix + "-demanded-results",
            "tile_application_result_pin",
        )
        self._pins: LedgerDict[tuple[int, PoweredResultKey], ResultLease] = (
            self.ledger.make_dict(self._pin_owner)
        )
        self.ledger.register_container(
            self._pin_owner,
            self._pins,
            payloads=self._pins.items,
            node_count=lambda: 0,
        )
        self._applications = TileApplicationRegistry(self, prefix)
        self._source_images = None
        self._causal_dependencies = TileDependencyLeases(
            self.ledger,
            self.tiles,
            prefix,
            self._applications,
        )
        self._causal_workspace = CausalSpatialWorkspace(self.ledger, prefix)
        self._causal_tasks = CausalTaskWorkspace(self.ledger, prefix)
        self._physical_supports: OrderedBooleanSupportArena | None = None
        self.results.attach_causal_tasks(self._causal_tasks)
        if not self.ledger.counters.get(_execution_keys.TILE_CAUSAL_ACCOUNTING_VERSION):
            self.ledger.bump(_execution_keys.TILE_CAUSAL_ACCOUNTING_VERSION, 2)
        self._next_application = 0
        self.ledger.register_execution_root(self)

    @classmethod
    def source_only(cls, ledger: ResourceLedger) -> Self:
        """Create the canonical scheduler owner for source-image execution only."""
        if type(ledger) is not ResourceLedger:
            raise TypeError("source-only tile scheduler requires a resource ledger")
        scheduler = cls.__new__(cls)
        scheduler._source_only = True
        scheduler.ledger = ledger
        scheduler._source_images = None
        ledger.register_execution_root(scheduler)
        return scheduler

    def _require_physical_scheduler(self) -> None:
        if self._source_only:
            raise RuntimeError(
                "source-only tile scheduler cannot execute physical tile methods"
            )

    @property
    def is_source_only(self) -> bool:
        """Whether this scheduler was issued for source-image work only."""
        return self._source_only

    def audit_causal_owners(self) -> CausalSchedulerAuditOwners:
        """Expose the exact owners whose retained causal state must be audited."""
        self._require_physical_scheduler()
        return CausalSchedulerAuditOwners(
            self._causal_workspace,
            self._causal_tasks,
            self._pins,
        )

    def audit_application_registry(
        self, containers: Mapping[int, object]
    ) -> tuple[set[int], set[tuple[int, int]]]:
        """Audit the scheduler's application registry through its owner API."""
        self._require_physical_scheduler()
        return self._applications.audit(containers)

    def audit_application_bindings(
        self, applications: Mapping[int, TileApplication]
    ) -> bool:
        """Check exact registry membership for the discovered live applications."""
        self._require_physical_scheduler()
        return self._applications.matches_live_applications(applications)

    def application_registry_is(self, registry: object) -> bool:
        """Check exact registry ownership without exposing the registry field."""
        return registry is self._applications

    def application_identity_is_live(self, identity: int) -> bool:
        """Check that an application ID was allocated by this scheduler."""
        return type(identity) is int and 0 <= identity < self._next_application

    def validate_application_identity(self, identity: object) -> int:
        """Validate an untrusted ID and return its admitted integer value."""
        if type(identity) is not int or not self.application_identity_is_live(identity):
            raise ValueError("tile application has an invalid scoped identity")
        return identity

    def application_is_registered(self, application: TileApplication) -> bool:
        """Check that this exact application is registered under its identity."""
        if not self.application_identity_is_live(application.identity):
            return False
        try:
            return self._applications.application(application.identity) is application
        except (AttributeError, KeyError, TypeError, ValueError):
            return False

    def application_by_id(self, identity: object) -> TileApplication:
        """Resolve one application after validating an untrusted scoped ID."""
        admitted_identity = self.validate_application_identity(identity)
        return self._applications.application(admitted_identity)

    def register_application(
        self, application: TileApplication, admitted: PoweredResultKey
    ) -> None:
        """Publish an application through the scheduler-owned registry."""
        self._applications.register(application, admitted)

    def unregister_application(self, application: TileApplication) -> None:
        """Remove an application through its scheduler-owned registry."""
        self._applications.unregister(application)

    def replace_application_root(
        self, application: TileApplication, root: ResultLease
    ) -> None:
        """Replace one registered application's completed root lease."""
        if not self.application_is_registered(application):
            raise ValueError("tile application is not registered with this scheduler")
        if root.audit_snapshot().issuer is not self.results:
            raise ValueError("application root belongs to another result arena")
        self._applications.replace_root(application, root)

    def audit_snapshot(self) -> TileSchedulerAuditSnapshot:
        """Return detached pin contents and exact backing-owner identities."""
        if self._source_only:
            return TileSchedulerAuditSnapshot(
                ledger=self.ledger,
                source_only=True,
                next_application=None,
                pin_owner=None,
                pins=MappingProxyType({}),
                pin_store=None,
                causal_tasks=None,
                causal_workspace=None,
            )
        return TileSchedulerAuditSnapshot(
            ledger=self.ledger,
            source_only=False,
            next_application=self._next_application,
            pin_owner=self._pin_owner,
            pins=MappingProxyType(dict(self._pins.items())),
            pin_store=self._pins,
            causal_tasks=self._causal_tasks.audit_snapshot(),
            causal_workspace=self._causal_workspace.audit_snapshot(),
        )

    @property
    def causal_tasks(self) -> CausalTaskWorkspace:
        """Return the scheduler's charged task workspace to causal operations."""
        return self._causal_tasks

    @property
    def causal_workspace(self) -> CausalSpatialWorkspace[CausalSpatialValue]:
        return self._causal_workspace

    @property
    def dependency_leases(self) -> TileDependencyLeases:
        return self._causal_dependencies

    @property
    def physical_supports(self) -> OrderedBooleanSupportArena:
        from number_compiler.hashlife.tiles.ordered_boolean_support import (
            OrderedBooleanSupportArena as OrderedBooleanSupportArenaType,
        )

        self._require_physical_scheduler()
        found = self._physical_supports
        if found is None:
            max_nodes = max(4096, self.ledger.max_nodes or 0)
            hooks = self.adapter.family_hooks
            found = (
                OrderedBooleanSupportArenaType(
                    max_nodes=max_nodes,
                    ledger=self.ledger,
                )
                if hooks is None
                else hooks.support_arena(max_nodes, self.ledger)
            )
            self.results.attach_physical_supports(found)
            self._physical_supports = found
        return found

    def record_workspace_peak(self, size: int) -> None:
        previous = self.ledger.counters.get(
            _execution_keys.TILE_SCHEDULER_WORKSPACE_PEAK, 0
        )
        if size > previous:
            self.ledger.bump(
                _execution_keys.TILE_SCHEDULER_WORKSPACE_PEAK,
                size - previous,
            )

    def child_context(
        self,
        action: FieldCellActionID,
        parent: TileID,
        left: TileID,
        right: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
        side: int,
        boundaries: BoundaryTileOperands = EMPTY_BOUNDARY_TILES,
    ) -> ChildContext:
        from number_compiler.hashlife.tiles.tile_context import (
            ChildContext as ChildContextType,
        )
        from number_compiler.hashlife.tiles.tile_context import (
            bind_context,
        )
        from number_compiler.hashlife.tiles.tile_ports import BoundPorts

        bound = bind_context(self, action, BoundPorts(ports, wiring, boundaries))
        self.ledger.bump(_execution_keys.TILE_SCHEDULER_SIBLING_TRANSFER_REQUESTS)
        context = self.adapter.child_context(
            action,
            parent,
            left,
            right,
            bound.ports,
            bound.wiring,
            side,
        )
        if type(context) is not ChildContextType:
            raise TypeError("bounded child transfer returned another record")
        self.ledger.bump(_execution_keys.TILE_SCHEDULER_SIBLING_TRANSFER_EVALUATIONS)
        return context

    def validate_pin_application(self, application: int) -> None:
        from number_compiler.hashlife.execution.tile_application_authority import (
            application_by_id,
        )

        application_by_id(self, application)

    def pin_causal(
        self,
        application: int,
        key: PoweredResultKey,
        lease: ResultLease,
    ) -> None:
        from number_compiler.hashlife.execution.tile_application_authority import (
            application_by_id,
        )
        from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
        from number_compiler.hashlife.tiles.tile_result_validation import (
            normalize_output_region,
        )
        from number_compiler.hashlife.tiles.tile_results import (
            ResultLease as ResultLeaseType,
        )

        if (
            type(application) is not int
            or not 0 <= application < self._next_application
        ):
            raise ValueError("causal pin has an invalid application identity")
        if type(key) is not PoweredResultKey or type(lease) is not ResultLeaseType:
            raise TypeError("causal pins require an exact result binding")
        self.results.validate_key(key)
        key = normalize_output_region(self.tiles, key)
        lease_binding = lease.audit_snapshot()
        if lease_binding.issuer is not self.results or lease_binding.key != key:
            raise ValueError("causal pin result belongs to another request")
        _ = lease.result
        application_source = application_by_id(self, application).source
        boundaries = [key.boundaries]
        if key.fusion is not None:
            boundaries.extend(
                (
                    key.fusion.producer.boundaries,
                    key.fusion.consumer.boundaries,
                )
            )
        dependencies = tuple(
            dict.fromkeys(
                (
                    key.input,
                    *(tile for item in boundaries for tile in item.tile_ids()),
                )
            )
        )
        dependencies = tuple(
            tile for tile in dependencies if tile != application_source
        )
        binding = application, key
        found = self._pins.get(binding)
        if found is not None:
            if (
                type(found) is not ResultLeaseType
                or found.audit_snapshot().issuer is not self.results
            ):
                raise ValueError("causal result pin contains a foreign lease")
            _ = found.result
            expected = {(application, tile) for tile in dependencies}
            self.ledger.bump(
                _execution_keys.TILE_CAUSAL_PIN_DEPENDENCY_CHECKS,
                len(expected),
            )
            if not all(item in self._causal_dependencies.records for item in expected):
                raise ValueError("causal result pin lost an exact input dependency")
            if found is not lease:
                lease.close()
            self.ledger.bump(_execution_keys.TILE_CAUSAL_PIN_EARLY_HITS)
            return
        reserved = False
        batch = None
        try:
            self.ledger.reserve(self._pin_owner, entries=1)
            reserved = True
            batch = self._causal_dependencies.acquire(application, dependencies)
            self._pins[binding] = lease
        except BaseException:
            self._pins.pop(binding, None)
            if batch is not None:
                self._causal_dependencies.rollback(batch)
            if reserved:
                self.ledger.release(self._pin_owner, entries=1)
            lease.close()
            raise
        self.ledger.bump(_execution_keys.TILE_SCHEDULER_DEMANDED_RESULT_PINS)

    def release_application_pins(self, application: int) -> None:
        self.release_result_pins(application)
        self._causal_dependencies.release_application(application)

    @staticmethod
    def request_key(
        action: FieldCellActionID,
        source: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
        boundaries: BoundaryTileOperands = EMPTY_BOUNDARY_TILES,
        fusion: FusedBoundaryContract | None = None,
    ) -> PoweredResultKey:
        from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey

        return PoweredResultKey(action, source, ports, wiring, boundaries, fusion)

    def child_actions(
        self,
        action: FieldCellActionID,
    ) -> tuple[FieldCellActionID, FieldCellActionID] | None:
        from number_compiler.hashlife.execution import tile_kernel

        if type(self.adapter) is not tile_kernel.PrimitiveTileKernelAdapter:
            self.adapter.validate_action(action)
        children = self.adapter.action_children(action)
        if children is None:
            return None
        if type(children) is not tuple or len(children) != 2:
            raise TypeError("action composition requires before and after actions")
        before, after = children
        self.adapter.validate_action(before)
        self.adapter.validate_action(after)
        if action in children:
            raise ValueError("field action cannot directly contain itself")
        return before, after

    def validate_execution_key(self, key: PoweredResultKey) -> None:
        self.results.validate_key(key)
        self.validate_execution_context(key)

    def validate_execution_context(self, key: PoweredResultKey) -> None:
        from number_compiler.hashlife.execution.tile_execution_validation import (
            validate_execution_context,
        )

        validate_execution_context(self, key)

    def lookup_execution_key(self, key: PoweredResultKey) -> ResultLease | None:
        return self.results.lookup(
            key, validate_context=self.validate_execution_context
        )

    def _publish_leaf(
        self,
        key: PoweredResultKey,
        symbol: int,
        semantics: ResultSemantics,
    ) -> ResultLease:
        source = self.tiles.resolve(key.input)
        if source.level or source.symbol is None:
            raise ValueError("primitive execution requires one canonical leaf")
        with self.tiles.leaf(source.alphabet, symbol) as output:
            result = semantics.completed(output.tile)
            if result.relative_extent > 1:
                raise ValueError("leaf result extent exceeds one tile cell")
            return self.results.publish(key, result)

    def complete_leaf(self, root: PoweredResultKey) -> ResultLease:
        from number_compiler.hashlife.interfaces.semantic_structures import (
            LocalInterfaceID,
        )
        from number_compiler.hashlife.tiles.tile_context import (
            PrimitiveTileResult,
            ResultSemantics,
            TemporalCocycle,
            bind_context,
        )
        from number_compiler.hashlife.tiles.tile_ports import BoundPorts

        self.results.validate_key(root)
        source = self.tiles.resolve(root.input)
        if source.level or source.symbol is None:
            raise ValueError("leaf completion requires one canonical leaf")
        self.ledger.bump(_execution_keys.COMPLETED_RESULT_EVALUATIONS)
        interface = self.adapter.leaf_interface(
            root.action,
            root.input,
            root.wiring,
        )
        if type(interface) is not LocalInterfaceID:
            raise TypeError("leaf compiler returned a noncanonical interface")
        record = self.results.interfaces.resolve(interface)
        if record.signature != root.wiring.signature:
            raise ValueError("leaf function has another port signature")
        bound = bind_context(
            self,
            root.action,
            BoundPorts(root.ports, root.wiring, root.boundaries),
        )
        value = self.adapter.apply_leaf(interface, bound.ports)
        if type(value) is not PrimitiveTileResult:
            raise TypeError("leaf function returned an incomplete result")
        if value.semantics.outgoing != interface:
            raise ValueError("leaf result discarded its compiled interface")
        cocycle = self.adapter.action_cocycle(root.action)
        if type(cocycle) is not TemporalCocycle:
            raise TypeError("field action returned a noncanonical cocycle")
        observed = self.adapter.leaf_observation(
            root.action,
            root.input,
            interface,
            bound.ports,
        )
        if type(observed) is not TemporalCocycle or observed.physical_ticks:
            raise TypeError("leaf observation returned an invalid cocycle delta")
        semantics = ResultSemantics(
            value.semantics.outgoing,
            value.semantics.outgoing_ports,
            cocycle.physical_ticks,
            cocycle.event_weight + observed.event_weight,
            cocycle.frame_shift + observed.frame_shift,
            value.semantics.relative_origin,
            value.semantics.relative_extent,
            value.semantics.outgoing_boundaries,
            observed_input_ports=bound.ports,
        )
        from number_compiler.hashlife.execution.tile_physical_support import (
            primitive_physical_support,
        )

        support = primitive_physical_support(self, root.action, root.input, bound.ports)
        if support is not None:
            semantics = ResultSemantics(
                semantics.outgoing,
                semantics.outgoing_ports,
                semantics.physical_ticks,
                semantics.event_weight,
                semantics.frame_shift,
                semantics.relative_origin,
                semantics.relative_extent,
                semantics.outgoing_boundaries,
                semantics.fusion,
                semantics.observed_input_ports,
                support,
            )
        self.ledger.bump(_execution_keys.TILE_SCHEDULER_LEAF_FUNCTION_APPLICATIONS)
        return self._publish_leaf(root, value.symbol, semantics)

    def complete_direct(
        self, root: PoweredResultKey, *, checked_miss: bool = False
    ) -> ResultLease:
        from number_compiler.hashlife.tiles.tile_context import (
            ResultSemantics,
            bind_context,
            validate_midpoint_exits,
        )
        from number_compiler.hashlife.tiles.tile_ports import BoundPorts

        frames: list[_DirectFrame] = [_DirectFrame(root, checked_miss=checked_miss)]
        values: list[ResultLease] = []
        try:
            while frames:
                self.record_workspace_peak(len(frames) + len(values))
                self.ledger.bump(_execution_keys.TILE_SCHEDULER_FRAMES)
                frame = frames.pop()
                key = frame.key
                if frame.stage == 0:
                    if frame.checked_miss:
                        self.validate_execution_key(key)
                        found = None
                    else:
                        found = self.lookup_execution_key(key)
                    if found is not None:
                        values.append(found)
                        continue
                    node = self.tiles.resolve(key.input)
                    if not node.level:
                        values.append(self.complete_leaf(key))
                        continue
                    self.ledger.bump(_execution_keys.COMPLETED_RESULT_EVALUATIONS)
                    if node.left is None or node.right is None:
                        raise ValueError("malformed canonical parent")
                    left_context = self.child_context(
                        key.action,
                        key.input,
                        node.left,
                        node.right,
                        key.ports,
                        key.wiring,
                        0,
                        key.boundaries,
                    )
                    right_context = self.child_context(
                        key.action,
                        key.input,
                        node.left,
                        node.right,
                        key.ports,
                        key.wiring,
                        1,
                        key.boundaries,
                    )
                    frame.stage = 1
                    frame.left_context, frame.right_context = (
                        left_context,
                        right_context,
                    )
                    frames.append(frame)
                    frames.append(
                        _DirectFrame(
                            self.request_key(
                                key.action,
                                node.right,
                                right_context.ports,
                                right_context.wiring,
                                right_context.boundaries,
                            )
                        )
                    )
                    frames.append(
                        _DirectFrame(
                            self.request_key(
                                key.action,
                                node.left,
                                left_context.ports,
                                left_context.wiring,
                                left_context.boundaries,
                            )
                        )
                    )
                    continue
                right, left = values.pop(), values.pop()
                try:
                    left_result, right_result = left.result, right.result
                    if getattr(self.adapter, "check_two_sided_midpoints", False):
                        if frame.left_context is None or frame.right_context is None:
                            raise ValueError(
                                "spatial frame lost its midpoint contracts"
                            )
                        validate_midpoint_exits(
                            frame.left_context,
                            frame.right_context,
                            left_result,
                            right_result,
                        )
                    bound = bind_context(
                        self,
                        key.action,
                        BoundPorts(key.ports, key.wiring, key.boundaries),
                    )
                    semantics = self.adapter.join_semantics(
                        key.action,
                        key.input,
                        bound.ports,
                        bound.wiring,
                        left_result,
                        right_result,
                    )
                    if type(semantics) is not ResultSemantics:
                        raise TypeError("spatial join returned incomplete semantics")
                    with self.tiles.join(left.output, right.output) as output:
                        values.append(
                            self.results.publish(
                                key,
                                semantics.completed(output.tile),
                            )
                        )
                    self.ledger.bump(
                        _execution_keys.TILE_SCHEDULER_SPATIAL_COMPOSITIONS
                    )
                finally:
                    left.close()
                    right.close()
            if len(values) != 1:
                raise AssertionError("tile scheduler produced multiple results")
            return values.pop()
        except BaseException:
            for value in values:
                value.close()
            raise

    def complete(
        self,
        action: FieldCellActionID,
        source: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
        *,
        boundaries: BoundaryTileOperands = EMPTY_BOUNDARY_TILES,
        fusion: FusedBoundaryContract | None = None,
    ) -> ResultLease:
        from number_compiler.hashlife.execution.tile_clock_dispatch import (
            complete_clock,
        )
        from number_compiler.hashlife.tiles.tile_context import (
            after_context,
            before_context,
            temporal_result,
        )

        self._require_physical_scheduler()
        validator = getattr(self.adapter, "validate_wiring", None)
        if validator is not None:
            validator(action, wiring)
        key = self.request_key(action, source, ports, wiring, boundaries, fusion)
        found = self.lookup_execution_key(key)
        if found is not None:
            self.ledger.bump(_execution_keys.TILE_SCHEDULER_PARENT_EARLY_HITS)
            return found
        clock = complete_clock(self, key)
        if clock is not None:
            return clock
        from number_compiler.hashlife.execution.tile_causal_entry import causal_complete

        causal = causal_complete(self, key)
        if causal is not None:
            return causal
        children = self.child_actions(action)
        if (
            children is not None
            and getattr(
                self.adapter,
                "complete_via_midpoint_tiles",
                False,
            )
            is True
        ):
            self.ledger.bump(_execution_keys.TILE_SCHEDULER_TEMPORAL_COMPLETE_REQUESTS)
            from number_compiler.hashlife.execution.tile_temporal import (
                complete_temporal,
            )

            return complete_temporal(self, key)
        if children is not None:
            producer = before_context(self, key, children[0])
            before_key = self.request_key(
                children[0],
                source,
                producer.ports,
                producer.wiring,
                producer.boundaries,
            )
            midpoint = self.lookup_execution_key(before_key)
            if midpoint is not None:
                try:
                    context = after_context(self, key, children[1], midpoint.result)
                    after = self.complete_direct(
                        self.request_key(
                            children[1],
                            midpoint.output,
                            context.ports,
                            context.wiring,
                            context.boundaries,
                        )
                    )
                    try:
                        self.ledger.bump(_execution_keys.COMPLETED_RESULT_EVALUATIONS)
                        result = self.results.publish(
                            key,
                            temporal_result(self, key, midpoint.result, after.result),
                        )
                        self.ledger.bump(_shared_keys.TILE_SCHEDULER_MIDPOINT_HITS)
                        return result
                    finally:
                        after.close()
                finally:
                    midpoint.close()
        self.ledger.bump(
            _execution_keys.TILE_SCHEDULER_DIRECT_REQUESTS
            if children is None
            else "tile_scheduler_fused_requests"
        )
        return self.complete_direct(key, checked_miss=True)

    def point(
        self,
        action: FieldCellActionID,
        source: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
        coordinate: int,
        *,
        _application: int | None = None,
        boundaries: BoundaryTileOperands = EMPTY_BOUNDARY_TILES,
        fusion: FusedBoundaryContract | None = None,
    ) -> int:
        self._require_physical_scheduler()
        from number_compiler.hashlife.observation.demanded_tiles import point

        return point(
            self,
            action,
            source,
            ports,
            wiring,
            coordinate,
            _application=_application,
            boundaries=boundaries,
            fusion=fusion,
        )

    def width(
        self,
        action: FieldCellActionID,
        source: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
        *,
        limit: int | None = None,
        _application: int | None = None,
        boundaries: BoundaryTileOperands = EMPTY_BOUNDARY_TILES,
        fusion: FusedBoundaryContract | None = None,
    ) -> int:
        self._require_physical_scheduler()
        from number_compiler.hashlife.observation.demanded_tiles import width

        return width(
            self,
            action,
            source,
            ports,
            wiring,
            limit=limit,
            _application=_application,
            boundaries=boundaries,
            fusion=fusion,
        )

    def active_context(
        self,
        action: FieldCellActionID,
        tile: TileID,
        context: ChildContext,
    ) -> bool:
        from number_compiler.hashlife.tiles.tile_context import bind_context
        from number_compiler.hashlife.tiles.tile_ports import BoundPorts

        bound = bind_context(
            self,
            action,
            BoundPorts(context.ports, context.wiring, context.boundaries),
        )
        return self.adapter.output_active(action, tile, bound.ports, bound.wiring)

    def prefix_active(
        self,
        action: FieldCellActionID,
        source: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
        limit: int,
        boundaries: BoundaryTileOperands = EMPTY_BOUNDARY_TILES,
    ) -> bool:
        from number_compiler.hashlife.observation.demanded_tiles import prefix_active

        return prefix_active(self, action, source, ports, wiring, limit, boundaries)

    def application(
        self,
        action: FieldCellActionID,
        source: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
    ) -> TileApplication:
        from number_compiler.hashlife.execution.tile_application import TileApplication
        from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey

        self._require_physical_scheduler()
        key = PoweredResultKey(action, source, ports, wiring)
        found = self.lookup_execution_key(key)
        identity = self._next_application
        self._next_application += 1
        try:
            return TileApplication(
                self,
                identity,
                action,
                source,
                ports,
                wiring,
                found,
                _seal=_APPLICATION_SEAL,
            )
        except BaseException:
            if found is not None:
                found.close()
            raise


__all__ = [
    "CausalSchedulerAuditOwners",
    "TileScheduler",
    "TileSchedulerAuditSnapshot",
]
