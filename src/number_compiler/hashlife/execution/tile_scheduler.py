"""Demand-driven execution over canonical exact future tiles."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Protocol

from number_compiler.arithmetic.contracts.exact_tree_context import source_reads_only
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.tile_application_authority import (
    TileApplicationRegistry,
    application_by_id,
    application_source,
)
from number_compiler.hashlife.execution.tile_clock_dispatch import complete_clock
from number_compiler.hashlife.execution.source_bound_images import (
    SourceBoundImageMixin,
)
from number_compiler.hashlife.execution.tile_causal_interfaces import (
    CausalInterfacePayload,
    interface_payload_from_completed,
)
from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileOperands
from number_compiler.hashlife.tiles.tile_context import (
    ChildContext,
    PrimitiveTileResult,
    ResultSemantics,
    TemporalCocycle,
    after_context,
    before_context,
    bind_context,
    temporal_result,
    validate_midpoint_exits,
)
from number_compiler.hashlife.tiles.tile_ports import (
    BoundPorts,
    FusedBoundaryContract,
    ResultWiring,
)
from number_compiler.hashlife.tiles.tile_result_records import (
    CompletedResult,
    PoweredResultKey,
)
from number_compiler.hashlife.tiles.tile_result_validation import (
    normalize_output_region,
)
from number_compiler.hashlife.tiles.tile_results import (
    CompletedResultArena,
    ResultLease,
)
from number_compiler.hashlife.tiles.tiles import TileArena, TileID
from number_compiler.resources.causal_workspace import (
    CausalSpatialWorkspace,
    CausalTaskWorkspace,
)
from number_compiler.resources.stores import LedgerDict
from number_compiler.resources.tile_dependency_leases import TileDependencyLeases
from number_compiler.sequences.collatz.physical_support import PhysicalSupportArena


class TileExecutionAdapter(Protocol):
    """Fixed-interface family law consumed by the shared scheduler."""

    complete_via_midpoint_tiles: bool

    def validate_action(self, action: FieldCellActionID) -> None: ...

    def validate_wiring(
        self,
        action: FieldCellActionID,
        wiring: ResultWiring,
    ) -> None: ...

    def action_children(
        self,
        action: FieldCellActionID,
    ) -> tuple[FieldCellActionID, FieldCellActionID] | None: ...

    def action_cocycle(self, action: FieldCellActionID) -> TemporalCocycle: ...

    def leaf_observation(
        self,
        action: FieldCellActionID,
        source: TileID,
        interface: LocalInterfaceID,
        ports: tuple[int, ...],
    ) -> TemporalCocycle: ...

    def leaf_interface(
        self,
        action: FieldCellActionID,
        source: TileID,
        wiring: ResultWiring,
    ) -> LocalInterfaceID: ...

    def apply_leaf(
        self,
        interface: LocalInterfaceID,
        ports: tuple[int, ...],
    ) -> PrimitiveTileResult: ...

    def child_context(
        self,
        action: FieldCellActionID,
        parent: TileID,
        left: TileID,
        right: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
        side: int,
    ) -> ChildContext: ...

    def join_semantics(
        self,
        action: FieldCellActionID,
        parent: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
        left: CompletedResult,
        right: CompletedResult,
    ) -> ResultSemantics: ...

    def temporal_before_context(
        self,
        action: FieldCellActionID,
        before: FieldCellActionID,
        original_ports: tuple[int, ...],
        wiring: ResultWiring,
    ) -> ChildContext: ...

    def temporal_after_context(
        self,
        action: FieldCellActionID,
        after: FieldCellActionID,
        before_result: CompletedResult,
        original_ports: tuple[int, ...],
        wiring: ResultWiring,
    ) -> ChildContext: ...

    def temporal_semantics(
        self,
        action: FieldCellActionID,
        before: CompletedResult,
        after: CompletedResult,
        original_ports: tuple[int, ...],
        wiring: ResultWiring,
    ) -> ResultSemantics: ...

    def output_active(
        self,
        action: FieldCellActionID,
        source: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
    ) -> bool: ...


@dataclass(slots=True)
class _DirectFrame:
    key: PoweredResultKey
    stage: int = 0
    left_context: ChildContext | None = None
    right_context: ChildContext | None = None
    checked_miss: bool = False


_APPLICATION_SEAL = object()


class TileScheduler(SourceBoundImageMixin):
    """One iterative complete-result and demand-observation executor."""

    def __init__(
        self,
        tiles: TileArena,
        results: CompletedResultArena,
        adapter: TileExecutionAdapter,
    ) -> None:
        if type(tiles) is not TileArena or type(results) is not CompletedResultArena:
            raise TypeError("tile scheduling requires canonical tile and result arenas")
        if results.tiles is not tiles or results.ledger is not tiles.ledger:
            raise ValueError("tile scheduler stores belong to another index")
        if getattr(adapter, "ledger", tiles.ledger) is not tiles.ledger:
            raise ValueError("tile adapter belongs to another index")
        if results._causal_tasks is not None:
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
        self._physical_supports: PhysicalSupportArena | None = None
        self.results.attach_causal_tasks(self._causal_tasks)
        if not self.ledger.counters.get("tile_causal_accounting_version"):
            self.ledger.bump("tile_causal_accounting_version", 2)
        self._next_application = 0
        self.ledger.register_execution_root(self)

    @property
    def physical_supports(self) -> PhysicalSupportArena:
        found = self._physical_supports
        if found is None:
            found = PhysicalSupportArena(
                max_nodes=max(4096, self.ledger.max_nodes or 0),
                ledger=self.ledger,
            )
            self.results.attach_physical_supports(found)
            self._physical_supports = found
        return found

    def _workspace_peak(self, size: int) -> None:
        previous = self.ledger.counters.get("tile_scheduler_workspace_peak", 0)
        if size > previous:
            self.ledger.bump("tile_scheduler_workspace_peak", size - previous)

    def _child_context(
        self,
        action: FieldCellActionID,
        parent: TileID,
        left: TileID,
        right: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
        side: int,
        boundaries: BoundaryTileOperands = BoundaryTileOperands(),
    ) -> ChildContext:
        bound = bind_context(self, action, BoundPorts(ports, wiring, boundaries))
        self.ledger.bump("tile_scheduler_sibling_transfer_requests")
        context = self.adapter.child_context(
            action,
            parent,
            left,
            right,
            bound.ports,
            bound.wiring,
            side,
        )
        if type(context) is not ChildContext:
            raise TypeError("bounded child transfer returned another record")
        self.ledger.bump("tile_scheduler_sibling_transfer_evaluations")
        return context

    def _pin(
        self,
        application: int,
        key: PoweredResultKey,
        lease: ResultLease,
    ) -> None:
        from number_compiler.hashlife.execution.tile_result_pinning import pin_result

        pin_result(self, application, key, lease)

    def _pin_causal(
        self,
        application: int,
        key: PoweredResultKey,
        lease: ResultLease,
    ) -> None:
        if (
            type(application) is not int
            or not 0 <= application < self._next_application
        ):
            raise ValueError("causal pin has an invalid application identity")
        if type(key) is not PoweredResultKey or type(lease) is not ResultLease:
            raise TypeError("causal pins require an exact result binding")
        self.results._validate_key(key)
        key = normalize_output_region(self.tiles, key)
        if lease._issuer is not self.results or lease._key != key:
            raise ValueError("causal pin result belongs to another request")
        lease.result
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
            if type(found) is not ResultLease or found._issuer is not self.results:
                raise ValueError("causal result pin contains a foreign lease")
            found.result
            expected = {(application, tile) for tile in dependencies}
            self.ledger.bump("tile_causal_pin_dependency_checks", len(expected))
            if not all(item in self._causal_dependencies.records for item in expected):
                raise ValueError("causal result pin lost an exact input dependency")
            if found is not lease:
                lease.close()
            self.ledger.bump("tile_causal_pin_early_hits")
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
        self.ledger.bump("tile_scheduler_demanded_result_pins")

    def _release_pins(self, application: int) -> None:
        from number_compiler.hashlife.execution.tile_result_pinning import (
            release_result_pins,
        )

        release_result_pins(self, application)
        self._causal_dependencies.release_application(application)

    @staticmethod
    def _key(
        action: FieldCellActionID,
        source: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
        boundaries: BoundaryTileOperands = BoundaryTileOperands(),
        fusion: FusedBoundaryContract | None = None,
    ) -> PoweredResultKey:
        return PoweredResultKey(action, source, ports, wiring, boundaries, fusion)

    def _children(
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

    def _validate_execution_key(self, key: PoweredResultKey) -> None:
        self.results._validate_key(key)
        self._validate_execution_context(key)

    def _validate_execution_context(self, key: PoweredResultKey) -> None:
        from number_compiler.hashlife.execution.tile_execution_validation import (
            validate_execution_context,
        )

        validate_execution_context(self, key)

    def _lookup_execution_key(self, key: PoweredResultKey) -> ResultLease | None:
        return self.results.lookup(
            key, validate_context=self._validate_execution_context
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

    def _complete_leaf(self, root: PoweredResultKey) -> ResultLease:
        self.results._validate_key(root)
        source = self.tiles.resolve(root.input)
        if source.level or source.symbol is None:
            raise ValueError("leaf completion requires one canonical leaf")
        self.ledger.bump("completed_result_evaluations")
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
            self, root.action, BoundPorts(root.ports, root.wiring, root.boundaries)
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
        self.ledger.bump("tile_scheduler_leaf_function_applications")
        return self._publish_leaf(root, value.symbol, semantics)

    def _complete_direct(
        self, root: PoweredResultKey, *, checked_miss: bool = False
    ) -> ResultLease:
        frames: list[_DirectFrame] = [_DirectFrame(root, checked_miss=checked_miss)]
        values: list[ResultLease] = []
        try:
            while frames:
                self._workspace_peak(len(frames) + len(values))
                self.ledger.bump("tile_scheduler_frames")
                frame = frames.pop()
                key = frame.key
                if frame.stage == 0:
                    if frame.checked_miss:
                        self._validate_execution_key(key)
                        found = None
                    else:
                        found = self._lookup_execution_key(key)
                    if found is not None:
                        values.append(found)
                        continue
                    node = self.tiles.resolve(key.input)
                    if not node.level:
                        values.append(self._complete_leaf(key))
                        continue
                    self.ledger.bump("completed_result_evaluations")
                    if node.left is None or node.right is None:
                        raise ValueError("malformed canonical parent")
                    left_context = self._child_context(
                        key.action,
                        key.input,
                        node.left,
                        node.right,
                        key.ports,
                        key.wiring,
                        0,
                        key.boundaries,
                    )
                    right_context = self._child_context(
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
                            self._key(
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
                            self._key(
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
                    self.ledger.bump("tile_scheduler_spatial_compositions")
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
        boundaries: BoundaryTileOperands = BoundaryTileOperands(),
        fusion: FusedBoundaryContract | None = None,
    ) -> ResultLease:
        # Reject unsupported public wiring before consulting the result store.
        # The store still performs full key/context admission on every lookup.
        validator = getattr(self.adapter, "validate_wiring", None)
        if validator is not None:
            validator(action, wiring)
        key = self._key(action, source, ports, wiring, boundaries, fusion)
        found = self._lookup_execution_key(key)
        if found is not None:
            self.ledger.bump("tile_scheduler_parent_early_hits")
            return found
        clock = complete_clock(self, key)
        if clock is not None:
            return clock
        from number_compiler.hashlife.execution.tile_causal_entry import causal_complete

        causal = causal_complete(self, key)
        if causal is not None:
            return causal
        children = self._children(action)
        if (
            children is not None
            and getattr(
                self.adapter,
                "complete_via_midpoint_tiles",
                False,
            )
            is True
        ):
            self.ledger.bump("tile_scheduler_temporal_complete_requests")
            from number_compiler.hashlife.execution.tile_temporal import (
                complete_temporal,
            )

            return complete_temporal(self, key)
        if children is not None:
            producer = before_context(self, key, children[0])
            before_key = self._key(
                children[0],
                source,
                producer.ports,
                producer.wiring,
                producer.boundaries,
            )
            midpoint = self._lookup_execution_key(before_key)
            if midpoint is not None:
                try:
                    context = after_context(self, key, children[1], midpoint.result)
                    after = self._complete_direct(
                        self._key(
                            children[1],
                            midpoint.output,
                            context.ports,
                            context.wiring,
                            context.boundaries,
                        )
                    )
                    try:
                        self.ledger.bump("completed_result_evaluations")
                        result = self.results.publish(
                            key,
                            temporal_result(self, key, midpoint.result, after.result),
                        )
                        self.ledger.bump("tile_scheduler_midpoint_hits")
                        return result
                    finally:
                        after.close()
                finally:
                    midpoint.close()
        self.ledger.bump(
            "tile_scheduler_direct_requests"
            if children is None
            else "tile_scheduler_fused_requests"
        )
        return self._complete_direct(key, checked_miss=True)

    def point(
        self,
        action: FieldCellActionID,
        source: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
        coordinate: int,
        *,
        _application: int | None = None,
        boundaries: BoundaryTileOperands = BoundaryTileOperands(),
        fusion: FusedBoundaryContract | None = None,
    ) -> int:
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
        boundaries: BoundaryTileOperands = BoundaryTileOperands(),
        fusion: FusedBoundaryContract | None = None,
    ) -> int:
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

    def _active_context(
        self,
        action: FieldCellActionID,
        tile: TileID,
        context: ChildContext,
    ) -> bool:
        bound = bind_context(
            self, action, BoundPorts(context.ports, context.wiring, context.boundaries)
        )
        return self.adapter.output_active(action, tile, bound.ports, bound.wiring)

    def _prefix_active(
        self,
        action: FieldCellActionID,
        source: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
        limit: int,
        boundaries: BoundaryTileOperands = BoundaryTileOperands(),
    ) -> bool:
        from number_compiler.hashlife.observation.demanded_tiles import _prefix_active

        return _prefix_active(self, action, source, ports, wiring, limit, boundaries)

    def application(
        self,
        action: FieldCellActionID,
        source: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
    ) -> TileApplication:
        key = PoweredResultKey(action, source, ports, wiring)
        found = self._lookup_execution_key(key)
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


class TileApplication:
    __slots__ = tuple(
        "scheduler identity action ports wiring _input _root _closed __weakref__".split()
    )

    def __setattr__(self, name: str, value: object) -> None:
        if name in {
            "scheduler",
            "identity",
            "action",
            "ports",
            "wiring",
            "_input",
        } and hasattr(self, name):
            raise AttributeError("tile application identity is immutable")
        object.__setattr__(self, name, value)

    def __init__(
        self,
        scheduler: TileScheduler,
        identity: int,
        action: FieldCellActionID,
        source: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
        root: ResultLease | None,
        *,
        _seal: object = None,
    ) -> None:
        if _seal is not _APPLICATION_SEAL:
            raise TypeError("tile applications must be issued by their scheduler")
        if type(scheduler) is not TileScheduler:
            raise TypeError("tile application requires the canonical scheduler")
        if type(identity) is not int or not 0 <= identity < scheduler._next_application:
            raise ValueError("tile application has an invalid scoped identity")
        key = PoweredResultKey(action, source, ports, wiring)
        scheduler._validate_execution_key(key)
        if root is not None:
            if type(root) is not ResultLease or root._issuer is not scheduler.results:
                raise ValueError("tile application has a foreign completed root")
            root.result
            if root._key != key:
                raise ValueError("tile application root belongs to another request")
        self.scheduler, self.identity, self.action, self.ports, self.wiring = (
            scheduler,
            identity,
            action,
            ports,
            wiring,
        )
        self._input = scheduler.tiles.retain(source)
        self._root = root
        self._closed = False
        scheduler.ledger.register_execution_root(self)
        try:
            scheduler._applications.register(self, key)
        except BaseException:
            self._input.close()
            raise

    @property
    def source(self) -> TileID:
        return application_source(self)

    def validate_execution(self) -> None:
        key = PoweredResultKey(self.action, self.source, self.ports, self.wiring)
        self.scheduler.results._validate_base(key.action, key.input, key.wiring)
        self.scheduler._validate_execution_context(key)

    def _cached_root(self) -> ResultLease | None:
        key = PoweredResultKey(self.action, self.source, self.ports, self.wiring)
        root = self._validate_root(key)
        if root is not None:
            self.scheduler._validate_execution_key(key)
            return root
        found = self.scheduler._lookup_execution_key(key)
        if found is not None:
            self._adopt_root(found)
        return found

    def _adopt_root(self, root: ResultLease) -> None:
        try:
            self.scheduler._applications.replace_root(self, root)
        except BaseException:
            root.close()
            raise
        self._root = root
        self.scheduler._release_pins(self.identity)

    def _validate_root(self, key: PoweredResultKey) -> ResultLease | None:
        root = self._root
        if root is None:
            return None
        if type(root) is not ResultLease or root._issuer is not self.scheduler.results:
            raise ValueError("tile application has a foreign completed root")
        if root._key != key:
            raise ValueError("tile application root belongs to another request")
        root.result
        return root

    def complete(self) -> CompletedResult:
        found = self._cached_root()
        if found is None:
            completed_root = self.scheduler.complete(
                self.action,
                self.source,
                self.ports,
                self.wiring,
            )
            self._adopt_root(completed_root)
        root = self._root
        if root is None:
            raise AssertionError("completed application has no root lease")
        return root.result

    @source_reads_only
    def point(self, coordinate: int) -> int:
        if type(coordinate) is not int:
            raise TypeError("tile coordinate requires an exact integer")
        if not 0 <= coordinate < self.scheduler.tiles.resolve(self.source).width:
            raise IndexError(coordinate)
        found = self._cached_root()
        if found is not None:
            self.scheduler.ledger.bump("tile_scheduler_demand_parent_hits")
            return self.scheduler.tiles.point(found.output, coordinate)
        return self.scheduler.point(
            self.action,
            self.source,
            self.ports,
            self.wiring,
            coordinate,
            _application=self.identity,
        )

    @source_reads_only
    def width(self, limit: int | None = None) -> int:
        if limit is not None:
            if type(limit) is not int:
                raise TypeError("tile width limit requires an exact integer")
            if not 0 <= limit <= self.scheduler.tiles.resolve(self.source).width:
                raise ValueError("tile width limit lies outside the source")
        found = self._cached_root()
        if found is not None:
            self.scheduler.ledger.bump("tile_scheduler_demand_parent_hits")
            return self.scheduler.tiles.active_width(found.output, limit)
        return self.scheduler.width(
            self.action,
            self.source,
            self.ports,
            self.wiring,
            limit=limit,
            _application=self.identity,
        )

    @source_reads_only
    def interface(self) -> CausalInterfacePayload:
        found = self._cached_root()
        if found is None:
            key = PoweredResultKey(self.action, self.source, self.ports, self.wiring)
            found = complete_clock(self.scheduler, key)
            if found is not None:
                self._adopt_root(found)
        if found is not None:
            return interface_payload_from_completed(
                self.scheduler.results, found.result, self.ports
            )
        from number_compiler.hashlife.execution.tile_causal import CausalTileEngine

        engine = CausalTileEngine(self.scheduler)
        return engine.interface(
            self.action,
            self.source,
            engine._initial(self.action, 0, self.ports[0]),
            engine._initial(self.action, 1, self.ports[1]),
            application=self.identity,
        )

    def close(self) -> None:
        if type(self._closed) is not bool:
            raise ValueError("malformed tile application")
        if not self._closed:
            self.source
            key = PoweredResultKey(self.action, self.source, self.ports, self.wiring)
            if self._root is not None:
                self._validate_root(key)
            self.scheduler._applications.unregister(self)
            self._closed = True

    def __enter__(self) -> TileApplication:
        self.source
        return self

    def __exit__(self, *_exception: object) -> None:
        self.close()


__all__ = [
    "ChildContext",
    "PrimitiveTileResult",
    "ResultSemantics",
    "TemporalCocycle",
    "TileApplication",
    "TileExecutionAdapter",
    "TileScheduler",
]
