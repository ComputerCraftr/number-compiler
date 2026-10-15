from __future__ import annotations

from typing import TYPE_CHECKING, Self

from number_compiler.hashlife.execution.source_bound_mixin import (
    SourceBoundImageMixin,
)
from number_compiler.hashlife.execution.tile_application import (
    TileApplication,
)
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
    from number_compiler.hashlife.execution.tile_execution_adapter import (
        TileExecutionAdapter,
    )
    from number_compiler.hashlife.tiles.ordered_boolean_support import (
        OrderedBooleanSupportArena,
    )
    from number_compiler.hashlife.tiles.tile_context import (
        ChildContext,
        PrimitiveTileResult,
        ResultSemantics,
        TemporalCocycle,
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
    from number_compiler.resources.stores import LedgerDict


class TileScheduler(SourceBoundImageMixin):
    """One iterative complete-result and demand-observation executor."""

    def __init__(
        self,
        tiles: TileArena,
        results: CompletedResultArena,
        adapter: TileExecutionAdapter,
    ) -> None:
        import number_compiler.hashlife.execution.tile_scheduler_physical_imports as impl

        self._source_only = False
        if (
            type(tiles) is not impl.TileArena
            or type(results) is not impl.CompletedResultArena
        ):
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
        self._applications = impl.TileApplicationRegistry(self, prefix)
        self._source_images = None
        self._causal_dependencies = impl.TileDependencyLeases(
            self.ledger,
            self.tiles,
            prefix,
            self._applications,
        )
        self._causal_workspace = impl.CausalSpatialWorkspace(self.ledger, prefix)
        self._causal_tasks = impl.CausalTaskWorkspace(self.ledger, prefix)
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
    def physical_supports(self) -> OrderedBooleanSupportArena:
        import number_compiler.hashlife.execution.tile_scheduler_physical_imports as impl

        self._require_physical_scheduler()
        found = self._physical_supports
        if found is None:
            max_nodes = max(4096, self.ledger.max_nodes or 0)
            hooks = self.adapter.family_hooks
            found = (
                impl.OrderedBooleanSupportArena(
                    max_nodes=max_nodes,
                    ledger=self.ledger,
                )
                if hooks is None
                else hooks.support_arena(max_nodes, self.ledger)
            )
            self.results.attach_physical_supports(found)
            self._physical_supports = found
        return found

    def _workspace_peak(self, size: int) -> None:
        previous = self.ledger.counters.get(
            _execution_keys.TILE_SCHEDULER_WORKSPACE_PEAK, 0
        )
        if size > previous:
            self.ledger.bump(
                _execution_keys.TILE_SCHEDULER_WORKSPACE_PEAK,
                size - previous,
            )

    def _child_context(
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
        import number_compiler.hashlife.execution.tile_scheduler_physical_imports as impl

        bound = impl.bind_context(
            self, action, impl.BoundPorts(ports, wiring, boundaries)
        )
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
        if type(context) is not impl.ChildContext:
            raise TypeError("bounded child transfer returned another record")
        self.ledger.bump(_execution_keys.TILE_SCHEDULER_SIBLING_TRANSFER_EVALUATIONS)
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
        import number_compiler.hashlife.execution.tile_scheduler_physical_imports as impl

        if (
            type(application) is not int
            or not 0 <= application < self._next_application
        ):
            raise ValueError("causal pin has an invalid application identity")
        if (
            type(key) is not impl.PoweredResultKey
            or type(lease) is not impl.ResultLease
        ):
            raise TypeError("causal pins require an exact result binding")
        self.results._validate_key(key)
        key = impl.normalize_output_region(self.tiles, key)
        if lease._issuer is not self.results or lease._key != key:
            raise ValueError("causal pin result belongs to another request")
        _ = lease.result
        application_source = impl.application_by_id(self, application).source
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
            if type(found) is not impl.ResultLease or found._issuer is not self.results:
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
        boundaries: BoundaryTileOperands = EMPTY_BOUNDARY_TILES,
        fusion: FusedBoundaryContract | None = None,
    ) -> PoweredResultKey:
        import number_compiler.hashlife.execution.tile_scheduler_physical_imports as impl

        return impl.PoweredResultKey(action, source, ports, wiring, boundaries, fusion)

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
        import number_compiler.hashlife.execution.tile_scheduler_physical_imports as impl

        self.results._validate_key(root)
        source = self.tiles.resolve(root.input)
        if source.level or source.symbol is None:
            raise ValueError("leaf completion requires one canonical leaf")
        self.ledger.bump(_execution_keys.COMPLETED_RESULT_EVALUATIONS)
        interface = self.adapter.leaf_interface(
            root.action,
            root.input,
            root.wiring,
        )
        if type(interface) is not impl.LocalInterfaceID:
            raise TypeError("leaf compiler returned a noncanonical interface")
        record = self.results.interfaces.resolve(interface)
        if record.signature != root.wiring.signature:
            raise ValueError("leaf function has another port signature")
        bound = impl.bind_context(
            self,
            root.action,
            impl.BoundPorts(root.ports, root.wiring, root.boundaries),
        )
        value = self.adapter.apply_leaf(interface, bound.ports)
        if type(value) is not impl.PrimitiveTileResult:
            raise TypeError("leaf function returned an incomplete result")
        if value.semantics.outgoing != interface:
            raise ValueError("leaf result discarded its compiled interface")
        cocycle = self.adapter.action_cocycle(root.action)
        if type(cocycle) is not impl.TemporalCocycle:
            raise TypeError("field action returned a noncanonical cocycle")
        observed = self.adapter.leaf_observation(
            root.action,
            root.input,
            interface,
            bound.ports,
        )
        if type(observed) is not impl.TemporalCocycle or observed.physical_ticks:
            raise TypeError("leaf observation returned an invalid cocycle delta")
        semantics = impl.ResultSemantics(
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
            semantics = impl.ResultSemantics(
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

    def _complete_direct(
        self, root: PoweredResultKey, *, checked_miss: bool = False
    ) -> ResultLease:
        import number_compiler.hashlife.execution.tile_scheduler_physical_imports as impl

        frames: list[_DirectFrame] = [_DirectFrame(root, checked_miss=checked_miss)]
        values: list[ResultLease] = []
        try:
            while frames:
                self._workspace_peak(len(frames) + len(values))
                self.ledger.bump(_execution_keys.TILE_SCHEDULER_FRAMES)
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
                    self.ledger.bump(_execution_keys.COMPLETED_RESULT_EVALUATIONS)
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
                        impl.validate_midpoint_exits(
                            frame.left_context,
                            frame.right_context,
                            left_result,
                            right_result,
                        )
                    bound = impl.bind_context(
                        self,
                        key.action,
                        impl.BoundPorts(key.ports, key.wiring, key.boundaries),
                    )
                    semantics = self.adapter.join_semantics(
                        key.action,
                        key.input,
                        bound.ports,
                        bound.wiring,
                        left_result,
                        right_result,
                    )
                    if type(semantics) is not impl.ResultSemantics:
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
        import number_compiler.hashlife.execution.tile_scheduler_physical_imports as impl

        self._require_physical_scheduler()
        validator = getattr(self.adapter, "validate_wiring", None)
        if validator is not None:
            validator(action, wiring)
        key = self._key(action, source, ports, wiring, boundaries, fusion)
        found = self._lookup_execution_key(key)
        if found is not None:
            self.ledger.bump(_execution_keys.TILE_SCHEDULER_PARENT_EARLY_HITS)
            return found
        clock = impl.complete_clock(self, key)
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
            self.ledger.bump(_execution_keys.TILE_SCHEDULER_TEMPORAL_COMPLETE_REQUESTS)
            from number_compiler.hashlife.execution.tile_temporal import (
                complete_temporal,
            )

            return complete_temporal(self, key)
        if children is not None:
            producer = impl.before_context(self, key, children[0])
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
                    context = impl.after_context(
                        self, key, children[1], midpoint.result
                    )
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
                        self.ledger.bump(_execution_keys.COMPLETED_RESULT_EVALUATIONS)
                        result = self.results.publish(
                            key,
                            impl.temporal_result(
                                self, key, midpoint.result, after.result
                            ),
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

    def _active_context(
        self,
        action: FieldCellActionID,
        tile: TileID,
        context: ChildContext,
    ) -> bool:
        import number_compiler.hashlife.execution.tile_scheduler_physical_imports as impl

        bound = impl.bind_context(
            self,
            action,
            impl.BoundPorts(context.ports, context.wiring, context.boundaries),
        )
        return self.adapter.output_active(action, tile, bound.ports, bound.wiring)

    def _prefix_active(
        self,
        action: FieldCellActionID,
        source: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
        limit: int,
        boundaries: BoundaryTileOperands = EMPTY_BOUNDARY_TILES,
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
        import number_compiler.hashlife.execution.tile_scheduler_physical_imports as impl

        self._require_physical_scheduler()
        key = impl.PoweredResultKey(action, source, ports, wiring)
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


_LAZY_PHYSICAL_EXPORTS = (
    "ChildContext",
    "CompletedResult",
    "PrimitiveTileResult",
    "ResultSemantics",
    "TemporalCocycle",
    "TileExecutionAdapter",
)


def __getattr__(name: str) -> object:
    if name not in _LAZY_PHYSICAL_EXPORTS:
        raise AttributeError(name)
    import number_compiler.hashlife.execution.tile_scheduler_physical_imports as impl

    return getattr(impl, name)


def __dir__() -> list[str]:
    return sorted(set(globals()) | set(_LAZY_PHYSICAL_EXPORTS))


__all__ = [
    "ChildContext",
    "PrimitiveTileResult",
    "ResultSemantics",
    "TemporalCocycle",
    "TileApplication",
    "TileExecutionAdapter",
    "TileScheduler",
]
