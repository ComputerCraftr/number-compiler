"""Scheduler-issued applications and their demanded-result leases."""

from __future__ import annotations

from typing import TYPE_CHECKING, Self

from number_compiler.arithmetic.contracts.exact_tree_context import source_reads_only
from number_compiler.hashlife.execution.tile_scheduler_frames import (
    _APPLICATION_SEAL,
)
from number_compiler.resources.metric_keys import shared as _shared_keys

if TYPE_CHECKING:
    from number_compiler.hashlife.actions.field_actions import FieldCellActionID
    from number_compiler.hashlife.execution.tile_causal_interfaces import (
        CausalInterfacePayload,
    )
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
    from number_compiler.hashlife.tiles.tile_ports import (
        ResultWiring,
    )
    from number_compiler.hashlife.tiles.tile_result_records import (
        CompletedResult,
        PoweredResultKey,
    )
    from number_compiler.hashlife.tiles.tile_results import (
        ResultLease,
    )
    from number_compiler.hashlife.tiles.tiles import TileID


class TileApplication:
    __slots__ = (
        "__weakref__",
        "_closed",
        "_input",
        "_root",
        "action",
        "identity",
        "ports",
        "scheduler",
        "wiring",
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
        import number_compiler.hashlife.execution.tile_scheduler_physical_imports as impl

        if _seal is not _APPLICATION_SEAL:
            raise TypeError("tile applications must be issued by their scheduler")
        from number_compiler.hashlife.execution.tile_scheduler import TileScheduler

        if type(scheduler) is not TileScheduler:
            raise TypeError("tile application requires the canonical scheduler")
        if type(identity) is not int or not 0 <= identity < scheduler._next_application:
            raise ValueError("tile application has an invalid scoped identity")
        key = impl.PoweredResultKey(action, source, ports, wiring)
        scheduler._validate_execution_key(key)
        if root is not None:
            if (
                type(root) is not impl.ResultLease
                or root._issuer is not scheduler.results
            ):
                raise ValueError("tile application has a foreign completed root")
            _ = root.result
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
        import number_compiler.hashlife.execution.tile_scheduler_physical_imports as impl

        return impl.application_source(self)

    def validate_execution(self) -> None:
        import number_compiler.hashlife.execution.tile_scheduler_physical_imports as impl

        key = impl.PoweredResultKey(self.action, self.source, self.ports, self.wiring)
        self.scheduler.results._validate_base(key.action, key.input, key.wiring)
        self.scheduler._validate_execution_context(key)

    def _cached_root(self) -> ResultLease | None:
        import number_compiler.hashlife.execution.tile_scheduler_physical_imports as impl

        key = impl.PoweredResultKey(self.action, self.source, self.ports, self.wiring)
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
        import number_compiler.hashlife.execution.tile_scheduler_physical_imports as impl

        root = self._root
        if root is None:
            return None
        if (
            type(root) is not impl.ResultLease
            or root._issuer is not self.scheduler.results
        ):
            raise ValueError("tile application has a foreign completed root")
        if root._key != key:
            raise ValueError("tile application root belongs to another request")
        _ = root.result
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
            self.scheduler.ledger.bump(_shared_keys.TILE_SCHEDULER_DEMAND_PARENT_HITS)
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
            self.scheduler.ledger.bump(_shared_keys.TILE_SCHEDULER_DEMAND_PARENT_HITS)
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
        import number_compiler.hashlife.execution.tile_scheduler_physical_imports as impl

        found = self._cached_root()
        if found is None:
            key = impl.PoweredResultKey(
                self.action, self.source, self.ports, self.wiring
            )
            found = impl.complete_clock(self.scheduler, key)
            if found is not None:
                self._adopt_root(found)
        if found is not None:
            return impl.interface_payload_from_completed(
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
        import number_compiler.hashlife.execution.tile_scheduler_physical_imports as impl

        if type(self._closed) is not bool:
            raise ValueError("malformed tile application")
        if not self._closed:
            _ = self.source
            key = impl.PoweredResultKey(
                self.action, self.source, self.ports, self.wiring
            )
            if self._root is not None:
                self._validate_root(key)
            self.scheduler._applications.unregister(self)
            self._closed = True

    def __enter__(self) -> Self:
        _ = self.source
        return self

    def __exit__(self, *_exception: object) -> None:
        self.close()
