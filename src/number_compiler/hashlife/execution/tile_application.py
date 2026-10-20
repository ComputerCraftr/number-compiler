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
    from number_compiler.resources.tile_runtime_audit_contracts import (
        TileApplicationAuditSnapshot,
    )


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
        from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
        from number_compiler.hashlife.tiles.tile_results import (
            ResultLease as ResultLeaseType,
        )

        if _seal is not _APPLICATION_SEAL:
            raise TypeError("tile applications must be issued by their scheduler")
        from number_compiler.hashlife.execution.tile_scheduler import TileScheduler

        if type(scheduler) is not TileScheduler:
            raise TypeError("tile application requires the canonical scheduler")
        scheduler.validate_application_identity(identity)
        key = PoweredResultKey(action, source, ports, wiring)
        scheduler.validate_execution_key(key)
        if root is not None:
            if (
                type(root) is not ResultLeaseType
                or root.audit_snapshot().issuer is not scheduler.results
            ):
                raise ValueError("tile application has a foreign completed root")
            _ = root.result
            if root.audit_snapshot().key != key:
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
            scheduler.register_application(self, key)
        except BaseException:
            self._input.close()
            raise

    @property
    def source(self) -> TileID:
        from number_compiler.hashlife.execution.tile_application_authority import (
            application_source,
        )

        return application_source(self)

    def audit_snapshot(self) -> TileApplicationAuditSnapshot:
        """Expose issued application bindings to read-only resource auditors."""
        from number_compiler.resources.tile_runtime_audit_contracts import (
            TileApplicationAuditSnapshot,
        )

        return TileApplicationAuditSnapshot(
            self.scheduler,
            self.identity,
            self.action,
            self.ports,
            self.wiring,
            self._input,
            self._root,
            self._closed,
        )

    def validate_execution(self) -> None:
        from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey

        key = PoweredResultKey(self.action, self.source, self.ports, self.wiring)
        self.scheduler.results.validate_base(key.action, key.input, key.wiring)
        self.scheduler.validate_execution_context(key)

    def cached_execution_root(self) -> ResultLease | None:
        from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey

        key = PoweredResultKey(self.action, self.source, self.ports, self.wiring)
        root = self._validate_root(key)
        if root is not None:
            self.scheduler.validate_execution_key(key)
            return root
        found = self.scheduler.lookup_execution_key(key)
        if found is not None:
            self._adopt_root(found)
        return found

    def _adopt_root(self, root: ResultLease) -> None:
        try:
            self.scheduler.replace_application_root(self, root)
        except BaseException:
            root.close()
            raise
        self._root = root
        self.scheduler.release_application_pins(self.identity)

    def _validate_root(self, key: PoweredResultKey) -> ResultLease | None:
        from number_compiler.hashlife.tiles.tile_results import (
            ResultLease as ResultLeaseType,
        )

        root = self._root
        if root is None:
            return None
        if (
            type(root) is not ResultLeaseType
            or root.audit_snapshot().issuer is not self.scheduler.results
        ):
            raise ValueError("tile application has a foreign completed root")
        if root.audit_snapshot().key != key:
            raise ValueError("tile application root belongs to another request")
        _ = root.result
        return root

    def complete(self) -> CompletedResult:
        found = self.cached_execution_root()
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
        found = self.cached_execution_root()
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
        found = self.cached_execution_root()
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
        from number_compiler.hashlife.execution.tile_causal_interfaces import (
            interface_payload_from_completed,
        )
        from number_compiler.hashlife.execution.tile_clock_dispatch import (
            complete_clock,
        )
        from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey

        found = self.cached_execution_root()
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
            engine.initial_state(self.action, 0, self.ports[0]),
            engine.initial_state(self.action, 1, self.ports[1]),
            application=self.identity,
        )

    def close(self) -> None:
        from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey

        if type(self._closed) is not bool:
            raise ValueError("malformed tile application")
        if not self._closed:
            _ = self.source
            key = PoweredResultKey(self.action, self.source, self.ports, self.wiring)
            if self._root is not None:
                self._validate_root(key)
            self.scheduler.unregister_application(self)
            self._closed = True

    def __enter__(self) -> Self:
        _ = self.source
        return self

    def __exit__(self, *_exception: object) -> None:
        self.close()
