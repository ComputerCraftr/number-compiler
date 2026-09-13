"""Charged O(1) authority checks for issued tile applications."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass, replace
from sys import is_finalizing
from typing import TYPE_CHECKING
from weakref import ReferenceType, ref

from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
from number_compiler.hashlife.tiles.tiles import TileLease
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_scheduler import (
        TileApplication,
        TileScheduler,
    )
    from number_compiler.hashlife.tiles.tile_results import ResultLease
    from number_compiler.hashlife.tiles.tiles import TileArena, TileID


@dataclass(slots=True)
class _TileApplicationCleanup:
    """Exact leases released when one application closes or expires."""

    application: ReferenceType[TileApplication]
    source: TileLease
    source_id: int
    root: ResultLease | None
    admitted: PoweredResultKey

    def __post_init__(self) -> None:
        from number_compiler.hashlife.tiles.tile_results import ResultLease

        if type(self.admitted) is not PoweredResultKey:
            raise TypeError("application cleanup requires its admitted binding")
        if type(self.application) is not ReferenceType:
            raise TypeError("application cleanup requires one weak occurrence")
        if type(self.source_id) is not int or self.source_id < 0:
            raise ValueError(
                "application cleanup requires its original source lease ID"
            )
        if type(self.source) is not TileLease:
            raise TypeError("application cleanup requires one source lease")
        if self.root is not None and type(self.root) is not ResultLease:
            raise TypeError("application cleanup requires one completed root lease")


class TileApplicationRegistry:
    """A charged identity index into the ledger's weak execution roots."""

    def __init__(self, scheduler: TileScheduler, prefix: str) -> None:
        from number_compiler.hashlife.execution.tile_scheduler import TileScheduler

        if type(scheduler) is not TileScheduler:
            raise TypeError("tile application registry requires its scheduler")
        ledger = scheduler.ledger
        if type(ledger) is not ResourceLedger:
            raise TypeError("tile application registry requires one resource ledger")
        self.ledger = ledger
        self._scheduler = ref(scheduler)
        self.owner = ledger.register(
            prefix + "-applications", "tile_application_registry"
        )
        self.records: LedgerDict[int, _TileApplicationCleanup] = ledger.make_dict(
            self.owner, nodes_per_entry=8
        )
        ledger.register_container(
            self.owner,
            self.records,
            node_count=lambda: 8 * len(self.records),
            payloads=self.records.items,
        )

    def register(
        self, application: TileApplication, admitted: PoweredResultKey
    ) -> None:
        """Publish one issued application without retaining the application."""
        from number_compiler.hashlife.execution.tile_scheduler import TileApplication

        if type(application) is not TileApplication:
            raise TypeError("application registry requires an exact tile application")
        identity = application.identity
        if type(identity) is not int or identity < 0:
            raise ValueError("application registry requires an exact scoped identity")
        if application.scheduler.ledger is not self.ledger:
            raise ValueError("tile application belongs to another execution ledger")
        if identity in self.records:
            raise ValueError("tile application identity was already issued")
        validate_application_issuer(application)
        registry = ref(self)
        finalizing = is_finalizing

        def expire(reference: ReferenceType[TileApplication]) -> None:
            if finalizing():
                return
            current = registry()
            if current is not None:
                current._expire(identity, reference)

        cleanup = _TileApplicationCleanup(
            ref(application, expire),
            application._input,
            application._input._id,
            application._root,
            # Copy scoped handles as well as wiring: a forged in-place edit of
            # an application handle must not also rewrite its admission record.
            PoweredResultKey(
                replace(admitted.action),
                replace(admitted.input),
                admitted.ports,
                replace(admitted.wiring, signature=replace(admitted.wiring.signature)),
            ),
        )
        self.ledger.reserve(self.owner, entries=1, nodes=8)
        try:
            self.records[identity] = cleanup
        except BaseException:
            self.records.pop(identity, None)
            self.ledger.release(self.owner, entries=1, nodes=8)
            raise

    def application(self, identity: int) -> TileApplication:
        """Return the one live issued application for an exact scoped ID."""
        from number_compiler.hashlife.execution.tile_scheduler import TileApplication

        if type(identity) is not int or identity < 0:
            raise ValueError("tile application has an invalid scoped identity")
        cleanup = self.records.get(identity)
        if type(cleanup) is not _TileApplicationCleanup:
            raise ValueError("tile application identity is stale or unpublished")
        cleanup.__post_init__()
        application = cleanup.application()
        if (
            type(application) is not TileApplication
            or type(application.identity) is not int
            or application.identity != identity
            or not 0 <= identity < application.scheduler._next_application
            or application.scheduler._applications is not self
            or application.scheduler.ledger is not self.ledger
            or type(application._closed) is not bool
            or application._closed
            or cleanup.source is not application._input
            or type(application._input._id) is not int
            or application._input._id != cleanup.source_id
        ):
            raise ValueError("tile application identity is stale or unpublished")
        if cleanup.root is not application._root:
            raise ValueError(
                "tile application completed root belongs to another request"
            )
        if (
            type(application._input) is not TileLease
            or application._input._arena is not application.scheduler.tiles
        ):
            raise ValueError("tile application has a foreign source lease")
        source = application._input.tile
        if cleanup.root is not None:
            if cleanup.root._issuer is not application.scheduler.results:
                raise ValueError("tile application has a foreign completed root")
            cleanup.root.result
        validate_admitted_binding(application, cleanup.admitted, source)
        return application

    def replace_root(
        self,
        application: TileApplication,
        root: ResultLease,
    ) -> None:
        """Journal a newly retained completed root before exposing it."""
        from number_compiler.hashlife.tiles.tile_results import ResultLease

        if self.application(application.identity) is not application:
            raise ValueError("tile application registry contains another occurrence")
        if (
            type(root) is not ResultLease
            or root._issuer is not application.scheduler.results
        ):
            raise ValueError("tile application has a foreign completed root")
        root.result
        previous = self.records[application.identity]
        if previous.root is not None:
            raise ValueError("tile application already owns a completed root")
        previous.root = root
        self.ledger.note_store_mutation()

    def _dispose(self, identity: int, cleanup: _TileApplicationCleanup) -> None:
        """Remove one binding and release every index-owned application root."""
        if self.records.get(identity) is not cleanup:
            raise ValueError("tile application cleanup binding changed")
        scheduler = self._scheduler()
        if scheduler is not None:
            scheduler._release_pins(identity)
        try:
            self.records.pop(identity)
        except BaseException:
            if identity not in self.records:
                self.records[identity] = cleanup
            raise
        error: BaseException | None = None
        for lease in (cleanup.root, cleanup.source):
            try:
                if lease is not None:
                    lease.close()
            except BaseException as caught:
                if error is None:
                    error = caught
        self.ledger.release(self.owner, entries=1, nodes=8)
        if error is not None:
            raise error

    def _expire(
        self,
        identity: int,
        reference: ReferenceType[TileApplication],
    ) -> None:
        cleanup = self.records.get(identity)
        if (
            type(cleanup) is _TileApplicationCleanup
            and cleanup.application is reference
        ):
            self._dispose(identity, cleanup)

    def unregister(self, application: TileApplication) -> None:
        """Remove exactly one live binding without recycling its identity."""
        if self.application(application.identity) is not application:
            raise ValueError("tile application registry contains another occurrence")
        self._dispose(application.identity, self.records[application.identity])


def audit_tile_application_registry(
    registry: TileApplicationRegistry,
    containers: Mapping[int, object],
) -> tuple[set[int], set[tuple[int, int]]]:
    """Independently reconcile weak application bindings and their account."""
    from number_compiler.hashlife.execution.tile_scheduler import TileApplication

    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    inventory = {item.owner: item for item in registry.ledger.inventory()}
    account = inventory.get(registry.owner)
    valid_store = (
        containers.get(registry.owner) is registry.records
        and account is not None
        and account.entries == len(registry.records)
        and account.observed_entries == len(registry.records)
        and account.nodes == 8 * len(registry.records)
        and account.observed_nodes == 8 * len(registry.records)
    )
    scheduler = registry._scheduler()
    for identity, cleanup in registry.records.items():
        valid = (
            type(identity) is int
            and identity >= 0
            and type(cleanup) is _TileApplicationCleanup
        )
        try:
            cleanup.__post_init__()
            application = cleanup.application()
            valid &= (
                type(application) is TileApplication
                and type(application.identity) is int
                and application.identity == identity
                and 0 <= identity < application.scheduler._next_application
                and application.scheduler._applications is registry
                and application.scheduler.ledger is registry.ledger
                and type(application._closed) is bool
                and not application._closed
                and type(application._input) is TileLease
                and application._input._arena is application.scheduler.tiles
                and cleanup.source is application._input
                and type(application._input._id) is int
                and application._input._id == cleanup.source_id
                and cleanup.root is application._root
                and scheduler is application.scheduler
            )
            if application is None:
                raise ValueError("tile application reference expired")
            source = application._input.tile
            if cleanup.root is not None:
                valid &= cleanup.root._issuer is application.scheduler.results
                cleanup.root.result
            validate_application_issuer(application)
            validate_admitted_binding(application, cleanup.admitted, source)
        except (AttributeError, KeyError, TypeError, ValueError):
            valid = False
        if valid:
            approved.update(
                (
                    id(identity),
                    id(cleanup),
                    id(cleanup.application),
                    id(cleanup.source),
                    id(cleanup.admitted),
                    id(cleanup.admitted.action),
                    id(cleanup.admitted.input),
                    id(cleanup.admitted.wiring),
                    id(cleanup.admitted.wiring.signature),
                )
            )
            if cleanup.root is not None:
                approved.add(id(cleanup.root))
        else:
            invalid.add((registry.owner, id(identity)))
    if valid_store and not invalid:
        approved.update((id(registry), id(registry.records)))
    elif not valid_store:
        invalid.add((registry.owner, id(registry.records)))
    return approved, invalid


def validate_admitted_binding(
    application: TileApplication,
    admitted: PoweredResultKey,
    source: TileID,
) -> None:
    """Reuse an immutable port tuple only under its original issued contract."""
    if (
        application.action != admitted.action
        or source != admitted.input
        or application.ports is not admitted.ports
        or application.wiring != admitted.wiring
    ):
        raise ValueError("tile application differs from its admitted binding")


def validate_application_issuer(application: TileApplication) -> None:
    reference = application.scheduler.ledger._execution_roots.get(id(application))
    if reference is None or reference() is not application:
        raise ValueError("tile application was not issued by its execution ledger")


def application_by_id(scheduler: TileScheduler, identity: int) -> TileApplication:
    """Resolve a scheduler-scoped application without walking execution roots."""
    return scheduler._applications.application(identity)


def application_source(application: TileApplication) -> TileID:
    """Return an issued application's live source without scanning the registry."""
    validate_application_issuer(application)
    if type(application._closed) is not bool or application._closed:
        raise ValueError("closed tile application")
    if (
        type(application.identity) is not int
        or not 0 <= application.identity < application.scheduler._next_application
    ):
        raise ValueError("tile application has an invalid scoped identity")
    if (
        application.scheduler._applications.application(application.identity)
        is not application
    ):
        raise ValueError("tile application registry contains another occurrence")
    return application._input.tile


def validate_application_dependencies(
    registry: TileApplicationRegistry,
    ledger: ResourceLedger,
    tiles: TileArena,
    identity: int,
) -> TileApplication:
    """Authenticate an application ID against one exact dependency store."""
    if type(registry) is not TileApplicationRegistry:
        raise TypeError("application dependency requires its scheduler registry")
    if registry.ledger is not ledger:
        raise ValueError("application dependency belongs to another execution ledger")
    application = registry.application(identity)
    if application.scheduler.tiles is not tiles:
        raise ValueError("application dependency belongs to another tile arena")
    return application


__all__ = [
    "TileApplicationRegistry",
    "audit_tile_application_registry",
    "application_by_id",
    "application_source",
    "validate_application_dependencies",
    "validate_application_issuer",
]
