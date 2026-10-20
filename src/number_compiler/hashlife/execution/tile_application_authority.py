"""Charged O(1) authority checks for issued tile applications."""

from __future__ import annotations

import logging
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
    from number_compiler.hashlife.execution.tile_application import TileApplication
    from number_compiler.hashlife.execution.tile_scheduler import (
        TileScheduler,
    )
    from number_compiler.hashlife.tiles.tile_results import ResultLease
    from number_compiler.hashlife.tiles.tiles import TileArena, TileID
    from number_compiler.resources.tile_runtime_audit_contracts import (
        TileApplicationAuditSnapshot,
        TileLeaseAuditSnapshot,
    )


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
        from number_compiler.hashlife.execution.tile_application import TileApplication

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
        state = application.audit_snapshot()
        source_lease = state.input_lease
        source_state = source_lease.audit_snapshot()

        def expire(reference: ReferenceType[TileApplication]) -> None:
            if finalizing():
                return
            current = registry()
            if current is not None:
                current._expire(identity, reference)

        cleanup = _TileApplicationCleanup(
            ref(application, expire),
            source_lease,
            source_state.identity,
            state.root_lease,
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
        from number_compiler.hashlife.execution.tile_application import TileApplication

        if type(identity) is not int or identity < 0:
            raise ValueError("tile application has an invalid scoped identity")
        cleanup = self.records.get(identity)
        if type(cleanup) is not _TileApplicationCleanup:
            raise ValueError("tile application identity is stale or unpublished")
        cleanup.__post_init__()
        application, state, input_state = _application_cleanup_snapshot(cleanup)
        if (
            type(application) is not TileApplication
            or type(application.identity) is not int
            or application.identity != identity
            or not _application_has_registry_authority(application, identity, self)
            or state is None
            or type(state.closed) is not bool
            or state.closed
            or cleanup.source is not state.input_lease
            or input_state is None
            or type(input_state.identity) is not int
            or input_state.identity != cleanup.source_id
        ):
            raise ValueError("tile application identity is stale or unpublished")
        if cleanup.root is not state.root_lease:
            raise ValueError(
                "tile application completed root belongs to another request"
            )
        if (
            type(state.input_lease) is not TileLease
            or input_state.arena is not application.scheduler.tiles
        ):
            raise ValueError("tile application has a foreign source lease")
        source = state.input_lease.tile
        if cleanup.root is not None:
            if (
                cleanup.root.audit_snapshot().issuer
                is not application.scheduler.results
            ):
                raise ValueError("tile application has a foreign completed root")
            _ = cleanup.root.result
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
            or root.audit_snapshot().issuer is not application.scheduler.results
        ):
            raise ValueError("tile application has a foreign completed root")
        _ = root.result
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
            scheduler.release_application_pins(identity)
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
                logging.getLogger(__name__).debug("Lease cleanup failed", exc_info=True)
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

    def audit(
        self, containers: Mapping[int, object]
    ) -> tuple[set[int], set[tuple[int, int]]]:
        """Run the independent owner audit without exposing registry stores."""
        return audit_tile_application_registry(self, containers)

    def matches_live_applications(
        self, applications: Mapping[int, TileApplication]
    ) -> bool:
        """Check exact live identities against this registry's current bindings."""
        try:
            if set(self.records) != set(applications):
                return False
            return all(
                type(cleanup) is _TileApplicationCleanup
                and cleanup.application() is applications[identity]
                for identity, cleanup in self.records.items()
            )
        except (AttributeError, KeyError, TypeError, ValueError):
            return False

    @property
    def scheduler_owner(self) -> TileScheduler | None:
        """Return the live scheduler when it still owns this registry."""
        return self._scheduler()


def audit_tile_application_registry(
    registry: TileApplicationRegistry,
    containers: Mapping[int, object],
) -> tuple[set[int], set[tuple[int, int]]]:
    """Independently reconcile weak application bindings and their account."""
    from number_compiler.hashlife.execution.tile_application import TileApplication

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
    scheduler = registry.scheduler_owner
    for identity, cleanup in registry.records.items():
        valid = (
            type(identity) is int
            and identity >= 0
            and type(cleanup) is _TileApplicationCleanup
        )
        try:
            cleanup.__post_init__()
            application, state, input_state = _application_cleanup_snapshot(cleanup)
            root_state = (
                None
                if state is None or state.root_lease is None
                else state.root_lease.audit_snapshot()
            )
            valid &= (
                type(application) is TileApplication
                and type(application.identity) is int
                and application.identity == identity
                and _application_has_registry_authority(application, identity, registry)
                and state is not None
                and type(state.closed) is bool
                and not state.closed
                and type(state.input_lease) is TileLease
                and input_state is not None
                and input_state.arena is application.scheduler.tiles
                and cleanup.source is state.input_lease
                and type(input_state.identity) is int
                and input_state.identity == cleanup.source_id
                and cleanup.root is state.root_lease
                and scheduler is application.scheduler
            )
            if application is None:
                raise ValueError("tile application reference expired")
            if state is None:
                raise ValueError("tile application audit snapshot is missing")
            source = state.input_lease.tile
            if cleanup.root is not None:
                valid &= (
                    root_state is not None
                    and root_state.issuer is application.scheduler.results
                )
                _ = cleanup.root.result
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


def _application_has_registry_authority(
    application: TileApplication,
    identity: int,
    registry: TileApplicationRegistry,
) -> bool:
    return (
        application.scheduler.application_identity_is_live(identity)
        and application.scheduler.application_registry_is(registry)
        and application.scheduler.ledger is registry.ledger
    )


def _application_cleanup_snapshot(
    cleanup: _TileApplicationCleanup,
) -> tuple[
    TileApplication | None,
    TileApplicationAuditSnapshot | None,
    TileLeaseAuditSnapshot | None,
]:
    application = cleanup.application()
    state = None if application is None else application.audit_snapshot()
    input_state = None if state is None else state.input_lease.audit_snapshot()
    return application, state, input_state


def validate_application_issuer(application: TileApplication) -> None:
    if not application.scheduler.ledger.owns_execution_root(application):
        raise ValueError("tile application was not issued by its execution ledger")


def application_by_id(scheduler: TileScheduler, identity: int) -> TileApplication:
    """Resolve a scheduler-scoped application without walking execution roots."""
    return scheduler.application_by_id(identity)


def application_source(application: TileApplication) -> TileID:
    """Return an issued application's live source without scanning the registry."""
    validate_application_issuer(application)
    state = application.audit_snapshot()
    if type(state.closed) is not bool or state.closed:
        raise ValueError("closed tile application")
    if not application.scheduler.application_identity_is_live(application.identity):
        raise ValueError("tile application has an invalid scoped identity")
    if not application.scheduler.application_is_registered(application):
        raise ValueError("tile application registry contains another occurrence")
    return state.input_lease.tile


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
    "application_by_id",
    "application_source",
    "audit_tile_application_registry",
    "validate_application_dependencies",
    "validate_application_issuer",
]
