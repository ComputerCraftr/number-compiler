"""Authenticated publication of application-owned completed result leases."""

from __future__ import annotations

from typing import TYPE_CHECKING, Protocol

from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
    from number_compiler.hashlife.tiles.tile_results import (
        CompletedResultArena,
        ResultLease,
    )
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.resources.stores import LedgerDict


class ResultPinning(Protocol):
    """Owner algorithms for charged result pins and their deletion journals."""

    ledger: ResourceLedger
    results: CompletedResultArena
    _pins: LedgerDict[tuple[int, PoweredResultKey], ResultLease]
    _pin_owner: int

    def validate_pin_application(self, application: int) -> None: ...

    def pin_result(
        self,
        application: int,
        key: PoweredResultKey,
        lease: ResultLease,
    ) -> None:
        """Validate ownership before warm lookup or retained publication."""
        from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
        from number_compiler.hashlife.tiles.tile_results import ResultLease

        self.validate_pin_application(application)
        if type(key) is not PoweredResultKey or type(lease) is not ResultLease:
            raise TypeError("application pins require an exact completed result")
        self.results.validate_key(key)
        if (
            lease.audit_snapshot().issuer is not self.results
            or lease.audit_snapshot().key != key
        ):
            raise ValueError("application pin belongs to another result request")
        _ = lease.result
        binding = application, key
        found = self._pins.get(binding)
        if found is not None:
            if type(found) is not ResultLease or found.audit_snapshot().key != key:
                raise ValueError("application pin contains another result request")
            _ = found.result
            if found is not lease:
                lease.close()
            self.ledger.bump(_execution_keys.TILE_RESULT_PIN_EARLY_HITS)
            return
        reserved = False
        try:
            self.ledger.reserve(self._pin_owner, entries=1)
            reserved = True
            self._pins[binding] = lease
        except BaseException:
            self._pins.pop(binding, None)
            if reserved:
                self.ledger.release(self._pin_owner, entries=1)
            lease.close()
            raise
        self.ledger.bump(_execution_keys.TILE_SCHEDULER_DEMANDED_RESULT_PINS)

    def release_result_pins(self, application: int) -> None:
        """Release one application's result pins with retryable deletion journals."""
        if type(application) is not int or application < 0:
            raise ValueError("application pin release requires an exact identity")
        bindings = tuple(key for key in self._pins if key[0] == application)
        for binding in bindings:
            lease = self._pins[binding]
            try:
                self._pins.pop(binding)
            except BaseException:
                if binding not in self._pins:
                    self._pins[binding] = lease
                raise
            try:
                lease.close()
            except BaseException:
                if not lease.audit_snapshot().closed:
                    self._pins[binding] = lease
                else:
                    self.ledger.release(self._pin_owner, entries=1)
                raise
            self.ledger.release(self._pin_owner, entries=1)


__all__ = ["ResultPinning"]
