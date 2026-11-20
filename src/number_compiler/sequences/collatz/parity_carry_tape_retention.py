"""Ledger-owned retained records for parity roots and authenticated joins."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.owned_memo import LedgerReservation, OwnedMemo
from number_compiler.resources.reference_delta import TemporaryRootLease
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.parity_carry_tape import ParityCarryTape

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.guarded_port_join import GuardedPortJoin

_LEASE_NODE_CHARGE = 16


def parity_action_node_cost(
    _key: int, payload: tuple[ParityCarryTape, DyadicTerminalFieldAction]
) -> int:
    from sys import getsizeof

    node, action = payload
    # Size accounting is in the ledger's logical 64-bit node units, not
    # CPython's object count. Include referenced tuple/word and all
    # independently retained integer limbs, not just the action pointer.
    byte_count = (
        getsizeof(node)
        + getsizeof(node[0])
        + getsizeof(node.children)
        + getsizeof(node.word)
        + getsizeof(node.kind)
        + getsizeof(action)
        + getsizeof(action.coefficient_snapshot())
        + getsizeof(payload)
    )
    # Integral fields may alias by identity. Charging once per occurrence
    # is conservative and never omits actual retained coefficient bytes.
    byte_count += sum(getsizeof(value) for value in action.coefficient_snapshot())
    byte_count += (
        getsizeof(node.steps)
        + getsizeof(node.odds)
        + getsizeof(node.repetitions)
        + getsizeof(node.height)
        + getsizeof(node.traversal_depth)
    )
    byte_count += sum(getsizeof(v) for v in node.word)
    return max(1, (byte_count + 7) // 8)


@dataclass(frozen=True, slots=True)
class _RetainedGuardedPort:
    joined: GuardedPortJoin
    node_charge: int


class ParityCarryTapeRetention:
    """Own transaction leases and completed ports through audited memo stores."""

    __slots__ = (
        "ledger",
        "lease_owner",
        "join_owner",
        "_leases",
        "_joins",
        "_disposed",
    )

    def __init__(
        self, ledger: ResourceLedger, lease_owner: int, join_owner: int
    ) -> None:
        self.ledger = ledger
        self.lease_owner = lease_owner
        self.join_owner = join_owner
        self._disposed = False
        leases: OwnedMemo[int, TemporaryRootLease[ParityCarryTape]] | None = None
        try:
            leases = OwnedMemo(ledger, lease_owner, node_cost=self._lease_node_cost)
            joins = OwnedMemo(ledger, join_owner, node_cost=self._joined_port_node_cost)
        except BaseException as error:
            if leases is not None:
                try:
                    leases.dispose()
                except BaseException as cleanup_error:
                    raise cleanup_error from error
            raise
        self._leases = leases
        self._joins = joins

    @staticmethod
    def _lease_node_cost(key: int, lease: TemporaryRootLease[ParityCarryTape]) -> int:
        if type(lease) is not TemporaryRootLease or key != id(lease):
            raise ValueError("temporary lease memo key lost exact object authority")
        return _LEASE_NODE_CHARGE - 1

    @staticmethod
    def _joined_port_node_cost(key: int, record: _RetainedGuardedPort) -> int:
        from number_compiler.sequences.collatz.guarded_port_join import (
            GuardedPortJoin,
        )

        if (
            type(record) is not _RetainedGuardedPort
            or type(record.joined) is not GuardedPortJoin
            or type(record.node_charge) is not int
            or record.node_charge < 1
            or key != id(record.joined)
        ):
            raise ValueError("retained port cost record lost exact join authority")
        return record.node_charge - 1

    def add_lease(
        self,
        lease: TemporaryRootLease[ParityCarryTape],
        reservation: LedgerReservation,
    ) -> None:
        if self._disposed:
            raise RuntimeError("parity retained-record owner is disposed")
        if type(lease) is not TemporaryRootLease:
            raise TypeError("parity lease store requires its exact lease type")
        self._leases.adopt_reserved(id(lease), lease, reservation)

    def forget_lease(self, lease: TemporaryRootLease[ParityCarryTape]) -> None:
        if self._disposed:
            raise RuntimeError("parity retained-record owner is disposed")
        if type(lease) is not TemporaryRootLease:
            raise TypeError("parity lease removal requires its exact lease type")
        key = id(lease)
        current = self._leases.get(key)
        if current is not lease:
            raise RuntimeError("temporary parity lease is foreign or stale")
        before = self.ledger.account_usage(self.lease_owner)
        try:
            del self._leases[key]
        except BaseException as error:
            after = self.ledger.account_usage(self.lease_owner)
            remaining = self._leases.get(key)
            committed = (before[0] - 1, before[1] - _LEASE_NODE_CHARGE)
            if remaining is None and after == committed:
                return
            if remaining is lease and after == before:
                raise
            raise RuntimeError(
                "lease removal left inconsistent owned accounting"
            ) from error

    def retain_join(
        self,
        joined: GuardedPortJoin,
        nodes: int,
        *,
        scratch_owner: int,
    ) -> None:
        from number_compiler.sequences.collatz.guarded_port_join import (
            GuardedPortJoin,
        )

        if self._disposed:
            raise RuntimeError("parity retained-record owner is disposed")
        if type(joined) is not GuardedPortJoin:
            raise TypeError("joined-port store requires its exact result type")
        if type(nodes) is not int or nodes < 1:
            raise ValueError("joined-port store requires a positive node charge")
        key = id(joined)
        existing = self._joins.get(key)
        if existing is not None:
            if existing.joined is joined:
                raise ValueError("joined port is already retained by this query")
            raise RuntimeError("joined-port memo identity was recycled")
        record = _RetainedGuardedPort(joined, nodes)
        with LedgerReservation(self.ledger, scratch_owner) as reservation:
            reservation.reserve(entries=1, nodes=nodes)
            self._joins.adopt_reserved(key, record, reservation)

    def dispose(self) -> None:
        if self._disposed:
            return
        from number_compiler.resources.lifecycle import cleanup_all

        revocations = (
            tuple(lease.revoke for lease in self._leases.values())
            if not self._leases.audit_snapshot().disposed
            else ()
        )
        cleanup_all((*revocations, self._leases.dispose, self._joins.dispose))
        self._disposed = True
