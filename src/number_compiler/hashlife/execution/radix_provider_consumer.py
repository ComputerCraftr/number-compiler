"""Typed heterogeneous composition of a binary provider with radix division."""

from __future__ import annotations

from collections.abc import Mapping, MutableMapping, MutableSequence
from dataclasses import dataclass
from typing import Literal, cast

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.arithmetic.radix_transfer import RadixRemainderTransfer
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.concrete_port_records import (
    PortAtom,
)
from number_compiler.hashlife.execution.continuations.concrete_port_scheduler import (
    ConcretePortAdapter,
)
from number_compiler.hashlife.execution.continuations.higher_values import (
    RuntimeValueID,
)
from number_compiler.hashlife.execution.continuations.provider_layers import (
    ProviderLayer,
)
from number_compiler.hashlife.execution.field_images import (
    SourceCellArena,
    SourceCellID,
)
from number_compiler.hashlife.execution.radix_consumer import (
    RadixDivisionActionArena,
    RadixDivisionActionID,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)
from number_compiler.resources.metric_keys import shared as _shared_keys
from number_compiler.resources.payload_containers import audit_mapping_items
from number_compiler.resources.stores import (
    NodeIndexFactory,
    append_indexed_node,
)


@dataclass(frozen=True, slots=True)
class RadixProviderActionID(FieldCellActionID):
    """Scoped identity of ``provider`` followed by a division action."""


@dataclass(frozen=True, slots=True)
class RadixProviderActionRecord:
    provider: FieldCellActionID
    consumer: RadixDivisionActionID


@dataclass(frozen=True, slots=True)
class RadixProviderActionAuditSnapshot:
    """Detached provider-action records and the identities of their stores."""

    ledger: ResourceLedger
    owner: ArenaToken
    kind: str
    node_owner: int
    node_store_identity: int
    nodes: tuple[RadixProviderActionRecord, ...]
    key_owner: int
    key_store_identity: int
    key_rows: tuple[tuple[object, object], ...]


class RadixProviderActionArena:
    """Intern heterogeneous roots without weakening either child action sort."""

    _nodes: MutableSequence[RadixProviderActionRecord]
    _keys: MutableMapping[RadixProviderActionRecord, int]

    KIND = "radix-provider-action"

    def __init__(
        self,
        ledger: ResourceLedger,
        provider: ConcretePortAdapter,
        divisions: RadixDivisionActionArena,
    ) -> None:
        if provider.ledger is not ledger or divisions.ledger is not ledger:
            raise ValueError("radix provider actions require one index ledger")
        if provider.sources.ledger is not ledger:
            raise ValueError("radix provider source belongs to another index")
        self.ledger, self.provider, self.divisions = ledger, provider, divisions
        self.owner = ArenaToken("radix-provider-actions")
        prefix = f"radix-provider-actions-{len(ledger.inventory())}"
        self._node_owner = ledger.register(prefix + "-nodes", "field_cell_action")
        self._key_owner = ledger.register(prefix + "-keys", "field_action_interner")
        self._nodes, self._keys = NodeIndexFactory[
            RadixProviderActionRecord, RadixProviderActionRecord
        ].dense(ledger, self._node_owner, self._key_owner)
        ledger.register_execution_root(self)

    def scoped_handle(self, local_id: int) -> RadixProviderActionID:
        return RadixProviderActionID(self.owner, self.KIND, local_id)

    def audit_snapshot(self) -> RadixProviderActionAuditSnapshot:
        """Capture action rows without exposing mutable interner storage."""
        return RadixProviderActionAuditSnapshot(
            ledger=self.ledger,
            owner=self.owner,
            kind=self.KIND,
            node_owner=self._node_owner,
            node_store_identity=id(self._nodes),
            nodes=tuple(self._nodes),
            key_owner=self._key_owner,
            key_store_identity=id(self._keys),
            key_rows=audit_mapping_items(cast(Mapping[object, object], self._keys)),
        )

    def record_index(self, record: RadixProviderActionRecord) -> int | None:
        """Return the canonical local ID for one provider-action record."""
        return self._keys.get(record)

    def resolve(self, action: RadixProviderActionID) -> RadixProviderActionRecord:
        if type(action) is not RadixProviderActionID:
            raise TypeError("expected a scoped radix provider action")
        action.validate(self.owner, self.KIND, size=len(self._nodes))
        return self._nodes[action.local_id]

    def intern(
        self,
        provider: FieldCellActionID,
        consumer: RadixDivisionActionID,
    ) -> RadixProviderActionID:
        self.provider.validate_action(provider)
        self.divisions.resolve(consumer)
        record = RadixProviderActionRecord(provider, consumer)
        found = self._keys.get(record)
        if found is not None:
            self.ledger.bump(_execution_keys.RADIX_PROVIDER_ACTION_EARLY_HITS)
            return self.scoped_handle(found)
        local_id = append_indexed_node(
            self.ledger,
            self._nodes,
            self._keys,
            self._node_owner,
            self._key_owner,
            record,
            record,
        )
        self.ledger.bump(_execution_keys.RADIX_PROVIDER_ACTION_EVALUATIONS)
        self.ledger.bump(_shared_keys.FIELD_ACTION_PUBLICATIONS)
        return self.scoped_handle(local_id)


class RadixProviderAdapter:
    """Concrete-port adapter for a producer followed by repeated ``D_radix``.

    Division carries run from the most-significant edge (side one) toward the
    least-significant edge.  Side zero observes whether the input contains a one.
    """

    def __init__(
        self,
        provider: ConcretePortAdapter,
        divisions: RadixDivisionActionArena,
    ) -> None:
        if provider.ledger is not divisions.ledger:
            raise ValueError("radix provider adapter requires one index ledger")
        self.provider, self.divisions = provider, divisions
        self.ledger: ResourceLedger = provider.ledger
        self.sources: SourceCellArena = provider.sources
        self.actions = RadixProviderActionArena(
            self.ledger,
            provider,
            divisions,
        )
        self.ledger.register_execution_root(self)

    def _division(self, action: FieldCellActionID) -> bool:
        return type(action) is RadixDivisionActionID

    def _root(self, action: FieldCellActionID) -> bool:
        return type(action) is RadixProviderActionID

    def validate_action(self, action: FieldCellActionID) -> object:
        if self._division(action):
            return self.divisions.resolve(cast(RadixDivisionActionID, action))
        if self._root(action):
            return self.actions.resolve(cast(RadixProviderActionID, action))
        return self.provider.validate_action(action)

    def children(
        self,
        action: FieldCellActionID,
    ) -> tuple[FieldCellActionID, FieldCellActionID] | None:
        if self._division(action):
            children = self.divisions.children(cast(RadixDivisionActionID, action))
            return None if children is None else children
        if self._root(action):
            record = self.actions.resolve(cast(RadixProviderActionID, action))
            return record.provider, record.consumer
        return self.provider.children(action)

    def action_kind(
        self,
        action: FieldCellActionID,
    ) -> Literal["identity", "primitive", "compose"]:
        children = self.children(action)
        if children is not None:
            return "compose"
        if self._division(action):
            return "primitive"
        kind = getattr(self.provider, "action_kind", None)
        return (
            "primitive"
            if kind is None
            else cast(
                Literal["identity", "primitive", "compose"],
                kind(action),
            )
        )

    @staticmethod
    def _side(side: int) -> int:
        if type(side) is not int:
            raise TypeError("radix division side must be an exact integer")
        if side not in (0, 1):
            raise ValueError("radix division side must be zero or one")
        return side

    def primitive_initial(self, action: FieldCellActionID, side: int) -> int:
        if not self._division(action):
            return self.provider.primitive_initial(action, side)
        self.divisions.resolve(cast(RadixDivisionActionID, action))
        self._side(side)
        return 0

    def primitive_state_count(self, action: FieldCellActionID, side: int) -> int:
        if not self._division(action):
            return self.provider.primitive_state_count(action, side)
        self.divisions.resolve(cast(RadixDivisionActionID, action))
        return 2 if self._side(side) == 0 else self.divisions.radix

    def primitive_advance(
        self,
        action: FieldCellActionID,
        side: int,
        state: int,
        symbol: int,
    ) -> int:
        if not self._division(action):
            return self.provider.primitive_advance(action, side, state, symbol)
        self.divisions.resolve(cast(RadixDivisionActionID, action))
        side = self._side(side)
        if type(state) is not int or type(symbol) is not int:
            raise TypeError("radix division requires exact finite port values")
        limit = 2 if side == 0 else self.divisions.radix
        if not 0 <= state < limit or symbol not in (0, 1, 2):
            raise ValueError("radix division input lies outside its finite port")
        self.ledger.bump(_shared_keys.RADIX_LIMB_OPERATIONS)
        if symbol == 2:
            return state
        if side == 0:
            return state | symbol
        return self.ledger.observe_arithmetic(2 * state + symbol) % self.divisions.radix

    def primitive_advance_cell(
        self,
        action: FieldCellActionID,
        side: int,
        state: int,
        cell: SourceCellID,
        reverse: bool,
    ) -> int:
        if not self._division(action):
            return self.provider.primitive_advance_cell(
                action,
                side,
                state,
                cell,
                reverse,
            )
        self.divisions.resolve(cast(RadixDivisionActionID, action))
        self.sources.resolve(cell)
        raise RuntimeError(
            "radix division consumes a virtual provider, not original source cells"
        )

    def primitive_emit(
        self,
        action: FieldCellActionID,
        left: int,
        symbol: int,
        right: int,
    ) -> int:
        if not self._division(action):
            return self.provider.primitive_emit(action, left, symbol, right)
        self.divisions.resolve(cast(RadixDivisionActionID, action))
        if any(type(value) is not int for value in (left, symbol, right)):
            raise TypeError("radix division emission requires exact finite values")
        if left not in (0, 1) or not 0 <= right < self.divisions.radix:
            raise ValueError("radix division emission has an invalid boundary")
        if symbol == 2:
            return 2
        if symbol not in (0, 1):
            raise ValueError("radix division requires a binary provider symbol")
        self.ledger.bump(_shared_keys.RADIX_LIMB_OPERATIONS)
        return (
            self.ledger.observe_arithmetic(2 * right + symbol) // self.divisions.radix
        )

    def blank_initial_is_stable(
        self,
        action: FieldCellActionID,
        side: int,
    ) -> bool:
        if self._root(action):
            self.actions.resolve(cast(RadixProviderActionID, action))
            self._side(side)
            return False
        if not self._division(action):
            return self.provider.blank_initial_is_stable(action, side)
        self.divisions.resolve(cast(RadixDivisionActionID, action))
        self._side(side)
        return True

    def output_blank(self, action: FieldCellActionID) -> int:
        self.validate_action(action)
        return 2

    def output_ignores_port(self, action: FieldCellActionID, side: int) -> bool:
        """Every D power emits independently of its input-activity port.

        The activity remains observable; only its use as an output dependency
        is erased. Both children preserve this law under temporal composition.
        """
        self.validate_action(action)
        self._side(side)
        return self._division(action) and side == 0

    def virtual_transfer_leaf(
        self,
        action: FieldCellActionID,
        side: int,
        symbol: int,
    ) -> RadixRemainderTransfer | None:
        self.validate_action(action)
        self._side(side)
        if not self._division(action) or side == 0:
            return None
        return RadixRemainderTransfer.leaf(self.divisions.radix, symbol)

    def validate_virtual_transfer(
        self,
        action: FieldCellActionID,
        side: int,
        transfer: object,
    ) -> None:
        self.validate_action(action)
        self._side(side)
        if not self._division(action) or side != 1:
            raise ValueError("affine division transfer has another action port")
        if type(transfer) is not RadixRemainderTransfer:
            raise TypeError("division requires a bounded affine remainder transfer")
        transfer.__post_init__()
        if transfer.radix != self.divisions.radix:
            raise ValueError("division transfer belongs to another radix")

    def compose_virtual_transfers(
        self,
        action: FieldCellActionID,
        side: int,
        first: object,
        second: object,
    ) -> RadixRemainderTransfer | None:
        if not self._division(action) or side == 0:
            return None
        self.validate_virtual_transfer(action, side, first)
        self.validate_virtual_transfer(action, side, second)
        return cast(RadixRemainderTransfer, first).then(
            cast(RadixRemainderTransfer, second),
            self.ledger,
        )

    def apply_virtual_transfer(
        self,
        action: FieldCellActionID,
        side: int,
        transfer: object,
        state: int,
    ) -> int | None:
        if not self._division(action) or side == 0:
            return None
        self.validate_virtual_transfer(action, side, transfer)
        return cast(RadixRemainderTransfer, transfer).apply(state, self.ledger)

    def validate_canonical_atom(self, value: RuntimeValueID) -> object:
        validator = getattr(self.provider, "validate_canonical_atom", None)
        if validator is None:
            raise TypeError("provider does not admit canonical runtime ports")
        return validator(value)

    def canonical_initial(
        self,
        action: FieldCellActionID,
        side: int,
    ) -> PortAtom | None:
        if self._division(action) or self._root(action):
            return None
        initial = getattr(self.provider, "canonical_initial", None)
        return None if initial is None else cast(PortAtom, initial(action, side))

    def canonical_advance_cell(
        self,
        action: FieldCellActionID,
        side: int,
        state: PortAtom,
        cell: SourceCellID,
        reverse: bool,
        layers: tuple[ProviderLayer, ...],
    ) -> PortAtom | None:
        if self._division(action) or self._root(action):
            return None
        advance = getattr(self.provider, "canonical_advance_cell", None)
        return (
            None
            if advance is None
            else cast(
                PortAtom | None,
                advance(action, side, state, cell, reverse, layers),
            )
        )

    def canonical_emit_leaf(
        self,
        action: FieldCellActionID,
        left: PortAtom,
        right: PortAtom,
        cell: SourceCellID,
        layers: tuple[ProviderLayer, ...],
    ) -> int | None:
        if self._division(action) or self._root(action):
            return None
        emit = getattr(self.provider, "canonical_emit_leaf", None)
        return (
            None
            if emit is None
            else cast(
                int | None,
                emit(action, left, right, cell, layers),
            )
        )


__all__ = [
    "RadixProviderActionAuditSnapshot",
    "RadixProviderActionArena",
    "RadixProviderActionID",
    "RadixProviderAdapter",
    "RadixProviderActionRecord",
]
