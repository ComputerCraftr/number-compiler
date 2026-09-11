"""Canonical temporal actions for heterogeneous binary-to-radix division."""

from __future__ import annotations

from collections.abc import MutableMapping, MutableSequence
from dataclasses import dataclass

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.arithmetic.functions.finite_function_types import FinitePort
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.interfaces.semantic_bits import (
    BinaryDivision,
    BitFunctionArena,
)
from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class RadixDivisionActionID(FieldCellActionID):
    """Scoped identity of one source-independent ``D_radix**exponent`` action."""


@dataclass(frozen=True, slots=True)
class RadixDivisionAction:
    radix: int
    exponent: int

    def __post_init__(self) -> None:
        if type(self.radix) is not int or not 2 <= self.radix <= 1 << 63:
            raise ValueError("radix action requires an exact bounded radix")
        if type(self.exponent) is not int or self.exponent < 1:
            raise ValueError("radix action requires a positive exact exponent")


class RadixDivisionActionArena:
    """Hash-cons division powers and their one-step finite semantic circuit."""

    _KIND = "radix-division-action"

    def __init__(self, ledger: ResourceLedger, radix: int) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("radix actions require an index resource ledger")
        RadixDivisionAction(radix, 1).__post_init__()
        self.ledger, self.radix = ledger, radix
        self.owner = ArenaToken("radix-division-actions")
        self.bits = BitFunctionArena(ledger)
        self.carry_port = FinitePort(
            PortVariable(0, 1, "radix-remainder", 0),
            radix,
        )
        self.symbol_port = FinitePort(
            PortVariable(0, 0, "provider-symbol", 0),
            2,
        )
        self.primitive_semantics: BinaryDivision = self.bits.divide_binary(
            radix,
            self.carry_port,
            self.symbol_port,
        )
        prefix = f"radix-{radix}-consumer-actions-{len(ledger.inventory())}"
        self._node_owner = ledger.register(prefix + "-nodes", "field_cell_action")
        self._key_owner = ledger.register(prefix + "-keys", "field_action_interner")
        self._compose_owner = ledger.register(
            prefix + "-compositions",
            "temporal_composition",
        )
        self._nodes: MutableSequence[RadixDivisionAction] = ledger.make_list(
            self._node_owner,
        )
        self._keys: MutableMapping[int, int] = ledger.make_dict(self._key_owner)
        self._children: MutableMapping[
            int, tuple[RadixDivisionActionID, RadixDivisionActionID]
        ] = ledger.make_dict(self._compose_owner)
        ledger.register_container(
            self._node_owner,
            self._nodes,
            node_count=lambda: len(self._nodes),
            payloads=lambda: self._nodes,
        )
        ledger.register_container(
            self._key_owner,
            self._keys,
            payloads=self._keys.items,
        )
        ledger.register_container(
            self._compose_owner,
            self._children,
            payloads=self._children.items,
        )
        ledger.register_execution_root(self)
        self.primitive = self._intern(1)

    def _handle(self, local_id: int) -> RadixDivisionActionID:
        return RadixDivisionActionID(self.owner, self._KIND, local_id)

    def resolve(self, action: RadixDivisionActionID) -> RadixDivisionAction:
        if type(action) is not RadixDivisionActionID:
            raise TypeError("expected a scoped radix division action")
        action.validate(self.owner, self._KIND, size=len(self._nodes))
        return self._nodes[action.local_id]

    def _intern(
        self,
        exponent: int,
        children: tuple[RadixDivisionActionID, RadixDivisionActionID] | None = None,
    ) -> RadixDivisionActionID:
        record = RadixDivisionAction(self.radix, exponent)
        if children is not None:
            before, after = children
            if self.resolve(before).exponent + self.resolve(after).exponent != exponent:
                raise ValueError("radix action witness has another exponent")
        found = self._keys.get(exponent)
        if found is not None:
            self.ledger.bump("radix_temporal_action_early_hits")
            return self._handle(found)
        reservations = [
            (self._node_owner, 1, 1),
            (self._key_owner, 1, 0),
        ]
        if children is not None:
            reservations.append((self._compose_owner, 1, 0))
        self.ledger.reserve_many(tuple(reservations))
        local_id = len(self._nodes)
        self._nodes.append(record)
        self._keys[exponent] = local_id
        if children is not None:
            self._children[local_id] = children
        self.ledger.bump("radix_temporal_action_evaluations")
        self.ledger.bump("field_action_publications")
        return self._handle(local_id)

    def compose(
        self,
        before: RadixDivisionActionID,
        after: RadixDivisionActionID,
    ) -> RadixDivisionActionID:
        """Apply ``before`` and then ``after`` with semantic pre-interning."""
        a, b = self.resolve(before), self.resolve(after)
        self.ledger.bump("radix_temporal_action_requests")
        found = self._keys.get(a.exponent + b.exponent)
        if found is not None:
            self.ledger.bump("radix_temporal_action_early_hits")
            return self._handle(found)
        return self._intern(a.exponent + b.exponent, (before, after))

    def children(
        self,
        action: RadixDivisionActionID,
    ) -> tuple[RadixDivisionActionID, RadixDivisionActionID] | None:
        record = self.resolve(action)
        return None if record.exponent == 1 else self._children[action.local_id]

    def power(self, exponent: int) -> RadixDivisionActionID:
        """Build ``D**exponent`` with logarithmic temporal compositions."""
        if type(exponent) is not int:
            raise TypeError("radix division exponent must be an exact integer")
        if exponent < 1:
            raise ValueError("radix division exponent must be positive")
        found = self._keys.get(exponent)
        if found is not None:
            self.ledger.bump("radix_temporal_action_early_hits")
            return self._handle(found)
        result: RadixDivisionActionID | None = None
        power = self.primitive
        remaining = exponent
        while remaining:
            if remaining & 1:
                result = power if result is None else self.compose(result, power)
            remaining >>= 1
            if remaining:
                power = self.compose(power, power)
        assert result is not None
        return result


__all__ = [
    "RadixDivisionAction",
    "RadixDivisionActionArena",
    "RadixDivisionActionID",
]
