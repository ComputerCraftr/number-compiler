"""Research-only bounded reverse/add leaf interface.

This obsolete primitive-port experiment is not an installed field-image or
source-cylinder execution owner.

This adapter exposes the primitive two-sided pair-cell law through scoped port
IDs.  It admits states only as demanded and never loads the decimal T2 proof
machine or constructs an exact tile, carry row, or output word.
"""

from __future__ import annotations

from collections.abc import MutableMapping, MutableSequence
from dataclasses import dataclass

from number_compiler.arithmetic.contracts.block_effect import (
    BoundarySide,
    BoundaryState,
)
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class ReversePortStateID(ArenaHandle):
    """Scoped finite state on one directed reverse/add cell interface."""


@dataclass(frozen=True, slots=True)
class ReverseLocalInterfaceMetrics:
    left_states: int
    right_states: int
    transition_requests: int
    transition_hits: int
    transition_evaluations: int
    output_requests: int
    output_hits: int
    output_evaluations: int


class ReverseLocalInterfaceArena:
    """Index-owned, demand-driven realization of the primitive pair law."""

    _KINDS = ("reverse-port-left", "reverse-port-right")

    def __init__(self, base: int, ledger: ResourceLedger | None = None) -> None:
        if type(base) is not int or base < 2:
            raise ValueError("reverse local interface requires an exact radix")
        self.base = base
        self.blank = 2 * base - 1
        self.ledger = ResourceLedger() if ledger is None else ledger
        if type(self.ledger) is not ResourceLedger:
            raise TypeError("reverse local interface requires an index ledger")
        self.owner = ArenaToken("reverse-local-interface")
        self.kernel = BaseBlockEffect(base)
        prefix = f"reverse-local-{len(self.ledger.inventory())}"
        self._state_owners = (
            self.ledger.register(prefix + "-left-states", "reverse_port_state"),
            self.ledger.register(prefix + "-right-states", "reverse_port_state"),
        )
        self._state_key_owners = (
            self.ledger.register(prefix + "-left-keys", "reverse_port_interner"),
            self.ledger.register(prefix + "-right-keys", "reverse_port_interner"),
        )
        self._transition_owner = self.ledger.register(
            prefix + "-transitions",
            "reverse_port_transition",
        )
        self._output_owner = self.ledger.register(
            prefix + "-outputs", "reverse_leaf_output"
        )
        self._states: tuple[
            MutableSequence[BoundaryState], MutableSequence[BoundaryState]
        ] = (
            self.ledger.make_list(self._state_owners[0]),
            self.ledger.make_list(self._state_owners[1]),
        )
        self._state_keys: tuple[
            MutableMapping[BoundaryState, ReversePortStateID],
            MutableMapping[BoundaryState, ReversePortStateID],
        ] = (
            self.ledger.make_dict(self._state_key_owners[0]),
            self.ledger.make_dict(self._state_key_owners[1]),
        )
        self._transitions: MutableMapping[
            tuple[BoundarySide, ReversePortStateID, int], ReversePortStateID
        ] = self.ledger.make_dict(self._transition_owner)
        self._outputs: MutableMapping[
            tuple[ReversePortStateID, int, ReversePortStateID], int
        ] = self.ledger.make_dict(
            self._output_owner,
        )
        self.transition_requests = 0
        self.transition_hits = 0
        self.transition_evaluations = 0
        self.output_requests = 0
        self.output_hits = 0
        self.output_evaluations = 0
        self.ledger.register_execution_root(self)
        self.identity = (
            self.intern_record(
                BoundarySide.LEFT, self.kernel.initial(BoundarySide.LEFT)
            ),
            self.intern_record(
                BoundarySide.RIGHT, self.kernel.initial(BoundarySide.RIGHT)
            ),
        )

    @staticmethod
    def _side(side: BoundarySide) -> int:
        if type(side) is not BoundarySide:
            raise TypeError("reverse port direction must be a BoundarySide")
        return int(side)

    def intern_record(
        self, side: BoundarySide, state: BoundaryState
    ) -> ReversePortStateID:
        index = self._side(side)
        found = self._state_keys[index].get(state)
        if found is not None:
            return found
        # These caps follow directly from the primitive value domains and are
        # intentionally loose. Their purpose is to make accidental admission
        # of a powered proof domain impossible.
        cap = 8 * (self.blank + 2) if side is BoundarySide.LEFT else 9
        if len(self._states[index]) >= cap:
            raise ValueError("reverse primitive interface exceeded its finite bound")
        result = ReversePortStateID(
            self.owner,
            self._KINDS[index],
            len(self._states[index]),
        )
        self.ledger.reserve_many(
            (
                (self._state_owners[index], 1, 1),
                (self._state_key_owners[index], 1, 0),
            )
        )
        self._states[index].append(state)
        self._state_keys[index][state] = result
        return result

    def resolve(
        self, side: BoundarySide, reference: ReversePortStateID
    ) -> BoundaryState:
        index = self._side(side)
        if type(reference) is not ReversePortStateID:
            raise TypeError("reverse interface requires a scoped port-state ID")
        reference.validate(
            self.owner, self._KINDS[index], size=len(self._states[index])
        )
        return self._states[index][reference.local_id]

    def initial(self, side: BoundarySide) -> ReversePortStateID:
        return self.identity[self._side(side)]

    def advance(
        self,
        side: BoundarySide,
        state: ReversePortStateID,
        symbol: int,
    ) -> ReversePortStateID:
        self._side(side)
        current = self.resolve(side, state)
        if type(symbol) is not int or not 0 <= symbol <= self.blank:
            raise ValueError("reverse pair symbol is outside its finite alphabet")
        self.transition_requests += 1
        # Resolve before probing.  Retaining the complete state handle in the
        # key preserves owner and directional kind, rather than relying on a
        # local integer that can alias another interface.
        key = side, state, symbol
        found = self._transitions.get(key)
        if found is not None:
            self.transition_hits += 1
            return found
        result = self.intern_record(side, self.kernel.advance(side, current, symbol))
        self.ledger.reserve(self._transition_owner, entries=1, nodes=0)
        self._transitions[key] = result
        self.transition_evaluations += 1
        self.ledger.bump("primitive_transition_evaluations")
        return result

    def emit(
        self,
        left: ReversePortStateID,
        symbol: int,
        right: ReversePortStateID,
    ) -> int:
        left_state = self.resolve(BoundarySide.LEFT, left)
        right_state = self.resolve(BoundarySide.RIGHT, right)
        if type(symbol) is not int or not 0 <= symbol <= self.blank:
            raise ValueError("reverse pair symbol is outside its finite alphabet")
        self.output_requests += 1
        key = left, symbol, right
        found = self._outputs.get(key)
        if found is not None:
            self.output_hits += 1
            return found
        result = int(self.kernel.emit(left_state, symbol, right_state))
        if not 0 <= result <= self.blank:
            raise AssertionError("reverse primitive emitted outside its alphabet")
        self.ledger.reserve(self._output_owner, entries=1, nodes=0)
        self._outputs[key] = result
        self.output_evaluations += 1
        self.ledger.bump("output_morphism_operations")
        return result

    def metrics(self) -> ReverseLocalInterfaceMetrics:
        return ReverseLocalInterfaceMetrics(
            len(self._states[0]),
            len(self._states[1]),
            self.transition_requests,
            self.transition_hits,
            self.transition_evaluations,
            self.output_requests,
            self.output_hits,
            self.output_evaluations,
        )


__all__ = [
    "ReverseLocalInterfaceArena",
    "ReverseLocalInterfaceMetrics",
    "ReversePortStateID",
]
