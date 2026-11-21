"""Ledger-owned all-inlet actions over compressed temporal signal words."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.resources.ledger import (
    LedgerReservation,
    OwnedMemo,
    ResourceLedger,
)
from number_compiler.resources.lifecycle import cleanup_all


@dataclass(frozen=True, slots=True)
class _SignalAction:
    duration: int
    exits: tuple[int, ...]
    hits: tuple[int | None, ...]


class TemporalSignalBank:
    """Compile one immutable transition/event law on an arena's signal DAG.

    Each table cell contains ``(next_state, event_bits)``. A hit requires all
    bits in ``required_events`` at the same time. Source and clock admission
    remain with the caller. The bank rejects stale arena generations.
    """

    def __init__(
        self,
        arena: LedgerSLPArena,
        scratch_owner: int,
        transitions: tuple[tuple[tuple[int, int], ...], ...],
        required_events: int,
    ) -> None:
        if type(transitions) is not tuple or not transitions or not transitions[0]:
            raise ValueError("signal law requires symbols and states")
        states = len(transitions[0])
        if len(transitions) > 256 or states > 256:
            raise ValueError("signal alphabet exceeds its bounded state space")
        if (
            type(required_events) is not int
            or required_events <= 0
            or required_events.bit_length() > 64
        ):
            raise ValueError("signal event conjunction must be nonempty")
        if type(transitions) is not tuple or any(
            type(row) is not tuple
            or len(row) != states
            or any(
                type(cell) is not tuple
                or len(cell) != 2
                or type(cell[0]) is not int
                or not 0 <= cell[0] < states
                or type(cell[1]) is not int
                or cell[1] < 0
                or cell[1].bit_length() > 64
                for cell in row
            )
            for row in transitions
        ):
            raise ValueError("invalid finite signal transition law")
        self._arena = arena
        self._generation = arena.node_id_generation
        self._ledger: ResourceLedger = arena.ledger
        self._scratch_owner = scratch_owner
        self._transitions = transitions
        self._required = required_events
        self._states = states
        owner = self._ledger.register(
            f"temporal-signal-actions-{self._ledger.owner_count}",
            "temporal_signal_action",
        )
        try:
            self._law_reservation = LedgerReservation(self._ledger, scratch_owner)
        except BaseException:
            self._ledger.mark_disposed(owner)
            raise
        try:
            self._law_reservation.reserve(nodes=1 + len(transitions) * (1 + 2 * states))
            self._cache: OwnedMemo[int, _SignalAction] = OwnedMemo(
                self._ledger,
                owner,
                node_cost=lambda _key, action: (
                    2 * states
                    + 1
                    + (states + 1) * ((action.duration.bit_length() + 63) // 64)
                ),
            )
        except BaseException:
            cleanup_all(
                (
                    self._law_reservation.close,
                    lambda: self._ledger.mark_disposed(owner),
                )
            )
            raise
        self._closed = False

    def _check(self) -> None:
        if self._closed:
            raise ValueError("temporal signal bank is closed")
        self._arena.empty()
        if self._arena.node_id_generation != self._generation:
            raise ValueError("temporal signal bank is stale")

    def _then(self, left: _SignalAction, right: _SignalAction) -> _SignalAction:
        exits: list[int] = []
        hits: list[int | None] = []
        for state, middle in enumerate(left.exits):
            exits.append(right.exits[middle])
            found = left.hits[state]
            following = right.hits[middle]
            hits.append(
                found
                if found is not None
                else None
                if following is None
                else left.duration + following
            )
        return _SignalAction(left.duration + right.duration, tuple(exits), tuple(hits))

    def _compile(self, root: int) -> _SignalAction:
        self._check()
        if type(root) is not int or not 0 <= root < len(self._arena.nodes):
            raise ValueError("invalid temporal signal root")
        cached = self._cache.get(root)
        if cached is not None:
            return cached
        identity = _SignalAction(0, tuple(range(self._states)), (None,) * self._states)
        stack: list[tuple[int, bool]] = []
        with LedgerReservation(self._ledger, self._scratch_owner) as reservation:
            reservation.reserve(nodes=4 * self._states)

            def push(node_id: int, ready: bool) -> None:
                reservation.reserve(entries=1, nodes=1)
                stack.append((node_id, ready))

            try:
                push(root, False)
                while stack:
                    node_id, ready = stack.pop()
                    reservation.release(entries=1, nodes=1)
                    if self._cache.get(node_id) is not None:
                        continue
                    node = self._arena.nodes[node_id]
                    if node.kind == "EMPTY":
                        action = identity
                    elif node.kind == "TERM":
                        if not 0 <= node.symbol < len(self._transitions):
                            raise ValueError("signal symbol outside its law")
                        table = self._transitions[node.symbol]
                        action = _SignalAction(
                            1,
                            tuple(target for target, _ in table),
                            tuple(
                                0 if events & self._required == self._required else None
                                for _, events in table
                            ),
                        )
                    elif not ready:
                        push(node_id, True)
                        if node.kind == "CONCAT":
                            push(node.right, False)
                            push(node.left, False)
                        elif node.kind == "REPEAT":
                            push(node.child, False)
                        else:
                            raise ValueError("invalid temporal signal node")
                        continue
                    elif node.kind == "CONCAT":
                        action = self._then(
                            self._cache[node.left], self._cache[node.right]
                        )
                    elif node.kind == "REPEAT":
                        count = node.count
                        if count.bit_length() > 4096:
                            raise ValueError("temporal signal exponent exceeds budget")
                        action, power = identity, self._cache[node.child]
                        while count:
                            if count & 1:
                                action = self._then(action, power)
                            count //= 2
                            if count:
                                power = self._then(power, power)
                    else:
                        raise ValueError("invalid temporal signal node")
                    self._cache[node_id] = action
            finally:
                stack.clear()
        return self._cache[root]

    def first_simultaneous(self, root: int, inlet: int) -> int | None:
        """Return the first zero-based aligned sample satisfying every event."""
        if type(inlet) is not int or not 0 <= inlet < self._states:
            raise ValueError("signal inlet is outside its state alphabet")
        return self._compile(root).hits[inlet]

    def dispose(self) -> None:
        if not self._closed:
            cleanup_all(
                (
                    self._cache.dispose,
                    self._law_reservation.close,
                )
            )
            self._closed = True
