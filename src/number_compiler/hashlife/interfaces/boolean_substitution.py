"""Iterative simultaneous Boolean substitution within one transaction."""

from __future__ import annotations

from collections.abc import Mapping
from typing import TYPE_CHECKING

from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.resources.metric_keys import (
    hashlife_interfaces as _interfaces_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.interfaces.semantic_bits import BooleanCircuit


def substitute_boolean(
    circuit: BooleanCircuit, root: int, replacements: Mapping[PortVariable, int]
) -> int:
    """Simultaneous substitution shared across all roots in this circuit.

    The memo is transient, scoped to one immutable semantic transaction and
    complete substitution environment. It contains no source/coordinate keys.
    """
    transaction = circuit.tx
    ledger = transaction.arena.ledger
    key = tuple(sorted(replacements.items()))
    done = circuit._substitutions.setdefault(key, {})

    def retain(identity: int, value: int) -> None:
        done[identity] = value
        circuit._substitution_entries += 1

    pending = [(root, False)]
    changed = frozenset(replacements)
    while pending:
        ledger.bump(
            _interfaces_keys.SEMANTIC_BIT_SUBSTITUTION_WORKSPACE_PEAK,
            max(
                0,
                len(pending)
                + circuit._substitution_entries
                - ledger.counters.get(
                    _interfaces_keys.SEMANTIC_BIT_SUBSTITUTION_WORKSPACE_PEAK,
                    0,
                ),
            ),
        )
        current, ready = pending.pop()
        ledger.bump(_interfaces_keys.SEMANTIC_BIT_SUBSTITUTION_FRAMES)
        if current in done:
            ledger.bump(_interfaces_keys.SEMANTIC_BIT_SUBSTITUTION_SHARED_HITS)
            continue
        node = transaction.node(current)
        if node.signature == circuit.signature and not changed.intersection(
            node.support
        ):
            retain(current, current)
            ledger.bump(_interfaces_keys.SEMANTIC_BIT_SUBSTITUTION_UNCHANGED_ROOTS)
        elif node.terminal is not None:
            retain(current, transaction.terminal(circuit.signature, node.terminal))
        else:
            assert node.variable is not None
            condition = replacements.get(node.variable)
            if condition in (circuit.zero, circuit.one):
                child = node.high if condition == circuit.one else node.low
                if child in done:
                    retain(current, done[child])
                else:
                    ledger.bump(
                        _interfaces_keys.SEMANTIC_BIT_SUBSTITUTION_COFACTOR_PRUNES
                    )
                    pending.extend(((current, True), (child, False)))
            elif ready:
                if condition is None:
                    retain(
                        current,
                        transaction.rebuilt_decision(
                            circuit.signature,
                            node.variable,
                            done[node.low],
                            done[node.high],
                        ),
                    )
                else:
                    retain(
                        current,
                        circuit.choose(condition, done[node.high], done[node.low]),
                    )
            else:
                pending.extend(((current, True), (node.high, False), (node.low, False)))
    return done[root]
