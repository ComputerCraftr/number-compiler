"""Independent structural audit for the finite-port decision arenas."""

from __future__ import annotations

from collections.abc import Iterable, Mapping
from dataclasses import dataclass

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.arithmetic.functions.finite_port_action import (
    FinitePortActionArena,
    PortVariable,
    _ChoiceIndexKey,
    _Decision,
    _DecisionIndexKey,
)
from number_compiler.arithmetic.functions.finite_port_substitution import (
    _PortIndexComponent,
    _SubstitutionIndexKey,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_containers import audit_mapping_items


@dataclass(frozen=True, slots=True)
class FinitePortAudit:
    arenas: dict[ArenaToken, FinitePortActionArena]
    index_owners: set[int]
    choices: set[int]
    substitutions: set[int]
    support_tuples: set[int]


def audit_finite_ports(
    ledger: ResourceLedger,
    roots: Iterable[object],
    containers: Mapping[int, object],
    forbidden: set[tuple[int, int]],
) -> FinitePortAudit:
    arenas: dict[ArenaToken, FinitePortActionArena] = {}
    index_owners: set[int] = set()
    choices: set[int] = set()
    substitutions: set[int] = set()
    support_tuples: set[int] = set()
    for root in roots:
        if type(root) is not FinitePortActionArena or root.ledger is not ledger:
            continue
        if (
            containers.get(root._node_owner) is not root._nodes
            or containers.get(root._key_owner) is not root._keys
        ):
            continue
        arenas[root.owner] = root
        # These stores contain only local decision-node indices and are
        # independently checked below against the owning arena.  Treating the
        # collection of those indices as an untyped numeric word makes a
        # larger, valid reduced decision DAG look like packed digit payload.
        index_owners.update(
            (
                root._key_owner,
                root._ite.owner,
                root._substitution.memo_owner,
                root._substitution.support_owner,
            )
        )
        _audit_choices(root, containers, forbidden, choices)
        _audit_substitutions(root, containers, forbidden, substitutions, support_tuples)
        _audit_decisions(root, forbidden)
    return FinitePortAudit(arenas, index_owners, choices, substitutions, support_tuples)


def _valid_index(value: object, bound: int) -> bool:
    return type(value) is int and 0 <= value < bound


def _audit_choices(
    arena: FinitePortActionArena,
    containers: Mapping[int, object],
    forbidden: set[tuple[int, int]],
    approved: set[int],
) -> None:
    memo = arena._ite
    if containers.get(memo.owner) is not memo._data:
        forbidden.add((memo.owner, id(memo._data)))
    for key, result in audit_mapping_items(memo._data):
        if type(key) is not _ChoiceIndexKey or not all(
            _valid_index(index, len(arena._nodes))
            for index in (key.condition, key.yes, key.no, result)
        ):
            forbidden.add((memo.owner, id(key)))
        else:
            approved.add(id(key))


def _audit_substitutions(
    arena: FinitePortActionArena,
    containers: Mapping[int, object],
    forbidden: set[tuple[int, int]],
    approved: set[int],
    support_tuples: set[int],
) -> None:
    substitution = arena._substitution
    if containers.get(substitution.memo_owner) is not substitution.memo:
        forbidden.add((substitution.memo_owner, id(substitution.memo)))
    if containers.get(substitution.support_owner) is not substitution.supports:
        forbidden.add((substitution.support_owner, id(substitution.supports)))
    for key, result in audit_mapping_items(substitution.memo):
        valid = (
            type(key) is _SubstitutionIndexKey
            and _valid_index(key.function, len(arena._nodes))
            and type(key.components) is tuple
            and _valid_index(result, len(arena._nodes))
        )
        previous: PortVariable | None = None
        if valid:
            for component in key.components:
                if (
                    type(component) is not _PortIndexComponent
                    or type(component.variable) is not PortVariable
                    or not _valid_index(component.function, len(arena._nodes))
                    or (previous is not None and component.variable <= previous)
                ):
                    valid = False
                    break
                previous = component.variable
        if valid:
            approved.add(id(key))
        else:
            forbidden.add((substitution.memo_owner, id(key)))
    for index, variables in audit_mapping_items(substitution.supports):
        valid = (
            _valid_index(index, len(arena._nodes))
            and type(variables) is tuple
            and all(type(variable) is PortVariable for variable in variables)
            and variables == tuple(sorted(set(variables)))
        )
        if valid:
            support_tuples.add(id(variables))
        else:
            forbidden.add((substitution.support_owner, id(variables)))


def _audit_decisions(
    arena: FinitePortActionArena,
    forbidden: set[tuple[int, int]],
) -> None:
    if len(arena._nodes) < 2 or len(arena._keys) != len(arena._nodes) - 2:
        forbidden.add((arena._key_owner, id(arena._keys)))
    for terminal in arena._nodes[:2]:
        if (
            type(terminal) is not _Decision
            or terminal.variable is not None
            or terminal.low != 0
            or terminal.high != 0
        ):
            forbidden.add((arena._node_owner, id(terminal)))
    for key, local_id in audit_mapping_items(arena._keys):
        if (
            type(key) is not _DecisionIndexKey
            or type(local_id) is not int
            or not 2 <= local_id < len(arena._nodes)
            or not _valid_index(key.low, local_id)
            or not _valid_index(key.high, local_id)
        ):
            forbidden.add((arena._key_owner, id(key)))
            continue
        node = arena._nodes[local_id]
        if (
            type(node) is not _Decision
            or type(key.variable) is not PortVariable
            or key.low == key.high
            or (node.variable, node.low, node.high) != (key.variable, key.low, key.high)
        ):
            forbidden.add((arena._key_owner, id(key)))
            continue
        try:
            key.variable.__post_init__()
            for child_id in (key.low, key.high):
                child = arena._nodes[child_id]
                if type(child) is not _Decision:
                    raise ValueError("invalid decision child")
                if child.variable is not None:
                    child.variable.__post_init__()
                    if child.variable <= key.variable:
                        raise ValueError("unordered decision variable")
        except (ValueError, TypeError, AttributeError):
            forbidden.add((arena._key_owner, id(key)))
