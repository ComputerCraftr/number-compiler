"""Independent structural audit for the finite-port decision arenas."""

from __future__ import annotations

from collections.abc import Iterable, Mapping
from dataclasses import dataclass
from typing import TypeGuard

from number_compiler.arithmetic.contracts.input_validation import is_exact_object_tuple
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.arithmetic.functions.finite_port_action import (
    ChoiceIndexKey,
    DecisionIndexKey,
    FinitePortActionArena,
    FinitePortActionAuditSnapshot,
    FinitePortDecisionRecord,
    PortVariable,
)
from number_compiler.arithmetic.functions.finite_port_substitution import (
    PortIndexComponent,
    SubstitutionIndexKey,
)
from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class FinitePortAudit:
    arenas: dict[ArenaToken, FinitePortActionArena]
    index_owners: set[int]
    choices: set[int]
    substitutions: set[int]
    support_tuples: set[int]
    substitution_components: set[int]


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
    substitution_components: set[int] = set()
    for root in roots:
        if type(root) is not FinitePortActionArena or root.ledger is not ledger:
            continue
        snapshot = FinitePortActionArena.audit_snapshot(root)
        if snapshot.ledger is not ledger or not all(
            _matches_store(containers, owner, identity)
            for owner, identity in (
                (snapshot.node_owner, snapshot.node_store_identity),
                (snapshot.key_owner, snapshot.key_store_identity),
            )
        ):
            continue
        arenas[snapshot.owner] = root
        # These stores contain only local decision-node indices and are
        # independently checked against the owning decision records. Treating
        # their integers as untyped numeric words makes a valid DAG look like a
        # packed digit payload.
        index_owners.update(
            (
                snapshot.key_owner,
                snapshot.choice_owner,
                snapshot.substitution_owner,
                snapshot.support_owner,
            )
        )
        _audit_choices(snapshot, containers, forbidden, choices)
        _audit_substitutions(
            snapshot,
            containers,
            forbidden,
            substitutions,
            support_tuples,
            substitution_components,
        )
        _audit_decisions(snapshot, forbidden)
    return FinitePortAudit(
        arenas,
        index_owners,
        choices,
        substitutions,
        support_tuples,
        substitution_components,
    )


def _matches_store(containers: Mapping[int, object], owner: int, identity: int) -> bool:
    container = containers.get(owner)
    return container is not None and id(container) == identity


def _valid_index(value: object, bound: int) -> bool:
    return type(value) is int and 0 <= value < bound


def _audit_choices(
    snapshot: FinitePortActionAuditSnapshot,
    containers: Mapping[int, object],
    forbidden: set[tuple[int, int]],
    approved: set[int],
) -> None:
    if not _matches_store(
        containers, snapshot.choice_owner, snapshot.choice_store_identity
    ):
        forbidden.add((snapshot.choice_owner, snapshot.choice_store_identity))
    node_count = len(snapshot.nodes)
    for key, result in snapshot.choice_rows:
        if type(key) is not ChoiceIndexKey or not all(
            _valid_index(index, node_count)
            for index in (key.condition, key.yes, key.no, result)
        ):
            forbidden.add((snapshot.choice_owner, id(key)))
        else:
            approved.add(id(key))


def _audit_substitutions(
    snapshot: FinitePortActionAuditSnapshot,
    containers: Mapping[int, object],
    forbidden: set[tuple[int, int]],
    approved: set[int],
    support_tuples: set[int],
    substitution_components: set[int],
) -> None:
    node_count = len(snapshot.nodes)
    if not _matches_store(
        containers, snapshot.substitution_owner, snapshot.substitution_store_identity
    ):
        forbidden.add(
            (snapshot.substitution_owner, snapshot.substitution_store_identity)
        )
    if not _matches_store(
        containers, snapshot.support_owner, snapshot.support_store_identity
    ):
        forbidden.add((snapshot.support_owner, snapshot.support_store_identity))
    for candidate, result in snapshot.substitution_rows:
        if not _is_substitution_index_key(candidate):
            forbidden.add((snapshot.substitution_owner, id(candidate)))
            continue
        key = candidate
        valid = (
            _valid_index(key.function, node_count)
            and type(key.components) is tuple
            and _valid_index(result, node_count)
        )
        previous: PortVariable | None = None
        if valid:
            for component in key.components:
                if (
                    type(component) is not PortIndexComponent
                    or type(component.variable) is not PortVariable
                    or not _valid_index(component.function, node_count)
                    or (previous is not None and component.variable <= previous)
                ):
                    valid = False
                    break
                previous = component.variable
        if valid:
            approved.add(id(key))
            substitution_components.update(
                id(component) for component in key.components
            )
        else:
            forbidden.add((snapshot.substitution_owner, id(key)))
    for index, variables in snapshot.support_rows:
        valid = _valid_index(index, node_count)
        checked_variables: list[PortVariable] = []
        if is_exact_object_tuple(variables):
            for variable in variables:
                if type(variable) is not PortVariable:
                    valid = False
                    break
                checked_variables.append(variable)
        else:
            valid = False
        if valid:
            valid = tuple(checked_variables) == tuple(sorted(set(checked_variables)))
        if valid:
            support_tuples.add(id(variables))
        else:
            forbidden.add((snapshot.support_owner, id(variables)))


def _audit_decisions(
    snapshot: FinitePortActionAuditSnapshot,
    forbidden: set[tuple[int, int]],
) -> None:
    nodes = snapshot.nodes
    node_count = len(nodes)
    if node_count < 2 or len(snapshot.key_rows) != node_count - 2:
        forbidden.add((snapshot.key_owner, snapshot.key_store_identity))
    for terminal in nodes[:2]:
        if (
            type(terminal) is not FinitePortDecisionRecord
            or terminal.variable is not None
            or terminal.low != 0
            or terminal.high != 0
        ):
            forbidden.add((snapshot.node_owner, id(terminal)))
    for key, local_id in snapshot.key_rows:
        if (
            type(key) is not DecisionIndexKey
            or type(local_id) is not int
            or not 2 <= local_id < node_count
            or not _valid_index(key.low, local_id)
            or not _valid_index(key.high, local_id)
        ):
            forbidden.add((snapshot.key_owner, id(key)))
            continue
        node = nodes[local_id]
        if (
            type(node) is not FinitePortDecisionRecord
            or type(key.variable) is not PortVariable
            or key.low == key.high
            or (node.variable, node.low, node.high) != (key.variable, key.low, key.high)
        ):
            forbidden.add((snapshot.key_owner, id(key)))
            continue
        try:
            key.variable.__post_init__()
            for child_id in (key.low, key.high):
                child = nodes[child_id]
                if type(child) is not FinitePortDecisionRecord:
                    raise ValueError("invalid decision child")
                if child.variable is not None:
                    child.variable.__post_init__()
                    if child.variable <= key.variable:
                        raise ValueError("unordered decision variable")
        except (ValueError, TypeError, AttributeError):
            forbidden.add((snapshot.key_owner, id(key)))


def _is_substitution_index_key(value: object) -> TypeGuard[SubstitutionIndexKey]:
    return type(value) is SubstitutionIndexKey
