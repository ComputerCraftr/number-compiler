"""Boolean composition with one canonical implementation owner."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.resources.metric_keys import (
    hashlife_interfaces as _interfaces_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.interfaces.semantic_bits import BooleanCircuit


@dataclass(frozen=True, slots=True)
class _CompositionKey:
    root: int
    # Integer roots are aligned exactly with tx.node(root).support. The root
    # identity binds this positional layout within one immutable transaction.
    environment: tuple[int, ...]


def substitute_boolean_fused(
    circuit: BooleanCircuit, root: int, replacements: Mapping[PortVariable, int]
) -> int:
    """Compose correlated inputs by one ordered external-variable traversal.

    This cofactoring explores reduced function DAGs, never integer assignments
    or a Cartesian port universe. Only final ordered nodes are constructed.
    """
    from number_compiler.hashlife.interfaces.semantic_bits import (
        BooleanCircuit,
        substitute_boolean,
    )

    tx, ledger = circuit.tx, circuit.tx.arena.ledger
    done = circuit._fused_substitutions

    def project(
        before: int, after: int, environment: tuple[int, ...]
    ) -> tuple[int, ...]:
        if before == after:
            return environment
        pair = before, after
        indices = circuit._fused_projections.get(pair)
        ledger.bump(_interfaces_keys.SEMANTIC_BIT_FUSED_PROJECTION_REQUESTS)
        if indices is None:
            source, target = tx.node(before).support, tx.node(after).support
            selected: list[int] = []
            cursor = 0
            for variable in target:
                while cursor < len(source) and source[cursor] < variable:
                    cursor += 1
                    ledger.bump(
                        _interfaces_keys.SEMANTIC_BIT_FUSED_PROJECTION_SUPPORT_VISITS
                    )
                ledger.bump(
                    _interfaces_keys.SEMANTIC_BIT_FUSED_PROJECTION_SUPPORT_VISITS
                )
                if cursor == len(source) or source[cursor] != variable:
                    raise AssertionError(
                        "cofactor support must be a subset of its canonical parent"
                    )
                selected.append(cursor)
            indices = tuple(selected)
            ledger.bump(
                _interfaces_keys.SEMANTIC_BIT_FUSED_PROJECTION_BUILD_SLOTS_PEAK,
                max(
                    0,
                    len(selected)
                    + len(indices)
                    - ledger.counters.get(
                        _interfaces_keys.SEMANTIC_BIT_FUSED_PROJECTION_BUILD_SLOTS_PEAK,
                        0,
                    ),
                ),
            )
            circuit._fused_projections[pair] = indices
            circuit._fused_projection_slots += len(indices)
            ledger.bump(_interfaces_keys.SEMANTIC_BIT_FUSED_PROJECTION_EVALUATIONS)
            ledger.bump(
                _interfaces_keys.SEMANTIC_BIT_FUSED_PROJECTION_CACHE_ENTRIES_PEAK,
                max(
                    0,
                    len(circuit._fused_projections)
                    - ledger.counters.get(
                        _interfaces_keys.SEMANTIC_BIT_FUSED_PROJECTION_CACHE_ENTRIES_PEAK,
                        0,
                    ),
                ),
            )
            ledger.bump(
                _interfaces_keys.SEMANTIC_BIT_FUSED_PROJECTION_INDEX_SLOTS_PEAK,
                max(
                    0,
                    circuit._fused_projection_slots
                    - ledger.counters.get(
                        _interfaces_keys.SEMANTIC_BIT_FUSED_PROJECTION_INDEX_SLOTS_PEAK,
                        0,
                    ),
                ),
            )
        else:
            ledger.bump(_interfaces_keys.SEMANTIC_BIT_FUSED_PROJECTION_HITS)
        result = tuple(environment[index] for index in indices)
        ledger.bump(
            _interfaces_keys.SEMANTIC_BIT_FUSED_PROJECTION_ARGUMENT_VISITS,
            len(indices),
        )
        ledger.bump(
            _interfaces_keys.SEMANTIC_BIT_FUSED_ENVIRONMENT_BINDINGS_CREATED,
            len(result),
        )
        ledger.bump(
            _interfaces_keys.SEMANTIC_BIT_FUSED_NORMALIZATION_BINDINGS_PEAK,
            max(
                0,
                len(environment)
                + len(result)
                - ledger.counters.get(
                    _interfaces_keys.SEMANTIC_BIT_FUSED_NORMALIZATION_BINDINGS_PEAK,
                    0,
                ),
            ),
        )
        return result

    def normalized(identity: int, environment: tuple[int, ...]) -> _CompositionKey:
        node = tx.node(identity)
        while node.variable is not None:
            # Ordered BDD nodes put their own split first in their support.
            argument = tx.node(environment[0])
            ledger.bump(_interfaces_keys.SEMANTIC_BIT_FUSED_NORMALIZATION_VISITS)
            ledger.bump(
                _interfaces_keys.SEMANTIC_BIT_FUSED_NORMALIZATION_BINDING_VISITS
            )
            if argument.terminal is None:
                break
            if argument.terminal.kind != "atom":
                raise AssertionError(
                    "factored argument bits must be total Boolean functions"
                )
            child = node.high if argument.terminal.value else node.low
            environment = project(identity, child, environment)
            identity, node = child, tx.node(child)
        return _CompositionKey(identity, environment)

    original = tx.node(root)
    constants = tuple(
        (variable, tx.node(value).terminal)
        for variable, value in replacements.items()
        if tx.node(value).terminal is not None
    )
    if constants:
        primitive = circuit._cofactor_circuits.get(original.signature.inputs)
        if primitive is None:
            primitive = BooleanCircuit(tx.arena, original.signature.inputs, tx)
            circuit._cofactor_circuits[original.signature.inputs] = primitive
            ledger.bump(
                _interfaces_keys.SEMANTIC_BIT_FUSED_COFACTOR_CONTEXTS_PEAK,
                max(
                    0,
                    len(circuit._cofactor_circuits)
                    - ledger.counters.get(
                        _interfaces_keys.SEMANTIC_BIT_FUSED_COFACTOR_CONTEXTS_PEAK,
                        0,
                    ),
                ),
            )
        constant_mapping = {}
        for variable, terminal in constants:
            if terminal is None or terminal.kind != "atom":
                raise AssertionError(
                    "factored argument bits must be total Boolean functions"
                )
            constant_mapping[variable] = (
                primitive.one if terminal.value else primitive.zero
            )
        root = substitute_boolean(primitive, root, constant_mapping)
        original = tx.node(root)
    environment = tuple(
        replacements[variable]
        if variable in replacements
        else tx.bit(circuit.inputs, variable)
        for variable in original.support
    )
    ledger.bump(
        _interfaces_keys.SEMANTIC_BIT_FUSED_ENVIRONMENT_BINDINGS_CREATED,
        len(environment),
    )
    first = normalized(root, environment)
    pending = [(first, False)]
    children: dict[
        _CompositionKey, tuple[PortVariable, _CompositionKey, _CompositionKey]
    ] = {}
    while pending:
        ledger.bump(
            _interfaces_keys.SEMANTIC_BIT_FUSED_WORKSPACE_PEAK,
            max(
                0,
                len(pending)
                + len(done)
                + len(children)
                - ledger.counters.get(
                    _interfaces_keys.SEMANTIC_BIT_FUSED_WORKSPACE_PEAK, 0
                ),
            ),
        )
        ledger.bump(
            _interfaces_keys.SEMANTIC_BIT_FUSED_RETAINED_ENVIRONMENT_BINDINGS_PEAK,
            max(
                0,
                circuit._fused_retained_bindings
                - ledger.counters.get(
                    _interfaces_keys.SEMANTIC_BIT_FUSED_RETAINED_ENVIRONMENT_BINDINGS_PEAK,
                    0,
                ),
            ),
        )
        key, ready = pending.pop()
        ledger.bump(_interfaces_keys.SEMANTIC_BIT_FUSED_FRAMES)
        if key in done:
            ledger.bump(_interfaces_keys.SEMANTIC_BIT_FUSED_SHARED_HITS)
            continue
        node = tx.node(key.root)
        if node.terminal is not None:
            done[key] = tx.terminal(circuit.signature, node.terminal)
            circuit._fused_retained_bindings += len(key.environment)
        elif ready:
            variable, low, high = children.pop(key)
            done[key] = tx.decision(circuit.signature, variable, done[low], done[high])
            circuit._fused_retained_bindings += len(key.environment)
        else:
            split = circuit._fused_splits.get(key.environment)
            ledger.bump(_interfaces_keys.SEMANTIC_BIT_FUSED_SPLIT_REQUESTS)
            if split is None:
                arguments = tuple(tx.node(value) for value in key.environment)
                ledger.bump(
                    _interfaces_keys.SEMANTIC_BIT_FUSED_BRANCH_NODE_REFERENCES_PEAK,
                    max(
                        0,
                        len(arguments)
                        - ledger.counters.get(
                            _interfaces_keys.SEMANTIC_BIT_FUSED_BRANCH_NODE_REFERENCES_PEAK,
                            0,
                        ),
                    ),
                )
                variable = min(
                    argument.variable
                    for argument in arguments
                    if argument.variable is not None
                )
                low_environment = tuple(
                    argument.low if argument.variable == variable else value
                    for value, argument in zip(key.environment, arguments, strict=True)
                )
                high_environment = tuple(
                    argument.high if argument.variable == variable else value
                    for value, argument in zip(key.environment, arguments, strict=True)
                )
                split = variable, low_environment, high_environment
                circuit._fused_splits[key.environment] = split
                ledger.bump(_interfaces_keys.SEMANTIC_BIT_FUSED_SPLIT_EVALUATIONS)
                ledger.bump(
                    _interfaces_keys.SEMANTIC_BIT_FUSED_SPLIT_CACHE_ENTRIES_PEAK,
                    max(
                        0,
                        len(circuit._fused_splits)
                        - ledger.counters.get(
                            _interfaces_keys.SEMANTIC_BIT_FUSED_SPLIT_CACHE_ENTRIES_PEAK,
                            0,
                        ),
                    ),
                )
                ledger.bump(
                    _interfaces_keys.SEMANTIC_BIT_FUSED_ENVIRONMENT_BINDINGS_CREATED,
                    len(low_environment) + len(high_environment),
                )
                ledger.bump(
                    _interfaces_keys.SEMANTIC_BIT_FUSED_BRANCH_ENVIRONMENT_BINDINGS_PEAK,
                    max(
                        0,
                        len(key.environment)
                        + len(low_environment)
                        + len(high_environment)
                        - ledger.counters.get(
                            _interfaces_keys.SEMANTIC_BIT_FUSED_BRANCH_ENVIRONMENT_BINDINGS_PEAK,
                            0,
                        ),
                    ),
                )
            else:
                ledger.bump(_interfaces_keys.SEMANTIC_BIT_FUSED_SPLIT_HITS)
            variable, low_environment, high_environment = split
            low = normalized(key.root, low_environment)
            high = normalized(key.root, high_environment)
            children[key] = variable, low, high
            pending.extend(((key, True), (high, False), (low, False)))
    ledger.bump(
        _interfaces_keys.SEMANTIC_BIT_FUSED_RETAINED_ENVIRONMENT_BINDINGS_PEAK,
        max(
            0,
            circuit._fused_retained_bindings
            - ledger.counters.get(
                _interfaces_keys.SEMANTIC_BIT_FUSED_RETAINED_ENVIRONMENT_BINDINGS_PEAK,
                0,
            ),
        ),
    )
    return done[first]
