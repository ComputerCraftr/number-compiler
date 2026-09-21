"""Explicit audit for the retired residue-based reverse temporal experiment."""

from __future__ import annotations

from dataclasses import dataclass, fields, is_dataclass

from devtools.experiments.reverse_add.coordinate_program import (
    ReverseCoordinateProgram,
    ReverseCoordinateProgramArena,
)
from devtools.experiments.reverse_add.field_action import ReverseFieldActionArena
from devtools.experiments.reverse_add.higher_interface import (
    ReverseHigherInterfaceCompilation,
    ReverseHigherInterfaceCompiler,
)
from number_compiler.arithmetic.automata.symmetry_powering import ActionTransform
from number_compiler.hashlife.actions.field_actions import (
    CoordinateOutputMorphismID,
    FieldCellActionID,
)
from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class ReverseTemporalExperimentAudit:
    invalid: frozenset[tuple[int, int]]


def _bounded_semantic_key(root: object) -> bool:
    pending = [root]
    visited: set[int] = set()
    units = 0
    while pending:
        value = pending.pop()
        units += 1
        if units > 256:
            return False
        if value is None or type(value) is bool:
            continue
        if type(value) is int:
            if abs(value).bit_length() > 64:
                return False
            continue
        if isinstance(value, (str, bytes)):
            if len(value) > 256:
                return False
            continue
        identity = id(value)
        if identity in visited:
            continue
        visited.add(identity)
        if type(value) is tuple:
            pending.extend(value)
        elif is_dataclass(value) and not isinstance(value, type):
            pending.extend(getattr(value, field.name) for field in fields(value))
        else:
            return False
    return True


def audit_reverse_temporal_experiment(
    ledger: ResourceLedger,
) -> ReverseTemporalExperimentAudit:
    """Validate only the explicitly imported research executor owners."""
    containers = dict(ledger.iter_containers())
    invalid: set[tuple[int, int]] = set()
    for root in ledger.iter_execution_roots():
        if type(root) is ReverseFieldActionArena:
            field_stores = (
                (root._action_owner, root._actions),
                (root._action_key_owner, root._action_keys),
                (root._residual_owner, root._residuals),
                (root._residual_key_owner, root._residual_keys),
                (root._output_owner, root._outputs),
                (root._output_key_owner, root._output_keys),
                (root._compose_owner, root._compose),
                (root._transform_owner, root._transforms),
                (root._witness_owner, root._witnesses),
            )
            valid_root = root.ledger is ledger and all(
                containers.get(owner) is store for owner, store in field_stores
            )
            if not valid_root:
                invalid.add((root._action_owner, id(root)))
                continue
            try:
                for index, field_action in enumerate(root._actions):
                    reference = FieldCellActionID(root.owner, root._ACTION_KIND, index)
                    valid = root.resolve(reference) is field_action
                    block = root._canonical_block(root._block(field_action))
                    valid &= block.innovation == field_action.innovation
                    root._residual_key(field_action.residual)
                    root._output_key(field_action.output)
                    field_action.geometry.__post_init__()
                    if not valid:
                        invalid.add((root._action_owner, id(field_action)))
                for key, reference in root._action_keys.items():
                    field_action = root.resolve(reference)
                    block = root._canonical_block(root._block(field_action))
                    valid = key == root._action_key(
                        field_action.base,
                        block,
                        field_action.carry_forward,
                        field_action.carry_backward,
                        field_action.residual,
                        field_action.output,
                        field_action.geometry,
                    )
                    if not valid:
                        invalid.add((root._action_key_owner, id(key)))
            except (AttributeError, IndexError, KeyError, TypeError, ValueError):
                invalid.add((root._action_owner, id(root)))
            for residual_key, residual_reference in root._residual_keys.items():
                try:
                    root._validate_semantic_key(residual_key)
                    valid = root._residual_key(residual_reference) == residual_key
                    valid &= _bounded_semantic_key(residual_key)
                except (AttributeError, IndexError, KeyError, TypeError, ValueError):
                    valid = False
                if not valid:
                    invalid.add((root._residual_key_owner, id(residual_key)))
            for output_key, output_reference in root._output_keys.items():
                try:
                    root._validate_semantic_key(output_key)
                    valid = root._output_key(output_reference) == output_key
                    valid &= _bounded_semantic_key(output_key)
                except (AttributeError, IndexError, KeyError, TypeError, ValueError):
                    valid = False
                if not valid:
                    invalid.add((root._output_key_owner, id(output_key)))
            for composition_key, result in root._compose.items():
                try:
                    valid = (
                        type(composition_key) is tuple
                        and len(composition_key) == 2
                        and all(
                            type(item) is FieldCellActionID for item in composition_key
                        )
                    )
                    root.resolve(composition_key[0])
                    root.resolve(composition_key[1])
                    root.resolve(result)
                except (AttributeError, IndexError, KeyError, TypeError, ValueError):
                    valid = False
                if not valid:
                    invalid.add((root._compose_owner, id(composition_key)))
            for transform_key, result in root._transforms.items():
                try:
                    valid = (
                        type(transform_key) is tuple
                        and len(transform_key) == 2
                        and type(transform_key[0]) is FieldCellActionID
                        and type(transform_key[1]) is ActionTransform
                    )
                    root.resolve(transform_key[0])
                    ActionTransform(transform_key[1])
                    root.resolve(result)
                except (AttributeError, IndexError, KeyError, TypeError, ValueError):
                    valid = False
                if not valid:
                    invalid.add((root._transform_owner, id(transform_key)))
            for parent, witness in root._witnesses.items():
                try:
                    valid = (
                        type(parent) is FieldCellActionID
                        and type(witness) is tuple
                        and len(witness) == 2
                    )
                    root.resolve(parent)
                    valid &= all(root.resolve(child) is not None for child in witness)
                except (AttributeError, IndexError, KeyError, TypeError, ValueError):
                    valid = False
                if not valid:
                    invalid.add((root._witness_owner, id(witness)))
        elif type(root) is ReverseCoordinateProgramArena:
            coordinate_stores = root._nodes, root._keys, root._compose
            valid = root.ledger is ledger and all(
                any(container is store for container in containers.values())
                for store in coordinate_stores
            )
            try:
                for index, program in enumerate(root._nodes):
                    valid &= type(program) is ReverseCoordinateProgram
                    program.__post_init__()
                    valid &= program.base == root.base
                    valid &= (
                        root.resolve(
                            CoordinateOutputMorphismID(root.owner, root._KIND, index)
                        )
                        is program
                    )
                    valid &= root._keys.get(program) == index
                    if program.atom is not None:
                        valid &= _bounded_semantic_key(program.atom)
            except (AttributeError, IndexError, KeyError, TypeError, ValueError):
                valid = False
            for coordinate_key, coordinate_result in root._compose.items():
                try:
                    composition_valid = (
                        type(coordinate_key) is tuple
                        and len(coordinate_key) == 2
                        and all(
                            type(item) is CoordinateOutputMorphismID
                            for item in coordinate_key
                        )
                    )
                    first = root.resolve(coordinate_key[0])
                    second = root.resolve(coordinate_key[1])
                    actual = root.resolve(coordinate_result)
                    composition_valid &= first.executable and second.executable
                    composition_valid &= actual == ReverseCoordinateProgram(
                        root.base,
                        first.pair_steps + second.pair_steps,
                        first.normalized or second.normalized,
                    )
                except (AttributeError, IndexError, KeyError, TypeError, ValueError):
                    composition_valid = False
                valid &= composition_valid
            if not valid:
                invalid.add((root._node_owner, id(root)))
        elif type(root) is ReverseHigherInterfaceCompiler:
            valid = (
                root.ledger is ledger
                and containers.get(root._cache_owner) is root._cache
            )
            for action_reference, compilation in root._cache.items():
                item_valid = (
                    type(action_reference) is FieldCellActionID
                    and type(compilation) is ReverseHigherInterfaceCompilation
                    and compilation.action == action_reference
                )
                try:
                    root.actions.validate_action(action_reference)
                    root.interfaces.interface(compilation.signature)
                    resolved = root.interfaces.resolve(compilation.interface)
                    item_valid &= resolved.signature == compilation.signature
                    root.actions._output_key(compilation.output_morphism)
                    root.semantics.expression(compilation.left)
                    root.semantics.expression(compilation.symbol)
                    root.semantics.expression(compilation.right)
                except (AttributeError, IndexError, KeyError, TypeError, ValueError):
                    item_valid = False
                valid &= item_valid
            if not valid:
                invalid.add((root._cache_owner, id(root)))
    return ReverseTemporalExperimentAudit(frozenset(invalid))


__all__ = ["ReverseTemporalExperimentAudit", "audit_reverse_temporal_experiment"]
