"""Independent validation of retained recursive higher semantic records."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Protocol

from number_compiler.resources.higher_readonly import (
    audit_identity_index,
    audit_validate_action,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_contracts import PayloadAuditContractAudit


@dataclass(frozen=True, slots=True)
class HigherPayloadAudit:
    approved: frozenset[int]
    invalid: frozenset[tuple[int, int]]


class _NodeKeyStoreAudit(Protocol):
    @property
    def ledger(self) -> ResourceLedger: ...

    @property
    def node_owner(self) -> int: ...

    @property
    def node_store(self) -> object: ...

    @property
    def key_owner(self) -> int: ...

    @property
    def key_store(self) -> object: ...


def audit_higher_payloads(
    ledger: ResourceLedger,
    contracts: PayloadAuditContractAudit | None = None,
) -> HigherPayloadAudit:
    """Validate issued higher DAG records through their owning arenas."""
    if contracts is None or not contracts.is_current_for(ledger):
        contracts = ledger.audit_payload_contracts()
    approved: set[int] = {value for _, value in contracts.approved}
    invalid: set[tuple[int, int]] = set(contracts.invalid)
    legacy_prefixes = (
        "number_compiler.hashlife.execution.continuations.",
        "number_compiler.hashlife.execution.recursive_outputs",
    )
    if not any(
        type(root).__module__.startswith(legacy_prefixes)
        for root in ledger.iter_execution_roots()
    ):
        return HigherPayloadAudit(frozenset(approved), frozenset(invalid))

    from number_compiler.hashlife.execution.continuations.higher_bimachine import (
        HigherBimachineRuntime,
        HigherEmitOperation,
        HigherInitialOperation,
        HigherStepOperation,
        HigherTransfer,
    )
    from number_compiler.hashlife.execution.continuations.higher_interfaces import (
        HigherInterfaceRecord,
        HigherLocalInterfaceArena,
        HigherMacroComponents,
        HigherMacroInterface,
    )
    from number_compiler.hashlife.execution.continuations.higher_macro_composer import (
        HigherSpatialMacroComposer,
        MacroBindingKey,
        SourceBoundHigherMacro,
    )
    from number_compiler.hashlife.execution.continuations.higher_semantic import (
        HigherSemanticArena,
    )
    from number_compiler.hashlife.execution.continuations.higher_summaries import (
        HigherSummaryArena,
    )
    from number_compiler.hashlife.execution.continuations.higher_temporal_image import (
        HigherTemporalImageArena,
    )
    from number_compiler.hashlife.execution.continuations.higher_temporal_provider import (
        HigherTemporalProviderEvaluator,
    )
    from number_compiler.hashlife.execution.continuations.higher_types import (
        FieldStateSort,
        HigherExpression,
        HigherFunction,
    )
    from number_compiler.hashlife.execution.continuations.higher_values import (
        RuntimeEnvironment,
        RuntimeValueArena,
    )
    from number_compiler.hashlife.execution.field_images import (
        SourceCellID,
        SourceForestID,
    )
    from number_compiler.hashlife.execution.recursive_outputs import (
        RecursiveCoordinateMorphismArena,
        RecursiveOutputBindingSource,
        RecursiveOutputBranch,
        RecursiveOutputLeaf,
        RecursiveOutputSource,
        RecursiveOutputTemporal,
    )
    from number_compiler.hashlife.interfaces.semantic_interfaces import (
        SemanticBoundaryArena,
        SemanticBoundaryRecord,
    )
    from number_compiler.resources.higher_operation_payload import (
        valid_higher_operation,
    )
    from number_compiler.resources.higher_value_record_audit import (
        valid_runtime_value_record,
    )

    containers = dict(ledger.iter_containers())

    def store(owner: int, value: object) -> bool:
        return containers.get(owner) is value

    def valid_node_key_store(snapshot: _NodeKeyStoreAudit) -> bool:
        return (
            snapshot.ledger is ledger
            and store(snapshot.node_owner, snapshot.node_store)
            and store(snapshot.key_owner, snapshot.key_store)
        )

    for root in ledger.iter_execution_roots():
        if type(root) is HigherSemanticArena:
            semantic_snapshot = root.audit_snapshot()
            valid_root = semantic_snapshot.ledger is ledger and all(
                (
                    store(
                        semantic_snapshot.expression_owner,
                        semantic_snapshot.expression_store,
                    ),
                    store(
                        semantic_snapshot.expression_key_owner,
                        semantic_snapshot.expression_key_store,
                    ),
                    store(
                        semantic_snapshot.expression_free_owner,
                        semantic_snapshot.expression_free_store,
                    ),
                    store(
                        semantic_snapshot.function_owner,
                        semantic_snapshot.function_store,
                    ),
                    store(
                        semantic_snapshot.function_key_owner,
                        semantic_snapshot.function_key_store,
                    ),
                    store(
                        semantic_snapshot.rewrite_owner,
                        semantic_snapshot.rewrite_store,
                    ),
                )
            )
            expressions_valid = valid_root
            for index, expression_record in enumerate(semantic_snapshot.expressions):
                valid = valid_root and type(expression_record) is HigherExpression
                free: tuple[int, ...] = ()
                try:
                    valid &= (
                        root.expression(root.expression_id(index)) is expression_record
                    )
                    root.validate_sort(expression_record.sort, readonly=True)
                    valid &= type(expression_record.children) is tuple and all(
                        type(child) is int and 0 <= child < index
                        for child in expression_record.children
                    )
                    valid &= type(
                        expression_record.side
                    ) is int and expression_record.side in (-1, 0, 1)
                    valid &= type(expression_record.value) is int
                    valid &= (
                        type(expression_record.role) is str
                        and len(expression_record.role) <= 128
                    )
                    if expression_record.action is not None:
                        audit_validate_action(root.schema, expression_record.action)
                    if expression_record.function is not None:
                        root.function_record(expression_record.function)
                    valid &= audit_identity_index(
                        semantic_snapshot.expression_keys,
                        expression_record,
                        index,
                    )
                    free = semantic_snapshot.expression_free_ids[index]
                    valid &= type(free) is tuple and all(
                        type(item) is int and 0 <= item <= index for item in free
                    )
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                target = approved if valid else None
                if target is not None:
                    target.update(
                        (id(expression_record), id(expression_record.sort), id(free))
                    )
                else:
                    invalid.add(
                        (semantic_snapshot.expression_owner, id(expression_record))
                    )
                    expressions_valid = False
            functions_valid = valid_root
            for index, function_record in enumerate(semantic_snapshot.functions):
                valid = valid_root and type(function_record) is HigherFunction
                try:
                    valid &= (
                        root.function_record(root.function_id(index)) is function_record
                    )
                    root.validate_sort(function_record.signature, readonly=True)
                    parameter = root.expression(function_record.parameter)
                    body = root.expression(function_record.body)
                    valid &= parameter.kind == "bound"
                    valid &= type(parameter.sort) is FieldStateSort
                    valid &= body.sort == function_record.signature.codomain
                    valid &= parameter.sort == function_record.signature.domain
                    valid &= type(function_record.free_variables) is tuple
                    for variable in function_record.free_variables:
                        root.expression(variable)
                    valid &= type(function_record.parameter_used) is bool
                    valid &= audit_identity_index(
                        semantic_snapshot.function_keys,
                        function_record,
                        index,
                    )
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.update(
                        (id(function_record), id(function_record.signature))
                    )
                else:
                    invalid.add((semantic_snapshot.function_owner, id(function_record)))
                    functions_valid = False
            rewrites_valid = valid_root
            for rewrite, result in semantic_snapshot.rewrites.items():
                valid = all(
                    type(item) is int
                    for item in (rewrite.root, rewrite.variable, rewrite.replacement)
                )
                try:
                    valid &= (
                        min(rewrite.root, rewrite.variable, rewrite.replacement) >= 0
                    )
                    root.expression(root.expression_id(rewrite.root))
                    root.expression(root.expression_id(rewrite.variable))
                    root.expression(root.expression_id(rewrite.replacement))
                    root.expression(result)
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(rewrite))
                else:
                    invalid.add((semantic_snapshot.rewrite_owner, id(rewrite)))
                    rewrites_valid = False
            if expressions_valid and functions_valid and rewrites_valid:
                approved.update(
                    (
                        id(semantic_snapshot.expression_store),
                        id(semantic_snapshot.expression_key_store),
                        id(semantic_snapshot.expression_free_store),
                        id(semantic_snapshot.function_store),
                        id(semantic_snapshot.function_key_store),
                        id(semantic_snapshot.rewrite_store),
                    )
                )
        elif type(root) is HigherLocalInterfaceArena:
            interface_snapshot = root.audit_snapshot()
            valid_root = interface_snapshot.ledger is ledger and all(
                (
                    store(
                        interface_snapshot.signature_owner,
                        interface_snapshot.signature_store,
                    ),
                    store(
                        interface_snapshot.signature_key_owner,
                        interface_snapshot.signature_key_store,
                    ),
                    store(interface_snapshot.node_owner, interface_snapshot.node_store),
                    store(interface_snapshot.key_owner, interface_snapshot.key_store),
                )
            )
            signatures_valid = valid_root
            for index, interface_record in enumerate(interface_snapshot.signatures):
                valid = valid_root and type(interface_record) is HigherMacroInterface
                found_signature = None
                try:
                    root.validate_interface(interface_record, readonly=True)
                    valid &= (
                        root.interface(root.signature_id(index)) is interface_record
                    )
                    found_signature = interface_snapshot.signature_keys.get(
                        interface_record
                    )
                    valid &= (
                        found_signature is not None
                        and found_signature.local_id == index
                    )
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(interface_record))
                    approved.update(id(output) for output in interface_record.outputs)
                    approved.update(
                        id(getattr(output, name))
                        for output in interface_record.outputs
                        if type(output).__name__ == "HigherMorphismSort"
                        for name in ("owner", "kind")
                    )
                    if found_signature is not None:
                        approved.add(id(found_signature))
                else:
                    invalid.add(
                        (interface_snapshot.signature_owner, id(interface_record))
                    )
                    signatures_valid = False
            interfaces_valid = valid_root
            for index, node_record in enumerate(interface_snapshot.nodes):
                valid = valid_root and type(node_record) is HigherInterfaceRecord
                found_interface = None
                try:
                    valid &= type(node_record.components) is HigherMacroComponents
                    root.validate_components(
                        node_record.signature, node_record.components
                    )
                    valid &= root.resolve(root.local_interface_id(index)) is node_record
                    found_interface = interface_snapshot.keys.get(node_record)
                    valid &= (
                        found_interface is not None
                        and found_interface.local_id == index
                    )
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.update((id(node_record), id(node_record.components)))
                    approved.add(id(node_record.signature))
                    approved.update(
                        id(component)
                        for component in node_record.components.functions()
                    )
                    if found_interface is not None:
                        approved.add(id(found_interface))
                else:
                    invalid.add((interface_snapshot.node_owner, id(node_record)))
                    interfaces_valid = False
            if signatures_valid and interfaces_valid:
                approved.update(
                    (
                        id(interface_snapshot.signature_store),
                        id(interface_snapshot.signature_key_store),
                        id(interface_snapshot.node_store),
                        id(interface_snapshot.key_store),
                    )
                )
        elif type(root) is RecursiveCoordinateMorphismArena:
            output_snapshot = root.audit_snapshot()
            valid_root = valid_node_key_store(output_snapshot)
            records_valid = valid_root
            for local_id, output_record in output_snapshot.nodes.items():
                valid = type(local_id) is int and type(output_record) in (
                    RecursiveOutputSource,
                    RecursiveOutputBindingSource,
                    RecursiveOutputLeaf,
                    RecursiveOutputBranch,
                    RecursiveOutputTemporal,
                )
                try:
                    valid &= (
                        root.resolve(root.handle_for_local_id(local_id))
                        is output_record
                    )
                    valid &= output_snapshot.keys.get(output_record) == local_id
                    if type(output_record) is RecursiveOutputSource:
                        root.validate_source(output_record.source)
                    elif type(output_record) is RecursiveOutputBindingSource:
                        if type(output_record.source) is SourceCellID:
                            root.validate_source(output_record.source)
                        elif type(output_record.source) is SourceForestID:
                            pass
                        else:
                            valid = False
                    elif type(output_record) is RecursiveOutputLeaf:
                        root.interfaces.resolve(output_record.scalar_interface)
                    elif type(output_record) is RecursiveOutputBranch:
                        branch = output_record
                        left = root.resolve(branch.left)
                        right = root.resolve(branch.right)
                        root.interfaces.resolve(branch.left_interface)
                        root.interfaces.resolve(branch.right_interface)
                        valid &= (
                            type(branch.left_width) is int
                            and branch.left_width > 0
                            and type(branch.spatial_complete) is bool
                            and branch.spatial_complete
                            == (
                                (
                                    False
                                    if type(left) is RecursiveOutputTemporal
                                    else left.spatial_complete
                                    if type(left) is RecursiveOutputBranch
                                    else True
                                )
                                and (
                                    False
                                    if type(right) is RecursiveOutputTemporal
                                    else right.spatial_complete
                                    if type(right) is RecursiveOutputBranch
                                    else True
                                )
                            )
                        )
                    elif type(output_record) is RecursiveOutputTemporal:
                        temporal_node = output_record
                        root.resolve(temporal_node.provider)
                        root.validate_output_action(temporal_node.action)
                        root.validate_output_interface(temporal_node.interface)
                    else:
                        valid = False
                except (TypeError, ValueError, KeyError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(output_record))
                    approved.update(
                        id(getattr(output_record, name))
                        for name in output_record.__dataclass_fields__
                    )
                else:
                    invalid.add((output_snapshot.node_owner, id(output_record)))
                    records_valid = False
            if records_valid:
                approved.update(
                    (id(output_snapshot.node_store), id(output_snapshot.key_store))
                )
        elif type(root) is HigherTemporalProviderEvaluator:
            provider_snapshot = root.audit_snapshot()
            valid_root = provider_snapshot.ledger is ledger and store(
                provider_snapshot.binding_owner, provider_snapshot.binding_store
            )
            try:
                root.validate_authority()
            except (TypeError, ValueError, KeyError, AttributeError):
                valid_root = False
            if not valid_root:
                invalid.add(
                    (
                        provider_snapshot.binding_owner,
                        id(provider_snapshot.binding_store),
                    )
                )
            bindings_valid = valid_root
            for output, provider_binding in provider_snapshot.bindings.items():
                valid = (
                    valid_root
                    and type(provider_binding) is tuple
                    and len(provider_binding) == 2
                )
                try:
                    root.validate_output(output)
                    source, provider_action = provider_binding
                    audit_validate_action(root.runtime.schema, provider_action)
                    if type(source) is SourceCellID:
                        root.runtime.sources.resolve(source)
                    elif type(source) is SourceForestID:
                        root.runtime.sources.resolve_forest(source)
                    else:
                        valid = False
                except (TypeError, ValueError, KeyError, AttributeError):
                    valid = False
                if valid:
                    approved.update((id(output), id(provider_binding)))
                else:
                    invalid.add((provider_snapshot.binding_owner, id(provider_binding)))
                    bindings_valid = False
            if bindings_valid:
                approved.add(id(provider_snapshot.binding_store))
        elif type(root) is HigherTemporalImageArena:
            from number_compiler.resources.higher_image_payload_audit import (
                audit_temporal_image_owner,
            )

            image_approved, image_invalid = audit_temporal_image_owner(
                root, ledger, containers
            )
            approved.update(image_approved)
            invalid.update(image_invalid)
        elif type(root) is HigherSpatialMacroComposer:
            macro_snapshot = root.audit_snapshot()
            valid_root = macro_snapshot.ledger is ledger and store(
                macro_snapshot.binding_owner, macro_snapshot.binding_store
            )
            try:
                root.declaration()
            except (TypeError, ValueError, KeyError, AttributeError):
                valid_root = False
            if not valid_root:
                invalid.add(
                    (macro_snapshot.binding_owner, id(macro_snapshot.binding_store))
                )
            bindings_valid = valid_root
            for key, macro in macro_snapshot.bindings.items():
                valid = (
                    valid_root
                    and type(key) is MacroBindingKey
                    and type(macro) is SourceBoundHigherMacro
                )
                try:
                    audit_validate_action(root.semantics.schema, key.action)
                    root.sources.binding_extent(key.source)
                    root.interfaces.resolve(macro.interface)
                    root.outputs.resolve(macro.output)
                    valid &= all(
                        type(value) is int and value >= 0
                        for value in (macro.width, macro.source_extent)
                    )
                    valid &= macro.source_extent <= macro.width
                    for component in (
                        macro.activity,
                        macro.first_active,
                        macro.last_active,
                        macro.extent,
                        macro.growth,
                    ):
                        root.semantics.expression(component)
                except (TypeError, ValueError, KeyError, AttributeError):
                    valid = False
                if valid:
                    approved.update((id(key), id(macro)))
                    approved.update(
                        (
                            id(key.action),
                            id(key.source),
                            id(macro.interface),
                            id(macro.output),
                            id(macro.width),
                            id(macro.source_extent),
                            id(macro.activity),
                            id(macro.first_active),
                            id(macro.last_active),
                            id(macro.extent),
                            id(macro.growth),
                        )
                    )
                else:
                    invalid.add((macro_snapshot.binding_owner, id(key)))
                    bindings_valid = False
            if bindings_valid:
                approved.add(id(macro_snapshot.binding_store))
        elif type(root) is RuntimeValueArena:
            value_snapshot = root.audit_snapshot()
            semantic_owner = next(
                (
                    candidate
                    for candidate in ledger.iter_execution_roots()
                    if type(candidate) is HigherSemanticArena
                    and candidate.runtime_values is root
                ),
                None,
            )
            valid_root = value_snapshot.ledger is ledger and all(
                (
                    store(value_snapshot.record_owner, value_snapshot.record_store),
                    store(value_snapshot.key_owner, value_snapshot.key_store),
                    store(
                        value_snapshot.environment_owner,
                        value_snapshot.environment_store,
                    ),
                    store(
                        value_snapshot.environment_key_owner,
                        value_snapshot.environment_key_store,
                    ),
                    store(value_snapshot.memo_owner, value_snapshot.evaluation_store),
                    store(
                        value_snapshot.operation_owner, value_snapshot.operation_store
                    ),
                    store(
                        value_snapshot.projection_owner, value_snapshot.projection_store
                    ),
                    store(
                        value_snapshot.projection_pattern_owner,
                        value_snapshot.projection_pattern_store,
                    ),
                )
            )
            records_valid = valid_root
            for local_id, runtime_record in value_snapshot.records.items():
                valid = valid_root and type(local_id) is int
                try:
                    valid &= root.resolve(root.value_id(local_id)) is runtime_record
                    valid &= valid_runtime_value_record(
                        root,
                        semantic_owner,
                        runtime_record,
                    )
                    valid &= value_snapshot.keys.get(runtime_record) == local_id
                except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(runtime_record))
                else:
                    invalid.add((value_snapshot.record_owner, id(runtime_record)))
                    records_valid = False
            environments_valid = valid_root
            for local_id, environment in value_snapshot.environments.items():
                valid = valid_root and type(environment) is RuntimeEnvironment
                try:
                    valid &= root.environment(local_id) is environment
                    valid &= (
                        value_snapshot.environment_keys.get(environment) == local_id
                    )
                    valid &= tuple(sorted(environment.bindings)) == environment.bindings
                    for binding, value in environment.bindings:
                        valid &= type(binding) is int
                        root.validate_atom(value)
                except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(environment))
                else:
                    invalid.add((value_snapshot.environment_owner, id(environment)))
                    environments_valid = False
            evaluations_valid = valid_root
            for evaluation_key, value in value_snapshot.evaluations.items():
                valid = (
                    type(evaluation_key) is tuple
                    and len(evaluation_key) == 2
                    and all(type(item) is int and item >= -1 for item in evaluation_key)
                )
                try:
                    if valid:
                        root.validate_atom(value)
                except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(evaluation_key))
                else:
                    invalid.add((value_snapshot.memo_owner, id(evaluation_key)))
                    evaluations_valid = False
            for operation_key, value in value_snapshot.operations.items():
                valid = valid_higher_operation(
                    root,
                    semantic_owner,
                    operation_key,
                    value,
                )
                if valid:
                    approved.add(id(operation_key))
                else:
                    invalid.add((value_snapshot.operation_owner, id(operation_key)))
                    evaluations_valid = False
            projections_valid = valid_root
            for projection_key, value in value_snapshot.projections.items():
                valid = (
                    type(projection_key) is tuple
                    and len(projection_key) == 2
                    and all(type(item) is int for item in projection_key)
                    and type(value) is int
                    and value >= -1
                )
                try:
                    if value >= 0:
                        root.environment(value)
                except (TypeError, ValueError, KeyError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(projection_key))
                else:
                    invalid.add((value_snapshot.projection_owner, id(projection_key)))
                    projections_valid = False
            patterns_valid = valid_root
            for bindings, pattern in value_snapshot.projection_patterns.items():
                valid = (
                    type(bindings) is tuple
                    and all(type(item) is int and item >= 0 for item in bindings)
                    and type(pattern) is int
                    and pattern >= 0
                )
                if valid:
                    approved.add(id(bindings))
                else:
                    invalid.add((value_snapshot.projection_pattern_owner, id(bindings)))
                    patterns_valid = False
            if (
                records_valid
                and environments_valid
                and evaluations_valid
                and projections_valid
                and patterns_valid
            ):
                approved.update(
                    (
                        id(value_snapshot.record_store),
                        id(value_snapshot.key_store),
                        id(value_snapshot.environment_store),
                        id(value_snapshot.environment_key_store),
                        id(value_snapshot.evaluation_store),
                        id(value_snapshot.operation_store),
                        id(value_snapshot.projection_store),
                        id(value_snapshot.projection_pattern_store),
                    )
                )
        elif type(root) is HigherBimachineRuntime:
            bimachine_snapshot = root.audit_snapshot()
            valid_root = (
                root.ledger is ledger
                and store(
                    bimachine_snapshot.operation_owner,
                    bimachine_snapshot.operation_store,
                )
                and store(
                    bimachine_snapshot.transfer_owner,
                    bimachine_snapshot.transfer_store,
                )
            )
            operations_valid = valid_root
            for op_record, result in bimachine_snapshot.operations.items():
                valid = type(op_record) in (
                    HigherInitialOperation,
                    HigherStepOperation,
                    HigherEmitOperation,
                )
                try:
                    audit_validate_action(root.schema, op_record.action)
                    if isinstance(
                        op_record, (HigherInitialOperation, HigherStepOperation)
                    ):
                        valid &= type(op_record.side) is int and op_record.side in (
                            0,
                            1,
                        )
                    if type(op_record) is HigherStepOperation:
                        root.semantics.expression(op_record.state)
                        root.semantics.expression(op_record.symbol)
                    elif type(op_record) is HigherEmitOperation:
                        root.semantics.expression(op_record.left)
                        root.semantics.expression(op_record.symbol)
                        root.semantics.expression(op_record.right)
                    root.semantics.expression(result)
                except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                    valid = False
                if valid:
                    approved.update((id(op_record), id(result)))
                else:
                    invalid.add((bimachine_snapshot.operation_owner, id(op_record)))
                    operations_valid = False
            transfers_valid = valid_root
            for transfer, transfer_result in bimachine_snapshot.transfers.items():
                valid = type(transfer) is HigherTransfer
                try:
                    audit_validate_action(root.schema, transfer.action)
                    root.sources.resolve(transfer.source)
                    valid &= type(transfer.side) is int and transfer.side in (0, 1)
                    root.semantics.function_record(transfer_result)
                except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                    valid = False
                if valid:
                    approved.update((id(transfer), id(transfer_result)))
                else:
                    invalid.add((bimachine_snapshot.transfer_owner, id(transfer)))
                    transfers_valid = False
            if operations_valid and transfers_valid:
                approved.update(
                    (
                        id(bimachine_snapshot.operation_store),
                        id(bimachine_snapshot.transfer_store),
                    )
                )
        elif type(root) is HigherSummaryArena:
            from number_compiler.resources.higher_summary_payload import (
                audit_higher_summary_arena,
            )

            summary_approved, summary_invalid = audit_higher_summary_arena(
                root,
                ledger,
                containers,
            )
            approved.update(summary_approved)
            invalid.update(summary_invalid)
        elif type(root) is SemanticBoundaryArena:
            boundary_snapshot = root.audit_snapshot()
            valid_root = valid_node_key_store(boundary_snapshot)
            records_valid = valid_root
            for index, boundary in enumerate(boundary_snapshot.records):
                valid = (
                    type(boundary) is SemanticBoundaryRecord
                    and type(boundary.left) is int
                    and boundary.left >= 0
                    and type(boundary.right) is int
                    and boundary.right >= 0
                    and boundary_snapshot.keys.get(boundary) == index
                )
                if valid:
                    approved.add(id(boundary))
                else:
                    invalid.add((boundary_snapshot.node_owner, id(boundary)))
                    records_valid = False
            if records_valid:
                approved.update(
                    (
                        id(boundary_snapshot.node_store),
                        id(boundary_snapshot.key_store),
                    )
                )
    return HigherPayloadAudit(frozenset(approved), frozenset(invalid))


__all__ = ["HigherPayloadAudit", "audit_higher_payloads"]
