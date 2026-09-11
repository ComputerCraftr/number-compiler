"""Independent validation of retained recursive higher semantic records."""

from __future__ import annotations

from dataclasses import dataclass
from typing import cast

from number_compiler.resources.higher_readonly import audit_schema_call
from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class HigherPayloadAudit:
    approved: frozenset[int]
    invalid: frozenset[tuple[int, int]]


def audit_higher_payloads(ledger: ResourceLedger) -> HigherPayloadAudit:
    """Validate issued higher DAG records through their owning arenas."""
    legacy_prefixes = (
        "number_compiler.hashlife.execution.continuations.",
        "number_compiler.hashlife.execution.recursive_outputs",
        "number_compiler.sequences.reverse_add.higher_interface",
    )
    if not any(
        type(root).__module__.startswith(legacy_prefixes)
        for root in ledger.iter_execution_roots()
    ):
        return HigherPayloadAudit(frozenset(), frozenset())

    from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
    from number_compiler.hashlife.actions.field_actions import (
        FieldCellActionID,
    )
    from number_compiler.hashlife.execution.continuations.higher_bimachine import (
        HigherBimachineRuntime,
        _Emit,
        _Initial,
        _Step,
        _Transfer,
    )
    from number_compiler.hashlife.execution.continuations.higher_interfaces import (
        HigherInterfaceRecord,
        HigherLocalInterfaceArena,
        HigherMacroComponents,
        HigherMacroInterface,
    )
    from number_compiler.hashlife.execution.continuations.higher_macro_composer import (
        HigherSpatialMacroComposer,
        SourceBoundHigherMacro,
        _MacroBindingKey,
    )
    from number_compiler.hashlife.execution.continuations.higher_semantic import (
        HigherSemanticArena,
    )
    from number_compiler.hashlife.execution.continuations.higher_summaries import (
        HigherSummaryArena,
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
        RuntimeValueID,
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
    from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
    from number_compiler.hashlife.interfaces.semantic_interfaces import (
        SemanticBoundaryArena,
        _Boundary,
    )
    from number_compiler.resources.higher_operation_payload import (
        valid_higher_operation,
    )
    from number_compiler.resources.higher_value_record_audit import (
        valid_runtime_value_record,
    )
    from number_compiler.sequences.collatz.range_runtime import (
        CollatzRadix4Range,
        CollatzRadix4RangeArena,
        CollatzRadix4RangeID,
    )
    from number_compiler.sequences.reverse_add.higher_interface import (
        ReverseHigherInterfaceCompilation,
        ReverseHigherInterfaceCompiler,
    )

    containers = dict(ledger.iter_containers())
    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()

    def store(owner: int, value: object) -> bool:
        return containers.get(owner) is value

    def identity_index(mapping: object, record: object, index: int) -> bool:
        """Use the canonical hash path, with a mutation-safe audit fallback."""
        try:
            found = mapping.get(record)  # type: ignore[attr-defined]
            return type(found) is int and found == index
        except (KeyError, TypeError, AttributeError):
            return any(
                key is record and type(value) is int and value == index
                for key, value in mapping.items()  # type: ignore[attr-defined]
            )

    for root in ledger.iter_execution_roots():
        if type(root) is HigherSemanticArena:
            valid_root = root.ledger is ledger and all(
                (
                    store(root._expression_owner, root._expressions),
                    store(root._expression_key_owner, root._expression_keys),
                    store(root._expression_free_owner, root._expression_free_ids),
                    store(root._function_owner, root._functions),
                    store(root._function_key_owner, root._function_keys),
                    store(root._rewrite_owner, root._rewrites),
                )
            )
            expressions_valid = valid_root
            for index, expression_record in enumerate(root._expressions):
                valid = valid_root and type(expression_record) is HigherExpression
                free: tuple[int, ...] = ()
                try:
                    valid &= (
                        root.expression(root._expression_handle(index))
                        is expression_record
                    )
                    root._validate_sort(expression_record.sort, readonly=True)
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
                        audit_schema_call(
                            root.schema, "validate_action", expression_record.action
                        )
                    if expression_record.function is not None:
                        root.function_record(expression_record.function)
                    valid &= identity_index(
                        root._expression_keys,
                        expression_record,
                        index,
                    )
                    free = root._expression_free_ids[index]
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
                    invalid.add((root._expression_owner, id(expression_record)))
                    expressions_valid = False
            functions_valid = valid_root
            for index, function_record in enumerate(root._functions):
                valid = valid_root and type(function_record) is HigherFunction
                try:
                    valid &= (
                        root.function_record(root._function_handle(index))
                        is function_record
                    )
                    root._validate_sort(function_record.signature, readonly=True)
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
                    valid &= identity_index(
                        root._function_keys,
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
                    invalid.add((root._function_owner, id(function_record)))
                    functions_valid = False
            rewrites_valid = valid_root
            for rewrite, result in root._rewrites.items():
                valid = all(
                    type(item) is int
                    for item in (rewrite.root, rewrite.variable, rewrite.replacement)
                )
                try:
                    valid &= (
                        min(rewrite.root, rewrite.variable, rewrite.replacement) >= 0
                    )
                    root.expression(root._expression_handle(rewrite.root))
                    root.expression(root._expression_handle(rewrite.variable))
                    root.expression(root._expression_handle(rewrite.replacement))
                    root.expression(result)
                except (TypeError, ValueError, IndexError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(rewrite))
                else:
                    invalid.add((root._rewrite_owner, id(rewrite)))
                    rewrites_valid = False
            if expressions_valid and functions_valid and rewrites_valid:
                approved.update(
                    (
                        id(root._expressions),
                        id(root._expression_keys),
                        id(root._expression_free_ids),
                        id(root._functions),
                        id(root._function_keys),
                        id(root._rewrites),
                    )
                )
        elif type(root) is HigherLocalInterfaceArena:
            valid_root = root.ledger is ledger and all(
                (
                    store(root._higher_signature_owner, root._higher_signatures),
                    store(
                        root._higher_signature_key_owner, root._higher_signature_keys
                    ),
                    store(root._higher_node_owner, root._higher_nodes),
                    store(root._higher_key_owner, root._higher_keys),
                )
            )
            signatures_valid = valid_root
            for index, interface_record in enumerate(root._higher_signatures):
                valid = valid_root and type(interface_record) is HigherMacroInterface
                found_signature = None
                try:
                    root._validate_interface(interface_record, readonly=True)
                    valid &= (
                        root.interface(
                            PortSignatureID(
                                root.owner,
                                root._SIGNATURE_KIND,
                                index,
                            )
                        )
                        is interface_record
                    )
                    found_signature = root._higher_signature_keys.get(interface_record)
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
                    invalid.add((root._higher_signature_owner, id(interface_record)))
                    signatures_valid = False
            interfaces_valid = valid_root
            for index, node_record in enumerate(root._higher_nodes):
                valid = valid_root and type(node_record) is HigherInterfaceRecord
                found_interface = None
                try:
                    valid &= type(node_record.components) is HigherMacroComponents
                    root._validate_components(
                        node_record.signature, node_record.components
                    )
                    valid &= (
                        root.resolve(
                            LocalInterfaceID(
                                root.owner,
                                root._INTERFACE_KIND,
                                index,
                            )
                        )
                        is node_record
                    )
                    found_interface = root._higher_keys.get(node_record)
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
                    invalid.add((root._higher_node_owner, id(node_record)))
                    interfaces_valid = False
            if signatures_valid and interfaces_valid:
                approved.update(
                    (
                        id(root._higher_signatures),
                        id(root._higher_signature_keys),
                        id(root._higher_nodes),
                        id(root._higher_keys),
                    )
                )
        elif type(root) is RecursiveCoordinateMorphismArena:
            valid_root = (
                root.ledger is ledger
                and store(root._node_owner, root._nodes)
                and store(root._key_owner, root._keys)
            )
            records_valid = valid_root
            for local_id, record in root._nodes.items():
                valid = type(local_id) is int and type(record) in (
                    RecursiveOutputSource,
                    RecursiveOutputBindingSource,
                    RecursiveOutputLeaf,
                    RecursiveOutputBranch,
                    RecursiveOutputTemporal,
                )
                try:
                    valid &= root.resolve(root._handle(local_id)) is record
                    valid &= root._keys.get(record) == local_id
                    if type(record) is RecursiveOutputSource:
                        if root._validate_source is None or root._read_source is None:
                            valid = False
                        else:
                            root._validate_source(record.source)
                    elif type(record) is RecursiveOutputBindingSource:
                        if type(record.source) is SourceCellID:
                            if root._validate_source is None:
                                valid = False
                            else:
                                root._validate_source(record.source)
                        elif type(record.source) is SourceForestID:
                            pass
                        else:
                            valid = False
                    elif type(record) is RecursiveOutputLeaf:
                        root.interfaces.resolve(record.scalar_interface)
                    elif type(record) is RecursiveOutputBranch:
                        branch = record
                        root.resolve(branch.left)
                        root.resolve(branch.right)
                        root.interfaces.resolve(branch.left_interface)
                        root.interfaces.resolve(branch.right_interface)
                        valid &= (
                            type(branch.left_width) is int and branch.left_width > 0
                        )
                    else:
                        temporal = cast(RecursiveOutputTemporal, record)
                        root.resolve(temporal.provider)
                        if root._validate_action is None:
                            valid = False
                        else:
                            root._validate_action(temporal.action)
                        root._validate_temporal_interface(temporal.interface)
                except (TypeError, ValueError, KeyError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(record))
                    approved.update(
                        id(getattr(record, name))
                        for name in record.__dataclass_fields__
                    )
                else:
                    invalid.add((root._node_owner, id(record)))
                    records_valid = False
            if records_valid:
                approved.update((id(root._nodes), id(root._keys)))
        elif type(root) is CollatzRadix4RangeArena:
            valid_root = (
                root.ledger is ledger
                and store(root._node_owner, root._nodes)
                and store(root._key_owner, root._keys)
                and store(root._binding_owner, root._bindings)
            )
            records_valid = valid_root
            for range_index, range_record in enumerate(root._nodes):
                valid = type(range_record) is CollatzRadix4Range
                try:
                    range_record.__post_init__()
                    valid &= root._keys.get(range_record) == range_index
                    root.resolve(
                        CollatzRadix4RangeID(
                            root.owner,
                            root._KIND,
                            range_index,
                        )
                    )
                except (TypeError, ValueError, KeyError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(range_record))
                else:
                    invalid.add((root._node_owner, id(range_record)))
                    records_valid = False
            bindings_valid = valid_root
            for range_source, range_action in root._bindings.items():
                try:
                    root.sources.resolve(range_source)
                    root.resolve(range_action)
                except (TypeError, ValueError, KeyError, AttributeError):
                    bindings_valid = False
                    invalid.add((root._binding_owner, id(range_source)))
            if records_valid and bindings_valid:
                approved.update((id(root._nodes), id(root._keys), id(root._bindings)))
        elif type(root) is HigherTemporalProviderEvaluator:
            valid_root = root.ledger is ledger and store(
                root._binding_owner, root._bindings
            )
            bindings_valid = valid_root
            for output, provider_binding in root._bindings.items():
                valid = type(provider_binding) is tuple and len(provider_binding) == 2
                try:
                    root._validate_output(output)
                    source, provider_action = provider_binding
                    audit_schema_call(
                        root.runtime.schema, "validate_action", provider_action
                    )
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
                    invalid.add((root._binding_owner, id(provider_binding)))
                    bindings_valid = False
            if bindings_valid:
                approved.add(id(root._bindings))
        elif type(root) is HigherSpatialMacroComposer:
            valid_root = root.ledger is ledger and store(
                root._binding_owner, root._bindings
            )
            bindings_valid = valid_root
            for key, macro in root._bindings.items():
                valid = (
                    type(key) is _MacroBindingKey
                    and type(macro) is SourceBoundHigherMacro
                )
                try:
                    audit_schema_call(
                        root.semantics.schema, "validate_action", key.action
                    )
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
                    invalid.add((root._binding_owner, id(key)))
                    bindings_valid = False
            if bindings_valid:
                approved.add(id(root._bindings))
        elif type(root) is RuntimeValueArena:
            semantic_owner = next(
                (
                    candidate
                    for candidate in ledger.iter_execution_roots()
                    if type(candidate) is HigherSemanticArena
                    and candidate.runtime_values is root
                ),
                None,
            )
            valid_root = root.ledger is ledger and all(
                (
                    store(root._record_owner, root._records),
                    store(root._key_owner, root._keys),
                    store(root._environment_owner, root._environments),
                    store(root._environment_key_owner, root._environment_keys),
                    store(root._memo_owner, root.evaluations),
                    store(root._operation_owner, root.operations),
                    store(root._projection_owner, root._projections),
                    store(root._projection_pattern_owner, root._projection_patterns),
                )
            )
            records_valid = valid_root
            for local_id, runtime_record in root._records.items():
                valid = valid_root and type(local_id) is int
                try:
                    valid &= (
                        root.resolve(RuntimeValueID(root.owner, root._KIND, local_id))
                        is runtime_record
                    )
                    valid &= valid_runtime_value_record(
                        root,
                        semantic_owner,
                        runtime_record,
                    )
                    valid &= root._keys.get(runtime_record) == local_id
                except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(runtime_record))
                else:
                    invalid.add((root._record_owner, id(runtime_record)))
                    records_valid = False
            environments_valid = valid_root
            for local_id, environment in root._environments.items():
                valid = valid_root and type(environment) is RuntimeEnvironment
                try:
                    valid &= root.environment(local_id) is environment
                    valid &= root._environment_keys.get(environment) == local_id
                    valid &= tuple(sorted(environment.bindings)) == environment.bindings
                    for binding, value in environment.bindings:
                        valid &= type(binding) is int
                        root.validate_atom(value)
                except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(environment))
                else:
                    invalid.add((root._environment_owner, id(environment)))
                    environments_valid = False
            evaluations_valid = valid_root
            for evaluation_key, value in root.evaluations.items():
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
                    invalid.add((root._memo_owner, id(evaluation_key)))
                    evaluations_valid = False
            for operation_key, value in root.operations.items():
                valid = valid_higher_operation(
                    root,
                    semantic_owner,
                    operation_key,
                    value,
                )
                if valid:
                    approved.add(id(operation_key))
                else:
                    invalid.add((root._operation_owner, id(operation_key)))
                    evaluations_valid = False
            projections_valid = valid_root
            for projection_key, value in root._projections.items():
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
                    invalid.add((root._projection_owner, id(projection_key)))
                    projections_valid = False
            patterns_valid = valid_root
            for bindings, pattern in root._projection_patterns.items():
                valid = (
                    type(bindings) is tuple
                    and all(type(item) is int and item >= 0 for item in bindings)
                    and type(pattern) is int
                    and pattern >= 0
                )
                if valid:
                    approved.add(id(bindings))
                else:
                    invalid.add((root._projection_pattern_owner, id(bindings)))
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
                        id(root._records),
                        id(root._keys),
                        id(root._environments),
                        id(root._environment_keys),
                        id(root.evaluations),
                        id(root.operations),
                        id(root._projections),
                        id(root._projection_patterns),
                    )
                )
        elif type(root) is HigherBimachineRuntime:
            valid_root = (
                root.ledger is ledger
                and store(root._operation_owner, root._operations)
                and store(root._transfer_owner, root._transfers)
            )
            operations_valid = valid_root
            for op_record, result in root._operations.items():
                valid = type(op_record) in (_Initial, _Step, _Emit)
                try:
                    audit_schema_call(root.schema, "validate_action", op_record.action)
                    if isinstance(op_record, (_Initial, _Step)):
                        valid &= type(op_record.side) is int and op_record.side in (
                            0,
                            1,
                        )
                    if type(op_record) is _Step:
                        root.semantics.expression(op_record.state)
                        root.semantics.expression(op_record.symbol)
                    elif type(op_record) is _Emit:
                        root.semantics.expression(op_record.left)
                        root.semantics.expression(op_record.symbol)
                        root.semantics.expression(op_record.right)
                    root.semantics.expression(result)
                except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                    valid = False
                if valid:
                    approved.update((id(op_record), id(result)))
                else:
                    invalid.add((root._operation_owner, id(op_record)))
                    operations_valid = False
            transfers_valid = valid_root
            for transfer, transfer_result in root._transfers.items():
                valid = type(transfer) is _Transfer
                try:
                    audit_schema_call(root.schema, "validate_action", transfer.action)
                    root.sources.resolve(transfer.source)
                    valid &= type(transfer.side) is int and transfer.side in (0, 1)
                    root.semantics.function_record(transfer_result)
                except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                    valid = False
                if valid:
                    approved.update((id(transfer), id(transfer_result)))
                else:
                    invalid.add((root._transfer_owner, id(transfer)))
                    transfers_valid = False
            if operations_valid and transfers_valid:
                approved.update((id(root._operations), id(root._transfers)))
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
        elif type(root) is ReverseHigherInterfaceCompiler:
            valid_root = root.ledger is ledger and store(root._cache_owner, root._cache)
            cache_valid = valid_root
            for action, compilation in root._cache.items():
                valid = (
                    type(action) is FieldCellActionID
                    and type(compilation) is ReverseHigherInterfaceCompilation
                    and compilation.action == action
                )
                try:
                    root.actions.validate_action(action)
                    root.actions.validate_action(compilation.action)
                    root.interfaces.interface(compilation.signature)
                    resolved_compilation = root.interfaces.resolve(
                        compilation.interface
                    )
                    valid &= resolved_compilation.signature == compilation.signature
                    root.actions._output_key(compilation.output_morphism)
                    root.semantics.expression(compilation.left)
                    root.semantics.expression(compilation.symbol)
                    root.semantics.expression(compilation.right)
                except (TypeError, ValueError, IndexError, KeyError, AttributeError):
                    valid = False
                if valid:
                    approved.add(id(compilation))
                    approved.update(
                        id(getattr(compilation, field))
                        for field in (
                            "action",
                            "signature",
                            "interface",
                            "output_morphism",
                            "left",
                            "symbol",
                            "right",
                        )
                    )
                else:
                    invalid.add((root._cache_owner, id(compilation)))
                    cache_valid = False
            if cache_valid:
                approved.add(id(root._cache))
        elif type(root) is SemanticBoundaryArena:
            valid_root = store(root._node_owner, root._nodes) and store(
                root._key_owner, root._keys
            )
            records_valid = valid_root
            for index, boundary in enumerate(root._nodes):
                valid = (
                    type(boundary) is _Boundary
                    and type(boundary.left) is int
                    and boundary.left >= 0
                    and type(boundary.right) is int
                    and boundary.right >= 0
                    and root._keys.get(boundary) == index
                )
                if valid:
                    approved.add(id(boundary))
                else:
                    invalid.add((root._node_owner, id(boundary)))
                    records_valid = False
            if records_valid:
                approved.update((id(root._nodes), id(root._keys)))
    return HigherPayloadAudit(frozenset(approved), frozenset(invalid))


__all__ = ["HigherPayloadAudit", "audit_higher_payloads"]
