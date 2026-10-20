"""Family-owned audit for retained reverse higher-interface compilations."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_contracts import (
    PayloadAuditContribution,
    PayloadAuditEntry,
)

if TYPE_CHECKING:
    from number_compiler.sequences.reverse_add.higher_interface import (
        ReverseHigherInterfaceCompiler,
    )


def register_reverse_higher_interface_contract(
    root: ReverseHigherInterfaceCompiler,
) -> None:
    from number_compiler.resources.payload_contracts import PayloadAuditStoreBinding

    state = root.audit_snapshot()
    root.ledger.register_payload_audit_contract(
        root,
        "reverse_add",
        (PayloadAuditStoreBinding(state.cache_owner, "_cache", "query_memo"),),
        audit_reverse_higher_interface_owner,
    )


def audit_reverse_higher_interface_owner(
    ledger_value: object, root_value: object
) -> PayloadAuditContribution:
    from number_compiler.hashlife.actions.field_actions import (
        CoordinateOutputMorphismID,
        FieldCellActionID,
    )
    from number_compiler.hashlife.execution.continuations.higher_bimachine import (
        HigherBimachineRuntime,
    )
    from number_compiler.hashlife.execution.continuations.higher_interfaces import (
        HigherInterfaceRecord,
        HigherLocalInterfaceArena,
        HigherMacroInterface,
        HigherPort,
    )
    from number_compiler.hashlife.execution.continuations.higher_semantic import (
        HigherSemanticArena,
    )
    from number_compiler.hashlife.execution.continuations.higher_types import (
        HigherExpressionID,
    )
    from number_compiler.sequences.reverse_add.field_action import (
        ReverseFieldActionArena,
    )
    from number_compiler.sequences.reverse_add.higher_interface import (
        ReverseHigherInterfaceCompilation,
        ReverseHigherInterfaceCompiler,
    )
    from number_compiler.sequences.reverse_add.higher_schema import (
        ReverseHigherActionSchema,
    )

    if type(ledger_value) is not ResourceLedger:
        raise TypeError("higher interface auditor received a foreign ledger")
    if type(root_value) is not ReverseHigherInterfaceCompiler:
        raise TypeError("higher interface auditor received a foreign root")
    ledger = ledger_value
    root = root_value
    state = root.audit_snapshot()
    cache_account = ledger.inventory_owner(state.cache_owner)
    valid_root = (
        root.ledger is ledger
        and type(root.actions) is ReverseFieldActionArena
        and type(root.schema) is ReverseHigherActionSchema
        and type(root.semantics) is HigherSemanticArena
        and type(root.runtime) is HigherBimachineRuntime
        and type(root.interfaces) is HigherLocalInterfaceArena
        and root.actions.ledger is ledger
        and root.schema.actions is root.actions
        and root.semantics.schema is root.schema
        and root.runtime.semantics is root.semantics
        and root.interfaces.semantics is root.semantics
        and ledger.registered_container(state.cache_owner) is state.cache
        and cache_account.role == "query_memo"
        and cache_account.entries == len(state.cache)
        and cache_account.nodes == 0
        and cache_account.payloads_registered
        and not cache_account.disposed
    )
    if not valid_root:
        raise ValueError("reverse higher interface owner is invalid")

    approved: list[PayloadAuditEntry] = []
    invalid: list[PayloadAuditEntry] = []
    for action, compilation in state.cache.items():
        valid = (
            type(action) is FieldCellActionID
            and type(compilation) is ReverseHigherInterfaceCompilation
            and compilation.action == action
        )
        try:
            root.actions.validate_action(action)
            action_record = root.actions.resolve(action)
            valid &= compilation.output_morphism == action_record.output
            valid &= type(compilation.output_morphism) is CoordinateOutputMorphismID
            signature = root.interfaces.interface(compilation.signature)
            interface_record = root.interfaces.resolve(compilation.interface)
            valid &= type(signature) is HigherMacroInterface
            valid &= type(interface_record) is HigherInterfaceRecord
            valid &= interface_record.signature == compilation.signature
            valid &= signature.kernel == root.actions.semantic_identity(
                action, audit=True
            )
            valid &= signature.phase_count == action_record.geometry.phase_count
            valid &= (
                root.interfaces.validate_components(
                    compilation.signature, interface_record.components
                )
                is signature
            )
            valid &= interface_record.components.normalization == (
                interface_record.components.output
            )
            expected_ports = (
                (compilation.left, "left-boundary"),
                (compilation.symbol, "source-symbol"),
                (compilation.right, "right-boundary"),
            )
            valid &= type(signature.inputs) is tuple and len(signature.inputs) == 3
            valid &= all(
                type(port) is HigherPort
                and type(variable) is HigherExpressionID
                and port.variable == variable
                and port.role == role
                for port, (variable, role) in zip(
                    signature.inputs, expected_ports, strict=True
                )
            )
            expected_sorts = (
                root.semantics.state_sort(action, 0),
                root.semantics.symbol_sort(action),
                root.semantics.state_sort(action, 1),
            )
            for (variable, role), expected_sort in zip(
                expected_ports, expected_sorts, strict=True
            ):
                expression = root.semantics.expression(variable)
                valid &= (
                    expression.kind == "variable"
                    and expression.role == role
                    and expression.sort == expected_sort
                    and not expression.children
                )
        except (TypeError, ValueError, IndexError, KeyError, AttributeError):
            valid = False
        target = approved if valid else invalid
        target.extend(
            (
                PayloadAuditEntry(state.cache_owner, action),
                PayloadAuditEntry(state.cache_owner, compilation),
            )
        )
    return PayloadAuditContribution(tuple(approved), tuple(invalid))


__all__ = [
    "audit_reverse_higher_interface_owner",
    "register_reverse_higher_interface_contract",
]
