"""Independent immutable-expression domain certificates, without execution."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.functions.finite_function_types import (
    FinitePort,
    SemanticFunctionID,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
    ExprID,
    FunctionSort,
    StateSort,
)
from number_compiler.hashlife.interfaces.semantic_expression_compiler import (
    ExpressionAdmissionKey,
    ExpressionDomainProof,
    SemanticExpressionCompiler,
    _FiniteLiftKey,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict

if TYPE_CHECKING:
    from number_compiler.resources.semantic_payload import SemanticPayloadRegistry
    from number_compiler.resources.semantic_profile_payload import (
        SemanticProfilePayloadRegistry,
    )


class SemanticAdmissionPayloadRegistry:
    record_types = (ExpressionAdmissionKey, ExpressionDomainProof, _FiniteLiftKey)

    def __init__(
        self,
        ledger: ResourceLedger,
        semantic: SemanticPayloadRegistry,
        profiles: SemanticProfilePayloadRegistry,
    ) -> None:
        self.valid_objects: set[int] = set()
        self.invalid_bindings: set[tuple[int, int]] = set()
        actual = dict(ledger.iter_containers())
        compilers = tuple(
            root
            for root in ledger.iter_execution_roots()
            if type(root) is SemanticExpressionCompiler
            and root.ledger is ledger
            and root.functions in semantic.functions
            and root.runtime.ledger is ledger
            and root.expressions is root.runtime.higher.expressions
        )
        if not compilers:
            return
        check = semantic.expression_valid
        if check is None:
            from number_compiler.hashlife.execution.diamond_payload import (
                DiamondPayloadRegistry,
            )

            check = DiamondPayloadRegistry(ledger).valid
        for compiler in compilers:
            store, owner = compiler.admissions._data, compiler.admissions.owner
            if (
                actual.get(owner) is not store
                or type(store) is not LedgerDict
                or not ledger.is_factory_container(store)
            ):
                self.invalid_bindings.add((owner, id(store)))
                continue
            for key, proof in store._data.items():
                try:
                    admitted = (
                        type(key) is ExpressionAdmissionKey
                        and type(key.structured) is bool
                        and type(key.expression) is ExprID
                        and key.expression.owner is compiler.expressions.token
                        and type(proof) is ExpressionDomainProof
                        and type(proof.key) is ExpressionAdmissionKey
                        and type(proof.key.expression) is ExprID
                        and type(proof.key.structured) is bool
                        and check(key.expression)
                        and check(proof.key.expression)
                        and proof.key == key
                        and (
                            proof.key.profile is None
                            or profiles.handle(proof.key.profile)
                        )
                        and (
                            key.profile is None
                            or key.structured
                            and profiles.handle(key.profile)
                            and compiler.profiles in profiles.arenas
                            and key.profile.owner is compiler.profiles.token
                        )
                        and _domains(compiler, key)
                    )
                except (ValueError, TypeError, AttributeError, IndexError, KeyError):
                    admitted = False
                if admitted:
                    self.valid_objects.update((id(key), id(proof), id(proof.key)))
                else:
                    self.invalid_bindings.update(((owner, id(key)), (owner, id(proof))))
            finite_store = compiler._finite_lifts._data
            finite_owner = compiler._finite_lifts.owner
            if (
                actual.get(finite_owner) is not finite_store
                or type(finite_store) is not LedgerDict
                or not ledger.is_factory_container(finite_store)
            ):
                self.invalid_bindings.add((finite_owner, id(finite_store)))
                continue
            for key, value in finite_store._data.items():
                accepted = False
                function: object = None
                port: object = None
                try:
                    if (
                        type(key) is not _FiniteLiftKey
                        or type(value) is not tuple
                        or len(value) != 2
                    ):
                        raise TypeError("finite lift has another record shape")
                    function, port = value
                    compiler.runtime.kernels.expression(key.function)
                    domain = compiler._atom_sort(key.source).cardinality
                    expected_port = FinitePort(
                        PortVariable(
                            0,
                            0,
                            "semantic-finite-map-input",
                            0,
                        ),
                        domain,
                    )
                    expected = compiler._atom_sort(key.target)
                    accepted = (
                        type(function) is SemanticFunctionID
                        and semantic.handle(function)
                        and type(port) is FinitePort
                        and port == expected_port
                        and compiler.functions.signature(function).inputs == (port,)
                        and compiler.functions.signature(function).output == expected
                    )
                except (ValueError, TypeError, AttributeError, IndexError, KeyError):
                    accepted = False
                if accepted:
                    self.valid_objects.update(
                        (id(key), id(value), id(function), id(port))
                    )
                else:
                    self.invalid_bindings.update(
                        ((finite_owner, id(key)), (finite_owner, id(value)))
                    )


def _domains(compiler: SemanticExpressionCompiler, key: ExpressionAdmissionKey) -> bool:
    expressions = compiler.expressions
    pending = [key.expression.local_id]
    seen: set[int] = set()
    while pending:
        identity = pending.pop()
        if identity in seen:
            continue
        seen.add(identity)
        node = expressions.nodes[identity]
        if node.kind == "lambda":
            if (
                type(node.sort) is not FunctionSort
                or type(node.sort.domain) is not StateSort
            ):
                return False
            domain = node.sort.domain
            action = compiler.runtime.actions.resolve(domain.action)
            if action.kind == "atom":
                if expressions.primitive(domain.action) is None:
                    return False
            elif action.kind == "compose" and key.structured:
                if key.profile is not None:
                    if compiler.profiles is None:
                        return False
                    profile = compiler.profiles.nodes[key.profile.local_id]
                    if domain.action != profile.action or domain.side != profile.side:
                        return False
                for child in (action.first, action.second):
                    reference = compiler.runtime.actions.reference(child)
                    if (
                        compiler.runtime.actions.resolve(reference).kind != "atom"
                        or expressions.primitive(reference) is None
                    ):
                        return False
            else:
                return False
        pending.extend(node.children)
        if node.closure is not None:
            pending.append(expressions.closures.resolve(node.closure).body.local_id)
    return True
