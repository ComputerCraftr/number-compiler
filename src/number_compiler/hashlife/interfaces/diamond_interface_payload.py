"""Independent finite-domain proof checking for universal admission memos."""

from __future__ import annotations

from number_compiler.hashlife.execution.continuations.diamond_expression_payload import (
    ExpressionPayloadRegistry,
)
from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
    StateSort,
    SymbolSort,
)
from number_compiler.hashlife.interfaces.diamond_finite_admission import (
    FiniteFunctionAdmission,
    FiniteInterfaceCertificate,
    FiniteInterfaceKey,
)
from number_compiler.resources.ledger import ResourceLedger


class InterfacePayloadRegistry:
    record_types = (FiniteInterfaceKey, FiniteInterfaceCertificate)

    def __init__(
        self, ledger: ResourceLedger, expressions: ExpressionPayloadRegistry
    ) -> None:
        self.expressions = expressions
        actual = dict(ledger.iter_containers())
        self.helpers = tuple(
            root
            for root in ledger.iter_execution_roots()
            if type(root) is FiniteFunctionAdmission
            and root.ledger is ledger
            and root.arena in expressions.arenas
            and root.kernels is root.arena.boundaries.kernels
            and actual.get(root.owner) is root.memo.audit_container
        )
        self.valid_records: set[int] = set()
        self.invalid_response_objects: set[tuple[int, int]] = set()
        for helper in self.helpers:
            for key, result in helper.memo.items():
                if self._entry(helper, key, result):
                    self.valid_records.update((id(key), id(result)))
                else:
                    self.invalid_response_objects.update(
                        ((helper.owner, id(key)), (helper.owner, id(result)))
                    )

    def _entry(
        self, helper: FiniteFunctionAdmission, key: object, result: object
    ) -> bool:
        if (
            type(key) is not FiniteInterfaceKey
            or type(result) is not FiniteInterfaceCertificate
            or type(key.source) is not StateSort
            or type(key.target) not in (StateSort, SymbolSort)
            or type(result.input_size) is not int
            or type(result.output_size) is not int
            or not self.expressions.finite_function(
                helper.arena, key.target, key.function, source=key.source
            )
        ):
            return False
        primitive = helper.arena.primitive(key.source.action)
        assert primitive is not None
        input_size = (
            primitive.left_count if key.source.side == 0 else primitive.right_count
        )
        if type(key.target) is StateSort:
            target = helper.arena.primitive(key.target.action)
            assert target is not None
            output_size = (
                target.left_count if key.target.side == 0 else target.right_count
            )
        else:
            assert isinstance(key.target, SymbolSort)
            output_size = key.target.blank + 1
        return (result.input_size, result.output_size) == (input_size, output_size)

    def valid(self, value: object) -> bool:
        return type(value) in self.record_types and id(value) in self.valid_records
