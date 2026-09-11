"""Independent finite-port and response checks for continuation reduction."""

from __future__ import annotations

from number_compiler.hashlife.execution.continuations.diamond_expression_payload import (
    ExpressionPayloadRegistry,
)
from number_compiler.hashlife.execution.diamond_continuation_reduction import (
    CompilePrimitiveFunction,
    NormalizePrimitiveLambda,
    PrimitiveContinuationReducer,
)
from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
    ExprID,
    FormalPort,
    FunctionSort,
    StateSort,
)
from number_compiler.resources.ledger import ResourceLedger


class ContinuationPayloadRegistry:
    record_types = (CompilePrimitiveFunction, NormalizePrimitiveLambda)

    def __init__(
        self, ledger: ResourceLedger, expressions: ExpressionPayloadRegistry
    ) -> None:
        self.expressions = expressions
        actual = dict(ledger.iter_containers())
        self.reducers = tuple(
            root
            for root in ledger.iter_execution_roots()
            if type(root) is PrimitiveContinuationReducer
            and root.ledger is ledger
            and root.expressions in expressions.arenas
            and actual.get(root.maps.owner) is root.maps._data
            and actual.get(root.normalized.owner) is root.normalized._data
        )
        self.valid_records: set[int] = set()
        self.invalid_response_objects: set[tuple[int, int]] = set()
        for reducer in self.reducers:
            for key, value in reducer.maps.items():
                if self._map(reducer, key, value):
                    self.valid_records.add(id(key))
                else:
                    self.invalid_response_objects.update(
                        ((reducer.maps.owner, id(key)), (reducer.maps.owner, id(value)))
                    )
            for request, response in reducer.normalized.items():
                if self._normalized(reducer, request, response):
                    self.valid_records.add(id(request))
                else:
                    self.invalid_response_objects.update(
                        (
                            (reducer.normalized.owner, id(request)),
                            (reducer.normalized.owner, id(response)),
                        )
                    )

    def _map(
        self, reducer: PrimitiveContinuationReducer, key: object, result: object
    ) -> bool:
        if (
            type(key) is not CompilePrimitiveFunction
            or type(key.variable) is not ExprID
            or type(key.expression) is not ExprID
            or key.variable.owner is not reducer.expressions.token
            or key.expression.owner is not reducer.expressions.token
        ):
            return False
        variable, expression = (
            self.expressions.expression(key.variable),
            self.expressions.expression(key.expression),
        )
        if (
            variable is None
            or expression is None
            or variable.kind != "port"
            or type(variable.sort) is not StateSort
            or type(expression.sort) is not StateSort
            or expression.free_ports != (FormalPort(variable.sort, variable.role),)
            or not self.expressions.universal_program(key.expression)
        ):
            return False
        return self.expressions._finite_function(
            reducer.expressions, expression.sort, result, source=variable.sort
        )

    def _normalized(
        self, reducer: PrimitiveContinuationReducer, key: object, result: object
    ) -> bool:
        if (
            type(key) is not NormalizePrimitiveLambda
            or type(key.function) is not ExprID
            or key.function.owner is not reducer.expressions.token
            or type(result) is not ExprID
            or key.function == result
        ):
            return False
        first, second = (
            self.expressions.expression(key.function),
            self.expressions.expression(result),
        )
        return (
            first is not None
            and second is not None
            and first.kind == "lambda"
            and type(first.sort) is FunctionSort
            and first.sort == second.sort
            and not first.free_ports
            and not second.free_ports
            and reducer.expressions.primitive(first.sort.domain.action) is not None
            and self.expressions.universal_program(key.function)
            and self.expressions.universal_program(result)
            and self.expressions.response_allowed(
                reducer.expressions, result, (key.function,)
            )
        )

    def valid(self, value: object) -> bool:
        return type(value) in self.record_types and id(value) in self.valid_records
