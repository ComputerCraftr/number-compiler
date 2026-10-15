"""Extensional one-primitive-port reduction of higher continuation expressions.

This is the fixed-domain partition/preimage reduction, using existing finite
function IDs instead of integer masks. Composed input universes are never
enumerated. Closed provider outputs are transient dependencies, never memo keys
for scalar or constant-function responses.
"""

from __future__ import annotations

from collections.abc import Generator
from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
    BoundarySide,
    _effect_key,
)
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    TransferSummaryID,
)
from number_compiler.hashlife.execution.continuations.diamond_context_program import (
    LEFT_A,
    RIGHT_A,
)
from number_compiler.hashlife.execution.continuations.diamond_expression_eval import (
    ResolveExpr,
)
from number_compiler.hashlife.execution.diamond_continuation_guard import (
    function_program_admission,
)
from number_compiler.hashlife.execution.diamond_observation_guard import (
    retain_expression_response,
)
from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
    ExprID,
    FormalPort,
    FunctionSort,
    StateSort,
    SymbolSort,
)
from number_compiler.hashlife.interfaces.diamond_finite_admission import (
    FiniteFunctionAdmission,
)
from number_compiler.hashlife.interfaces.diamond_kernel_bridge import (
    input_expression,
    substitution_bindings,
)
from number_compiler.resources.ledger import OwnedMemo
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )
    from number_compiler.hashlife.execution.continuations.diamond_tasks import (
        Result,
        Task,
    )


@dataclass(frozen=True, slots=True)
class CompilePrimitiveFunction:
    variable: ExprID
    expression: ExprID


@dataclass(frozen=True, slots=True)
class NormalizePrimitiveLambda:
    function: ExprID


PRIMITIVE_CONTINUATION_TASKS = (CompilePrimitiveFunction, NormalizePrimitiveLambda)
ContinuationTask = CompilePrimitiveFunction | NormalizePrimitiveLambda


def _expression(value: Result) -> ExprID:
    if type(value) is not ExprID:
        raise AssertionError("expected a symbolic boundary expression")
    return value


def _function(value: Result) -> TransferSummaryID:
    if type(value) is not TransferSummaryID:
        raise AssertionError("expected a complete finite function")
    return value


class PrimitiveContinuationReducer:
    def __init__(self, runtime: DiamondRuntime) -> None:
        self.runtime = runtime
        self.expressions = runtime.higher.expressions
        self.kernels = runtime.kernels
        self.ledger = runtime.ledger
        self.ledger.register_execution_root(self)
        self.admission = FiniteFunctionAdmission(self.expressions)
        prefix = f"diamond-primitive-continuations-{len(self.ledger.inventory())}"
        self.maps: OwnedMemo[CompilePrimitiveFunction, TransferSummaryID] = OwnedMemo(
            self.ledger,
            self.ledger.register(prefix + "-maps", "query_memo"),
            evictable=True,
        )
        self.normalized: OwnedMemo[NormalizePrimitiveLambda, ExprID] = OwnedMemo(
            self.ledger,
            self.ledger.register(prefix + "-lambdas", "query_memo"),
            evictable=True,
        )
        self.binding_admission: OwnedMemo[ExprID, bool] = OwnedMemo(
            self.ledger,
            self.ledger.register(prefix + "-binding-admission", "query_memo"),
            evictable=True,
        )

    def _input(self, variable: ExprID) -> tuple[StateSort, ActionProgramID]:
        node = self.expressions.node(variable)
        if node.kind != "port" or type(node.sort) is not StateSort:
            raise ValueError("finite continuation requires a declared state port")
        primitive = self.expressions.primitive(node.sort.action)
        if primitive is None:
            raise ValueError(
                "finite continuation requires an already admitted primitive domain"
            )
        handle = self.kernels._kernel_ids[_effect_key(primitive.effect)]
        return node.sort, handle

    def _support(
        self, expression: ExprID, variable: ExprID
    ) -> tuple[bool, bool, int, int]:
        node = self.expressions.node(expression)
        input_node = self.expressions.node(variable)
        expected = FormalPort(input_node.sort, input_node.role)
        depends = expected in node.free_ports
        foreign = any(port != expected for port in node.free_ports)
        return depends, foreign, 1, 1

    def validate(self, task: ContinuationTask) -> None:
        if type(task) is NormalizePrimitiveLambda:
            node = self.expressions.node(task.function)
            if type(node.sort) is not FunctionSort:
                raise ValueError("continuation normalization requires a typed function")
            return
        if type(task) is not CompilePrimitiveFunction:
            raise ValueError("unknown primitive continuation task")
        self._input(task.variable)
        sort = self.expressions.node(task.expression).sort
        if type(sort) is StateSort:
            if self.expressions.primitive(sort.action) is None:
                raise ValueError(
                    "finite continuation output requires an admitted primitive"
                )
        elif type(sort) is not SymbolSort:
            raise ValueError("finite continuation output is not a finite interface")
        if self._support(task.expression, task.variable)[1]:
            raise ValueError("finite continuation has an additional free port")

    def _admit_binding(self, expression: ExprID) -> bool:
        # Resolve the scoped handle before the semantic proof cache.  A warm hit
        # may skip the expensive expression walk, never owner/kind validation.
        self.expressions.node(expression)
        cached = self.binding_admission.get(expression)
        if cached is not None:
            self.ledger.bump(
                _execution_keys.PRIMITIVE_CONTINUATION_BINDING_ADMISSION_HITS
            )
            return cached
        eligible, visits, peak = function_program_admission(
            self.expressions, expression
        )
        self.ledger.bump(
            _execution_keys.PRIMITIVE_CONTINUATION_BINDING_ADMISSION_FRAMES,
            visits,
        )
        self.ledger.bump(
            _execution_keys.PRIMITIVE_CONTINUATION_BINDING_ADMISSION_PEAK,
            max(
                0,
                peak
                - self.ledger.counters.get(
                    _execution_keys.PRIMITIVE_CONTINUATION_BINDING_ADMISSION_PEAK,
                    0,
                ),
            ),
        )
        self.binding_admission[expression] = eligible
        return eligible

    def probe(self, task: ContinuationTask) -> ExprID | TransferSummaryID | None:
        self.validate(task)
        self.ledger.bump(_execution_keys.PRIMITIVE_CONTINUATION_REQUESTS)
        found: ExprID | TransferSummaryID | None
        if isinstance(task, NormalizePrimitiveLambda):
            found = self.normalized.get(task)
            if found is not None:
                self.ledger.bump(_execution_keys.PRIMITIVE_CONTINUATION_CACHE_HITS)
                return found
            if not self._admit_binding(task.function):
                return None
        else:
            depends, _, visits, peak = self._support(task.expression, task.variable)
            self.ledger.bump(
                _execution_keys.PRIMITIVE_CONTINUATION_SUPPORT_METADATA_READS,
                2 * visits,
            )
            self.ledger.bump(
                _execution_keys.PRIMITIVE_CONTINUATION_ADMISSION_WORKSPACE_PEAK,
                max(
                    0,
                    peak
                    - self.ledger.counters.get(
                        _execution_keys.PRIMITIVE_CONTINUATION_ADMISSION_WORKSPACE_PEAK,
                        0,
                    ),
                ),
            )
            if not depends or isinstance(
                self.expressions.node(task.expression).sort, SymbolSort
            ):
                return None
            found = self.maps.get(task)
            if found is not None:
                self.ledger.bump(_execution_keys.PRIMITIVE_CONTINUATION_CACHE_HITS)
                return found
            if not self._admit_binding(task.expression):
                return None
            limit = self.ledger.max_cache_entries
            if limit is not None and self.ledger.entries >= limit:
                raise BlockContextBudgetExceeded(
                    "primitive function binding needs one free cache entry"
                )
        return None

    def _validate_result(self, task: ContinuationTask, result: Result) -> int:
        self.validate(task)
        if isinstance(task, NormalizePrimitiveLambda):
            result_node = self.expressions.node(_expression(result))
            if result_node.sort != self.expressions.node(task.function).sort:
                raise ValueError("normalized continuation has another signature")
            return 1
        source, _ = self._input(task.variable)
        target = self.expressions.node(task.expression).sort
        assert isinstance(target, (StateSort, SymbolSort))
        return self.admission.validate(source, target, _function(result))

    def publish(self, task: ContinuationTask, result: Result) -> None:
        visits = self._validate_result(task, result)
        self.ledger.bump(
            _execution_keys.PRIMITIVE_CONTINUATION_RESULT_VALIDATION_VISITS,
            visits,
        )
        if isinstance(task, NormalizePrimitiveLambda):
            expression = _expression(result)
            if (
                expression != task.function
                and self._admit_binding(task.function)
                and self._admit_binding(expression)
                and retain_expression_response(
                    self.expressions, expression, (task.function,)
                )
            ):
                self.normalized[task] = expression
        else:
            depends = self._support(task.expression, task.variable)[0]
            self.ledger.bump(
                _execution_keys.PRIMITIVE_CONTINUATION_SUPPORT_METADATA_READS
            )
            if (
                depends
                and isinstance(self.expressions.node(task.expression).sort, StateSort)
                and self._admit_binding(task.expression)
            ):
                self.maps[task] = _function(result)
        self.ledger.bump(_execution_keys.PRIMITIVE_CONTINUATION_EVALUATIONS)

    def program(self, task: ContinuationTask) -> Generator[Task, Result, Result]:
        if isinstance(task, NormalizePrimitiveLambda):
            return (yield from self._normalize(task))
        return (yield from self._compile(task))

    def _normalize(
        self, task: NormalizePrimitiveLambda
    ) -> Generator[Task, Result, Result]:
        arena = self.expressions
        node = arena.node(task.function)
        assert isinstance(node.sort, FunctionSort)
        signature = node.sort
        if (
            node.kind != "lambda"
            or arena.constant_function(task.function) is not None
            or arena.primitive(signature.domain.action) is None
        ):
            self.ledger.bump(_execution_keys.PRIMITIVE_CONTINUATION_DECLINED)
            return task.function
        variable = arena.fresh_variable(
            signature.domain, "primitive-continuation-input", (task.function,)
        )
        body = arena.apply(task.function, variable)
        foreign = self._support(body, variable)[1]
        self.ledger.bump(_execution_keys.PRIMITIVE_CONTINUATION_SUPPORT_METADATA_READS)
        if foreign:
            self.ledger.bump(_execution_keys.PRIMITIVE_CONTINUATION_DECLINED)
            return task.function
        if arena.primitive(signature.codomain.action) is None:
            head_expression = _expression((yield ResolveExpr(body)))
            head = arena.node(head_expression)
            if head.kind != "pair":
                self.ledger.bump(_execution_keys.PRIMITIVE_CONTINUATION_DECLINED)
                return task.function
            anchor = arena.anchor(head_expression)
            anchor_function = arena.lambda_(variable, anchor)
            normalized_anchor = _expression(
                (yield NormalizePrimitiveLambda(anchor_function))
            )
            continuation = arena.continuation(head_expression)
            normalized_continuation = _expression(
                (yield NormalizePrimitiveLambda(continuation))
            )
            new_body = arena.pair(
                signature.codomain.action,
                signature.codomain.side,
                arena.apply(normalized_anchor, variable),
                normalized_continuation,
            )
            self.ledger.bump(_execution_keys.PRIMITIVE_CONTINUATION_PAIR_DECOMPOSITIONS)
            return arena.lambda_(variable, new_body)
        head = arena.node(body)
        if head.kind in ("finite_apply", "finite_map") and head.children == (
            variable.local_id,
        ):
            return task.function
        finite = _function((yield CompilePrimitiveFunction(variable, body)))
        normalized = arena.finite_map(
            signature.domain, signature.codomain, finite, variable
        )
        self.ledger.bump(_execution_keys.PRIMITIVE_CONTINUATION_EXTENSIONAL_REDUCTIONS)
        return arena.lambda_(variable, normalized)

    def _compile(
        self, task: CompilePrimitiveFunction
    ) -> Generator[Task, Result, Result]:
        arena = self.expressions
        source, source_kernel = self._input(task.variable)
        source_primitive = self.kernels.kernel(source_kernel)
        domain = len(source_primitive.domain(BoundarySide(source.side)))
        port = LEFT_A if source.side == 0 else RIGHT_A
        node = arena.node(task.expression)
        if node.kind in ("call", "anchor", "continuation", "apply"):
            head = _expression((yield ResolveExpr(task.expression)))
            if head == task.expression:
                raise ValueError(
                    "finite continuation contains an unresolved structural expression"
                )
            return (yield CompilePrimitiveFunction(task.variable, head))
        if node.kind == "port":
            if task.expression != task.variable:
                raise ValueError("finite continuation contains another port")
            return input_expression(self.kernels, domain, port)
        if node.kind == "literal":
            assert isinstance(node.sort, StateSort)
            primitive = arena.primitive(node.sort.action)
            assert primitive is not None
            return self.kernels.constant(
                len(primitive.domain(BoundarySide(node.sort.side))), node.value
            )
        if node.kind == "symbol":
            assert isinstance(node.sort, SymbolSort)
            return self.kernels.constant(node.sort.blank + 1, node.value)
        if node.kind in ("finite_apply", "finite_map"):
            assert node.function is not None
            argument = arena._handle(node.children[0])
            input_sort = arena.node(argument).sort
            assert isinstance(input_sort, StateSort)
            primitive = arena.primitive(input_sort.action)
            assert primitive is not None
            argument_map = _function(
                (yield CompilePrimitiveFunction(task.variable, argument))
            )
            old_port = LEFT_A if input_sort.side == 0 else RIGHT_A
            bindings = substitution_bindings(
                self.kernels,
                len(primitive.domain(BoundarySide(input_sort.side))),
                old_port,
                argument_map,
            )
            self.ledger.bump(
                _execution_keys.PRIMITIVE_CONTINUATION_FUNCTION_COMPOSITIONS
            )
            return self.kernels.substitute(node.function, bindings)
        if node.kind not in ("advance", "emit") or node.action is None:
            raise ValueError("unsupported finite continuation constructor")
        arguments: list[TransferSummaryID] = []
        for child in node.children:
            arguments.append(
                _function(
                    (
                        yield CompilePrimitiveFunction(
                            task.variable, arena._handle(child)
                        )
                    )
                )
            )
        if len(arguments) not in (2, 3):
            raise AssertionError("primitive continuation exceeded its fixed arity")
        self.ledger.bump(
            _execution_keys.PRIMITIVE_CONTINUATION_ARGUMENT_PEAK,
            max(
                0,
                len(arguments)
                - self.ledger.counters.get(
                    _execution_keys.PRIMITIVE_CONTINUATION_ARGUMENT_PEAK, 0
                ),
            ),
        )
        target = self.kernels._kernel_ids.get(
            _effect_key(self.runtime.actions.primitive(node.action))
        )
        if target is None:
            raise ValueError("primitive continuation operation was not admitted")
        functions = self.kernels.functions
        constants = all(
            functions._resolve(bit) < 2
            for argument in arguments
            for bit in self.kernels.expression(argument).bits
        )
        self.ledger.bump(_execution_keys.PRIMITIVE_CONTINUATION_KERNEL_LIFTS)
        if constants:
            if node.kind == "advance":
                return self.kernels.advance_expression(
                    target, BoundarySide(node.side), arguments[0], arguments[1]
                )
            return self.kernels.emit_expression(
                target, arguments[0], arguments[1], arguments[2]
            )
        return arena.unary.mapped(
            source_kernel,
            source.side,
            port,
            target,
            node.kind,
            node.side if node.kind == "advance" else 0,
            tuple(arguments),
        )
