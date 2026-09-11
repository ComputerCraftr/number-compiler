"""Iterative observation of typed higher semantic expressions."""

from __future__ import annotations

from collections.abc import Mapping
from typing import TYPE_CHECKING, cast

from number_compiler.hashlife.execution.continuations.higher_types import (
    FieldAtomSort,
    HigherExpressionID,
)
from number_compiler.hashlife.execution.continuations.higher_values import (
    RuntimeActionFunction,
    RuntimeAtom,
    RuntimeFunction,
    RuntimePair,
    RuntimeTableFunction,
    RuntimeValueID,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.higher_semantic import (
        HigherSemanticArena,
    )


def evaluate_higher(
    arena: HigherSemanticArena,
    expression: HigherExpressionID,
    inputs: Mapping[HigherExpressionID, object] | None = None,
) -> object:
    """Evaluate with canonical scoped runtime values and no Python recursion."""
    arena.expression(expression)
    values_arena = arena.runtime_values
    environment = -1
    for variable, value in ({} if inputs is None else dict(inputs)).items():
        node = arena.expression(variable)
        if node.kind != "variable":
            raise ValueError("higher evaluation inputs require free variables")
        if type(value) is int:
            atom: RuntimeAtom = value
        elif type(value) is RuntimeValueID:
            atom = value
        else:
            raise TypeError("higher inputs require bounded atoms or scoped values")
        environment = values_arena.intern_environment(
            environment,
            variable.local_id,
            atom,
        )
    tasks: list[tuple[object, ...]] = [
        ("eval", expression.local_id, environment, None),
    ]
    stack: list[RuntimeAtom] = []
    peak = 1
    frames = 0
    try:
        while tasks:
            frames += 1
            peak = max(peak, len(tasks) + len(stack))
            task = tasks.pop()
            if task[0] == "resume-operation":
                from number_compiler.hashlife.execution.continuations.higher_operations import (
                    OperationMachine,
                    RuntimeFunctionRequest,
                )
                from number_compiler.hashlife.execution.continuations.operation_dependencies import (
                    advance_operation,
                )

                machine = task[1]
                if type(machine) is not OperationMachine:
                    raise AssertionError("higher evaluator lost its operation machine")
                supplied = stack.pop() if task[2] else None
                outcome = advance_operation(arena, machine, supplied)
                if isinstance(outcome, RuntimeFunctionRequest):
                    record = arena.function_record(outcome.function.function)
                    nested = values_arena.intern_environment(
                        outcome.function.environment,
                        record.parameter.local_id,
                        outcome.argument,
                    )
                    tasks.append(("resume-operation", machine, True))
                    tasks.append(("eval", record.body.local_id, nested, None))
                else:
                    stack.append(outcome)
                continue
            mode, local_id, env, raw_cache_key = task
            if (
                type(mode) is not str
                or type(local_id) is not int
                or type(env) is not int
            ):
                raise AssertionError("invalid higher expression task")
            cache_key = cast(tuple[int, int] | None, raw_cache_key)
            node = arena._expressions[local_id]
            if mode == "cache":
                if cache_key is None:
                    raise AssertionError("higher evaluation lost its cache key")
                values_arena.publish_evaluation(cache_key[0], cache_key[1], stack[-1])
                continue
            if mode == "select":
                condition = stack.pop()
                if type(condition) is not int or condition not in (0, 1):
                    raise ValueError("higher selection received a non-boolean")
                branch = node.children[1] if condition else node.children[2]
                tasks.append(("eval", branch, env, None))
                continue
            if mode == "apply-function":
                function_id = stack.pop()
                if type(function_id) is not RuntimeValueID:
                    raise ValueError("higher application received a non-function")
                function = values_arena.resolve(function_id)
                if type(function) not in (
                    RuntimeFunction,
                    RuntimeActionFunction,
                    RuntimeTableFunction,
                ):
                    raise ValueError("higher application received a non-function")
                if type(function) is RuntimeFunction:
                    record = arena.function_record(function.function)
                    if not record.parameter_used:
                        tasks.append(
                            ("eval", record.body.local_id, function.environment, None)
                        )
                        continue
                    stack.append(function_id)
                    tasks.append(("finish", local_id, env, None))
                    tasks.append(("eval", node.children[1], env, None))
                else:
                    stack.append(function_id)
                    tasks.append(("finish", local_id, env, None))
                    tasks.append(("eval", node.children[1], env, None))
                continue
            if mode == "bind-free":
                replacement = stack.pop()
                nested = values_arena.intern_environment(env, node.value, replacement)
                tasks.append(("eval", node.children[0], nested, None))
                continue
            if mode == "eval":
                env = values_arena.project_environment(
                    env,
                    arena._expression_free_ids[local_id],
                    projection=local_id,
                )
                key = local_id, env
                cached = values_arena.evaluations.get(key)
                if cached is not None:
                    values_arena.validate_atom(cached)
                    stack.append(cached)
                    continue
                if node.kind in ("variable", "bound"):
                    value = values_arena.lookup(env, local_id)
                    if value is None:
                        raise ValueError(
                            f"higher expression contains unbound {node.kind} {local_id}"
                        )
                    stack.append(value)
                    values_arena.publish_evaluation(local_id, env, value)
                elif node.kind in ("literal", "symbol", "constant"):
                    stack.append(node.value)
                    values_arena.publish_evaluation(local_id, env, node.value)
                elif node.kind == "function":
                    if node.function is None:
                        raise AssertionError("function expression lost its function ID")
                    captured = values_arena.project_environment(
                        env,
                        tuple(
                            free.local_id
                            for free in arena.function_record(
                                node.function
                            ).free_variables
                        ),
                        projection=-(node.function.local_id + 2),
                    )
                    value = values_arena.function(node.function, captured)
                    stack.append(value)
                    values_arena.publish_evaluation(local_id, env, value)
                elif node.kind == "select":
                    tasks.append(("cache", local_id, env, key))
                    tasks.append(("select", local_id, env, None))
                    tasks.append(("eval", node.children[0], env, None))
                elif node.kind == "apply":
                    tasks.append(("cache", local_id, env, key))
                    tasks.append(("apply-function", local_id, env, None))
                    tasks.append(("eval", node.children[0], env, None))
                elif node.kind == "bind-free":
                    tasks.append(("cache", local_id, env, key))
                    tasks.append(("bind-free", local_id, env, None))
                    tasks.append(("eval", node.children[1], env, None))
                else:
                    tasks.append(("cache", local_id, env, key))
                    tasks.append(("finish", local_id, env, None))
                    tasks.extend(
                        ("eval", child, env, None) for child in reversed(node.children)
                    )
                continue
            if node.kind == "pair":
                continuation, anchor = stack.pop(), stack.pop()
                if type(continuation) is not RuntimeValueID:
                    raise ValueError(
                        "higher pair continuation did not evaluate to a function"
                    )
                stack.append(values_arena.pair(anchor, continuation))
            elif node.kind == "anchor":
                pair_id = stack.pop()
                if type(pair_id) is not RuntimeValueID:
                    raise ValueError("higher anchor received a primitive state")
                pair = values_arena.resolve(pair_id)
                if type(pair) is not RuntimePair:
                    raise ValueError("higher anchor received a non-pair state")
                stack.append(pair.anchor)
            elif node.kind == "continuation":
                pair_id = stack.pop()
                if type(pair_id) is not RuntimeValueID:
                    raise ValueError("higher continuation received a primitive state")
                pair = values_arena.resolve(pair_id)
                if type(pair) is not RuntimePair:
                    raise ValueError("higher continuation received a non-pair state")
                stack.append(pair.continuation)
            elif node.kind == "apply":
                argument, function_id = stack.pop(), stack.pop()
                if type(function_id) is not RuntimeValueID:
                    raise ValueError("higher application received a non-function")
                function = values_arena.resolve(function_id)
                if type(function) is RuntimeTableFunction:
                    if type(argument) is not int or not 0 <= argument < len(
                        function.outputs
                    ):
                        raise ValueError(
                            "bounded function argument is outside its domain"
                        )
                    stack.append(function.outputs[argument])
                    continue
                if type(function) is RuntimeActionFunction:
                    from number_compiler.hashlife.execution.continuations.higher_operations import (
                        start_function_application,
                    )

                    tasks.append(
                        (
                            "resume-operation",
                            start_function_application(function_id, argument),
                            False,
                        )
                    )
                    continue
                if type(function) is not RuntimeFunction:
                    raise ValueError("higher application received a non-function")
                record = arena.function_record(function.function)
                nested = values_arena.intern_environment(
                    function.environment,
                    record.parameter.local_id,
                    argument,
                )
                tasks.append(("eval", record.body.local_id, nested, None))
            elif node.kind == "retag":
                stack.append(stack.pop())
            elif node.kind == "equal-constant":
                value = stack.pop()
                if type(value) is not int:
                    raise ValueError("higher equality received a structured value")
                stack.append(int(value == node.value))
            elif node.kind == "add-constant":
                value = stack.pop()
                if type(value) is not int or type(node.sort) is not FieldAtomSort:
                    raise ValueError("higher addition received a structured value")
                result = value + node.value
                if not 0 <= result < node.sort.cardinality:
                    raise ValueError("higher bounded addition overflowed")
                stack.append(result)
            elif node.kind == "primitive-step":
                symbol, state = stack.pop(), stack.pop()
                if (
                    type(state) is not int
                    or type(symbol) is not int
                    or node.action is None
                ):
                    raise ValueError("primitive step received a structured operand")
                stack.append(arena.schema.step(node.action, node.side, state, symbol))
            elif node.kind == "primitive-emit":
                right, symbol, left = stack.pop(), stack.pop(), stack.pop()
                if (
                    type(left) is not int
                    or type(symbol) is not int
                    or type(right) is not int
                    or node.action is None
                ):
                    raise ValueError("primitive emit received a structured operand")
                stack.append(arena.schema.emit(node.action, left, symbol, right))
            elif node.kind in ("action-initial", "action-step", "action-emit"):
                from number_compiler.hashlife.execution.continuations.higher_operations import (
                    start_operation,
                )

                if node.action is None:
                    raise AssertionError("opaque higher operation lost its action")
                arity = {"action-initial": 0, "action-step": 2, "action-emit": 3}[
                    node.kind
                ]
                operands = tuple(reversed([stack.pop() for _ in range(arity)]))
                machine = start_operation(
                    node.kind.removeprefix("action-"),
                    node.action,
                    node.side,
                    operands,
                )
                tasks.append(("resume-operation", machine, False))
            else:
                raise AssertionError(f"unhandled higher expression {node.kind}")
    finally:
        arena.ledger.bump("higher_semantic_task_frames", frames)
    if len(stack) != 1:
        raise AssertionError("higher evaluator did not produce one result")
    arena._evaluations += 1
    arena._evaluation_workspace_peak = max(arena._evaluation_workspace_peak, peak)
    arena.ledger.bump("higher_semantic_evaluations")
    return stack[0]


__all__ = ["evaluate_higher"]
