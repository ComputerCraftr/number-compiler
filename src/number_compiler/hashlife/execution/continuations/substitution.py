"""Store-free substitution operations."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.execution.continuations.higher_types import (
    HigherExpression,
    HigherExpressionID,
    HigherFunction,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.higher_semantic import (
        HigherSemanticArena,
    )


def bind_free(
    self: HigherSemanticArena,
    expression: HigherExpressionID,
    variable: HigherExpressionID,
    replacement: HigherExpressionID,
) -> HigherExpressionID:
    """Bind one free port lazily without cloning its expression DAG."""
    node, variable_node, replacement_node = (
        self.expression(expression),
        self.expression(variable),
        self.expression(replacement),
    )
    if variable_node.kind != "variable":
        raise ValueError("higher deferred binding requires a free variable")
    if variable_node.sort != replacement_node.sort:
        raise ValueError("higher deferred binding sorts disagree")
    if variable == replacement:
        return expression
    if variable.local_id not in self._expression_free_ids[expression.local_id]:
        return expression
    if expression == variable:
        return replacement
    return self._intern_expression(
        HigherExpression(
            "bind-free",
            node.sort,
            (expression.local_id, replacement.local_id),
            value=variable.local_id,
        )
    )


def substitute(
    self: HigherSemanticArena,
    expression: HigherExpressionID,
    variable: HigherExpressionID,
    replacement: HigherExpressionID,
) -> HigherExpressionID:
    from number_compiler.hashlife.execution.continuations.higher_semantic import (
        _Rewrite,
    )

    _root, old, new = (
        self.expression(expression),
        self.expression(variable),
        self.expression(replacement),
    )
    if old.sort != new.sort or old.kind not in ("variable", "bound"):
        raise ValueError("higher substitution requires equal variable/value sorts")
    if variable.local_id not in self._expression_free_ids[expression.local_id]:
        return expression
    key = _Rewrite(expression.local_id, variable.local_id, replacement.local_id)
    found = self._rewrites.get(key)
    if found is not None:
        return found
    self.ledger.reserve(self._rewrite_owner, entries=1, nodes=0)
    try:
        pending = [(expression.local_id, False)]
        built: dict[int, int] = {}
        while pending:
            local_id, ready = pending.pop()
            if local_id in built:
                continue
            if local_id == variable.local_id:
                built[local_id] = replacement.local_id
                continue
            node = self._expressions[local_id]
            function_body = None
            if node.function is not None:
                nested = self.function_record(node.function)
                # A nested function shadows the canonical bound variable
                # for its own domain.  Substitution must not cross it.
                if nested.parameter != variable:
                    function_body = nested.body.local_id
            visible_children = (
                node.children[1:]
                if node.kind == "bind-free" and node.value == variable.local_id
                else node.children
            )
            dependencies = visible_children + (
                () if function_body is None else (function_body,)
            )
            if not dependencies:
                built[local_id] = local_id
                continue
            if not ready:
                pending.append((local_id, True))
                pending.extend((child, False) for child in reversed(dependencies))
                continue
            children = tuple(
                child if child not in built else built[child] for child in node.children
            )
            rewritten_function = node.function
            if node.function is not None and function_body is not None:
                function_record = self.function_record(node.function)
                rewritten_body = self._expression_handle(built[function_body])
                if rewritten_body != function_record.body:
                    rewritten_function = self._intern_function(
                        HigherFunction(
                            function_record.signature,
                            function_record.parameter,
                            rewritten_body,
                            self._function_free_variables(
                                rewritten_body,
                                function_record.parameter,
                            ),
                            function_record.parameter
                            in self._free_variables(
                                rewritten_body,
                            ),
                        )
                    )
            if children == node.children and rewritten_function == node.function:
                built[local_id] = local_id
            else:
                rebuilt_children = tuple(
                    self._expression_handle(child) for child in children
                )
                if node.kind == "anchor":
                    rebuilt_id = self.anchor(rebuilt_children[0])
                elif node.kind == "continuation":
                    rebuilt_id = self.continuation(rebuilt_children[0])
                elif node.kind == "apply":
                    rebuilt_id = self._intern_expression(
                        HigherExpression(
                            "apply",
                            node.sort,
                            (
                                rebuilt_children[0].local_id,
                                rebuilt_children[1].local_id,
                            ),
                        )
                    )
                elif node.kind == "bind-free":
                    rebuilt_id = self.bind_free(
                        rebuilt_children[0],
                        self._expression_handle(node.value),
                        rebuilt_children[1],
                    )
                elif node.kind == "primitive-step":
                    if node.action is None:
                        raise AssertionError("primitive step lost its action")
                    rebuilt_id = self.primitive_step(
                        node.action,
                        node.side,
                        rebuilt_children[0],
                        rebuilt_children[1],
                    )
                elif node.kind == "primitive-emit":
                    if node.action is None:
                        raise AssertionError("primitive emit lost its action")
                    rebuilt_id = self.primitive_emit(
                        node.action,
                        rebuilt_children[0],
                        rebuilt_children[1],
                        rebuilt_children[2],
                    )
                elif node.kind == "select":
                    rebuilt_id = self.select(*rebuilt_children)
                elif node.kind == "equal-constant":
                    rebuilt_id = self.equal_constant(rebuilt_children[0], node.value)
                elif node.kind == "function" and rewritten_function is not None:
                    rebuilt_id = self.function_expression(rewritten_function)
                else:
                    rebuilt_id = self._intern_expression(
                        HigherExpression(
                            node.kind,
                            node.sort,
                            children,
                            node.action,
                            node.side,
                            node.value,
                            node.role,
                            rewritten_function,
                        )
                    )
                built[local_id] = rebuilt_id.local_id
        result = self._expression_handle(built[expression.local_id])
    except BaseException:
        self.ledger.release(self._rewrite_owner, entries=1)
        raise
    self._rewrites[key] = result
    self._substitutions += 1
    return result
