"""Store-free substitution operations."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.execution.continuations.higher_types import (
    HigherExpression,
    HigherExpressionID,
    HigherFunction,
    HigherRewriteKey,
)
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
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
    if variable.local_id not in self.free_variable_local_ids(expression):
        return expression
    if expression == variable:
        return replacement
    return self.intern_expression(
        HigherExpression(
            "bind-free",
            node.sort,
            (expression.local_id, replacement.local_id),
            value=variable.local_id,
        )
    )


def bind_free_many(
    self: HigherSemanticArena,
    expression: HigherExpressionID,
    bindings: tuple[tuple[HigherExpressionID, HigherExpressionID], ...],
) -> HigherExpressionID:
    """Suspend simultaneous port substitution without traversing the body.

    All replacements see the original environment. Fresh staging variables
    depend on the complete supplied binding vector, so no replacement can
    contain another staging variable, including on repeated calls. This adds
    at most three expression nodes per relevant port; it is not a bound on
    subsequent evaluation or on free-variable metadata storage.
    """
    self.expression(expression)
    if type(bindings) is not tuple:
        raise TypeError("simultaneous bindings require an immutable port vector")
    seen: set[int] = set()
    relevant: list[tuple[HigherExpressionID, HigherExpressionID]] = []
    free = self.free_variable_local_ids(expression)
    for binding in bindings:
        self.ledger.bump(_execution_keys.HIGHER_SIMULTANEOUS_BINDING_PAIRS_CHECKED)
        if type(binding) is not tuple or len(binding) != 2:
            raise TypeError("simultaneous bindings require variable/value pairs")
        variable, replacement = binding
        old, new = self.expression(variable), self.expression(replacement)
        if old.kind != "variable" or old.sort != new.sort:
            raise ValueError("simultaneous bindings require equal free-port sorts")
        if variable.local_id in seen:
            raise ValueError("simultaneous bindings repeat a free port")
        seen.add(variable.local_id)
        if variable != replacement and variable.local_id in free:
            relevant.append((variable, replacement))
    if not relevant:
        return expression
    if len(relevant) == 1:
        variable, replacement = relevant[0]
        self.ledger.bump(_execution_keys.HIGHER_SIMULTANEOUS_BINDING_PORTS)
        return bind_free(self, expression, variable, replacement)
    relevant.sort(key=lambda binding: binding[0].local_id)
    dependencies = (expression,) + tuple(item for pair in relevant for item in pair)
    staged: list[tuple[HigherExpressionID, HigherExpressionID]] = []
    for variable, replacement in relevant:
        placeholder = self.variable(
            self.expression(variable).sort,
            f"simultaneous-free-port:{variable.local_id}",
            dependencies,
        )
        expression = bind_free(self, expression, variable, placeholder)
        staged.append((placeholder, replacement))
    for placeholder, replacement in staged:
        expression = bind_free(self, expression, placeholder, replacement)
    self.ledger.bump(_execution_keys.HIGHER_SIMULTANEOUS_BINDING_PORTS, len(relevant))
    return expression


def substitute(
    self: HigherSemanticArena,
    expression: HigherExpressionID,
    variable: HigherExpressionID,
    replacement: HigherExpressionID,
) -> HigherExpressionID:
    _root, old, new = (
        self.expression(expression),
        self.expression(variable),
        self.expression(replacement),
    )
    if old.sort != new.sort or old.kind not in ("variable", "bound"):
        raise ValueError("higher substitution requires equal variable/value sorts")
    if variable.local_id not in self.free_variable_local_ids(expression):
        return expression
    key = HigherRewriteKey(
        expression.local_id,
        variable.local_id,
        replacement.local_id,
    )
    found = self.begin_rewrite(key)
    if found is not None:
        return found
    try:
        pending = [(expression.local_id, False)]
        built: dict[int, int] = {}
        while pending:
            local_id, ready = pending.pop()
            if local_id in built:
                continue
            # Variable dependency children are identity metadata, not free
            # occurrences. Respect the same lexical scope used by interning
            # and skip subgraphs that cannot contain the substituted variable.
            local_expression = self.expression_id(local_id)
            if variable.local_id not in self.free_variable_local_ids(local_expression):
                built[local_id] = local_id
                continue
            if local_id == variable.local_id:
                built[local_id] = replacement.local_id
                continue
            node = self.expression(local_expression)
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
            children = tuple(built.get(child, child) for child in node.children)
            rewritten_function = node.function
            if node.function is not None and function_body is not None:
                function_record = self.function_record(node.function)
                rewritten_body = self.expression_id(built[function_body])
                if rewritten_body != function_record.body:
                    rewritten_function = self.intern_function(
                        HigherFunction(
                            function_record.signature,
                            function_record.parameter,
                            rewritten_body,
                            tuple(
                                item
                                for item in self.component_free_variables(
                                    rewritten_body
                                )
                                if item != function_record.parameter
                            ),
                            function_record.parameter
                            in self.component_free_variables(
                                rewritten_body,
                            ),
                        )
                    )
            if children == node.children and rewritten_function == node.function:
                built[local_id] = local_id
            else:
                rebuilt_children = tuple(
                    self.expression_id(child) for child in children
                )
                if node.kind == "anchor":
                    rebuilt_id = self.anchor(rebuilt_children[0])
                elif node.kind == "continuation":
                    rebuilt_id = self.continuation(rebuilt_children[0])
                elif node.kind == "apply":
                    rebuilt_id = self.intern_expression(
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
                        self.expression_id(node.value),
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
                    rebuilt_id = self.intern_expression(
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
        result = self.expression_id(built[expression.local_id])
    except BaseException:
        self.cancel_rewrite()
        raise
    self.publish_rewrite(key, result)
    return result
