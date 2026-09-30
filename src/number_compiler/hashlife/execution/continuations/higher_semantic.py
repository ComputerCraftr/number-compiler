"""Source-free typed higher expressions for algebraic field actions.
Recursive product/function boundaries remain canonical DAGs; they are never
flattened into proof-machine Cartesian domains. Evaluation is iterative.
"""

from __future__ import annotations

from collections.abc import Mapping, MutableMapping, MutableSequence
from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.higher_types import (
    FieldAtomSort,
    FieldFunctionSort,
    FieldStateSort,
    FieldSymbolSort,
    HigherActionSchema,
    HigherExpression,
    HigherExpressionID,
    HigherFunction,
    HigherFunctionID,
    HigherSemanticMetrics,
    HigherSort,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import append_indexed_node

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.higher_summaries import (
        HigherSummaryArena,
    )


_MAX_ENUMERATED_PRIMITIVE_STATES = 1 << 12


@dataclass(frozen=True, slots=True)
class _Rewrite:
    root: int
    variable: int
    replacement: int


class HigherSemanticArena:
    """Canonical recursive state/function DAG for one index and action arena."""

    _EXPRESSION_KIND = "higher-semantic-expression"
    _FUNCTION_KIND = "higher-semantic-function"

    def __init__(self, schema: HigherActionSchema) -> None:
        # Verify concrete capabilities without accepting a callable payload
        # into any semantic key.
        required = (
            "validate_action",
            "children",
            "kind",
            "alphabet",
            "state_count",
            "initial",
            "step",
            "emit",
        )
        if any(not callable(getattr(schema, name, None)) for name in required):
            raise TypeError("higher semantics require a complete action schema")
        candidate_ledger = getattr(schema, "ledger", None)
        if type(candidate_ledger) is not ResourceLedger:
            raise TypeError("higher semantics require one index ledger")
        self.schema = schema
        self.ledger: ResourceLedger = candidate_ledger
        self.owner = ArenaToken("higher-field-semantics")
        self.ledger.register_execution_root(self)
        prefix = f"higher-field-{len(self.ledger.inventory())}"
        self._expression_owner = self.ledger.register(
            prefix + "-expressions",
            "higher_semantic_expression",
        )
        self._expression_key_owner = self.ledger.register(
            prefix + "-expression-keys",
            "higher_semantic_expression_interner",
        )
        self._expression_free_owner = self.ledger.register(
            prefix + "-expression-free-ports",
            "higher_semantic_metadata",
        )
        self._function_owner = self.ledger.register(
            prefix + "-functions",
            "higher_semantic_function",
        )
        self._function_key_owner = self.ledger.register(
            prefix + "-function-keys",
            "higher_semantic_function_interner",
        )
        self._rewrite_owner = self.ledger.register(
            prefix + "-rewrites",
            "query_memo",
        )
        self._expressions: MutableSequence[HigherExpression] = self.ledger.make_list(
            self._expression_owner,
        )
        self._expression_free_ids: MutableSequence[tuple[int, ...]] = (
            self.ledger.make_list(self._expression_free_owner, nodes_per_entry=0)
        )
        self._expression_keys: MutableMapping[HigherExpression, int] = (
            self.ledger.make_dict(
                self._expression_key_owner,
            )
        )
        self._functions: MutableSequence[HigherFunction] = self.ledger.make_list(
            self._function_owner,
        )
        self._function_keys: MutableMapping[HigherFunction, int] = (
            self.ledger.make_dict(
                self._function_key_owner,
            )
        )
        self._rewrites: MutableMapping[_Rewrite, HigherExpressionID] = (
            self.ledger.make_dict(
                self._rewrite_owner,
            )
        )
        self.ledger.register_container(
            self._expression_owner,
            self._expressions,
            node_count=lambda: len(self._expressions),
            payloads=lambda: self._expressions,
        )
        self.ledger.register_container(
            self._expression_key_owner,
            self._expression_keys,
            payloads=self._expression_keys.items,
        )
        self.ledger.register_container(
            self._expression_free_owner,
            self._expression_free_ids,
            payloads=lambda: self._expression_free_ids,
        )
        self.ledger.register_container(
            self._function_owner,
            self._functions,
            node_count=lambda: len(self._functions),
            payloads=lambda: self._functions,
        )
        self.ledger.register_container(
            self._function_key_owner,
            self._function_keys,
            payloads=self._function_keys.items,
        )
        self.ledger.register_container(
            self._rewrite_owner,
            self._rewrites,
            node_count=lambda: 0,
            payloads=self._rewrites.items,
            evict=self.clear_rewrites,
        )
        self._expression_hits = self._function_hits = self._substitutions = 0
        self._evaluations = self._evaluation_workspace_peak = 0
        self._beta_active = False
        from number_compiler.hashlife.execution.continuations.higher_primitive_tables import (
            HigherPrimitiveTables,
        )
        from number_compiler.hashlife.execution.continuations.higher_values import (
            RuntimeValueArena,
        )

        self.runtime_values = RuntimeValueArena(self.ledger, schema)
        self.runtime_values.bind_function_validator(self.function_record)
        self.primitive_tables = HigherPrimitiveTables(schema, self.ledger)
        self.summary_runtime: HigherSummaryArena | None = None

    def bind_summary_runtime(self, summaries: HigherSummaryArena) -> None:
        if summaries.semantics is not self:
            raise ValueError("higher summary runtime belongs to another semantic arena")
        if self.summary_runtime not in (None, summaries):
            raise ValueError("higher semantics already has another summary runtime")
        self.summary_runtime = summaries

    def clear_rewrites(self) -> None:
        count = len(self._rewrites)
        self._rewrites.clear()
        self.ledger.release(self._rewrite_owner, entries=count)

    def _expression_handle(self, local_id: int) -> HigherExpressionID:
        return HigherExpressionID(self.owner, self._EXPRESSION_KIND, local_id)

    def _function_handle(self, local_id: int) -> HigherFunctionID:
        return HigherFunctionID(self.owner, self._FUNCTION_KIND, local_id)

    def expression(self, reference: HigherExpressionID) -> HigherExpression:
        if type(reference) is not HigherExpressionID:
            raise TypeError("expected a higher expression ID")
        reference.validate(
            self.owner, self._EXPRESSION_KIND, size=len(self._expressions)
        )
        return self._expressions[reference.local_id]

    def function_record(self, reference: HigherFunctionID) -> HigherFunction:
        if type(reference) is not HigherFunctionID:
            raise TypeError("expected a higher function ID")
        reference.validate(self.owner, self._FUNCTION_KIND, size=len(self._functions))
        return self._functions[reference.local_id]

    def component_sort(
        self,
        reference: HigherExpressionID | HigherFunctionID,
    ) -> HigherSort:
        """Return a validated component sort without lowering its behavior."""
        if type(reference) is HigherExpressionID:
            return self.expression(reference).sort
        if type(reference) is HigherFunctionID:
            return self.function_record(reference).signature
        raise TypeError("expected a scoped higher semantic component")

    def component_free_variables(
        self,
        reference: HigherExpressionID | HigherFunctionID,
    ) -> tuple[HigherExpressionID, ...]:
        """Return canonical declared higher ports for interface validation."""
        if type(reference) is HigherExpressionID:
            return self._free_variables(reference)
        if type(reference) is HigherFunctionID:
            return self.function_record(reference).free_variables
        raise TypeError("expected a scoped higher semantic component")

    def _validate_sort(self, sort: HigherSort, *, readonly: bool = False) -> None:
        pending: list[HigherSort] = [sort]
        while pending:
            current = pending.pop()
            if type(current) is FieldStateSort:
                validator = (
                    getattr(self.schema, "validate_action_readonly", None)
                    if readonly
                    else None
                )
                (self.schema.validate_action if validator is None else validator)(
                    current.action
                )
                if type(current.side) is not int or current.side not in (0, 1):
                    raise ValueError("field-state direction must be zero or one")
            elif type(current) is FieldFunctionSort:
                pending.extend((current.codomain, current.domain))
            elif type(current) is FieldSymbolSort:
                if (
                    type(current.base) is not int
                    or current.base < 2
                    or type(current.blank) is not int
                    or not 1 <= current.blank < 1 << 64
                ):
                    raise ValueError("invalid higher symbol sort")
            elif type(current) is FieldAtomSort:
                if (
                    type(current.role) is not str
                    or not current.role
                    or len(current.role) > 128
                    or type(current.cardinality) is not int
                    or not 1 <= current.cardinality <= 1 << 64
                ):
                    raise ValueError("invalid higher bounded-atom sort")
            else:
                raise TypeError("unknown higher semantic sort")

    def state_sort(self, action: FieldCellActionID, side: int) -> FieldStateSort:
        result = FieldStateSort(action, side)
        self._validate_sort(result)
        return result

    def _primitive_state_count(self, action: FieldCellActionID, side: int) -> int:
        count = self.schema.state_count(action, side)
        if type(count) is not int:
            raise TypeError("primitive state cardinality must be an exact integer")
        if not 1 <= count <= _MAX_ENUMERATED_PRIMITIVE_STATES:
            raise ValueError("primitive state domain exceeds its bounded interface")
        return count

    def symbol_sort(self, action: FieldCellActionID) -> FieldSymbolSort:
        self.schema.validate_action(action)
        base, blank = self.schema.alphabet(action)
        result = FieldSymbolSort(base, blank)
        self._validate_sort(result)
        return result

    def function_sort(
        self,
        domain: FieldStateSort,
        codomain: FieldStateSort,
    ) -> FieldFunctionSort:
        result = FieldFunctionSort(domain, codomain)
        self._validate_sort(result)
        return result

    def _intern_expression(self, record: HigherExpression) -> HigherExpressionID:
        self._validate_sort(record.sort)
        found = self._expression_keys.get(record)
        if found is not None:
            self._expression_hits += 1
            return self._expression_handle(found)
        self.ledger.reserve_many(
            (
                (self._expression_owner, 1, 1),
                (self._expression_key_owner, 1, 0),
                (self._expression_free_owner, 1, 0),
            )
        )
        local_id = len(self._expressions)
        self._expressions.append(record)
        free_ids: tuple[int, ...]
        if record.kind in ("variable", "bound"):
            free_ids = (local_id,)
        elif record.kind == "function" and record.function is not None:
            free_ids = tuple(
                value.local_id
                for value in self.function_record(record.function).free_variables
            )
        elif record.kind == "bind-free":
            source, replacement = record.children
            free_ids = tuple(
                sorted(
                    (set(self._expression_free_ids[source]) - {record.value})
                    | set(self._expression_free_ids[replacement])
                )
            )
        else:
            free_ids = tuple(
                sorted(
                    {
                        value
                        for child in record.children
                        for value in self._expression_free_ids[child]
                    }
                )
            )
        self._expression_free_ids.append(free_ids)
        self._expression_keys[record] = local_id
        return self._expression_handle(local_id)

    def variable(
        self,
        sort: HigherSort,
        role: str,
        dependencies: tuple[HigherExpressionID, ...] = (),
    ) -> HigherExpressionID:
        self._validate_sort(sort)
        if type(role) is not str or not role or len(role) > 128:
            raise ValueError("higher variables require a stable role")
        if type(dependencies) is not tuple:
            raise TypeError("higher variable dependencies must be canonical")
        for dependency in dependencies:
            self.expression(dependency)
        return self._intern_expression(
            HigherExpression(
                "variable",
                sort,
                tuple(item.local_id for item in dependencies),
                role=role,
            )
        )

    def _bound(self, sort: FieldStateSort, depth: int = 0) -> HigherExpressionID:
        if type(depth) is not int or depth < 0:
            raise ValueError("higher binder depth must be nonnegative")
        return self._intern_expression(HigherExpression("bound", sort, value=depth))

    def _binder_depth(
        self,
        expression: HigherExpressionID,
        sort: FieldStateSort,
    ) -> int:
        from number_compiler.hashlife.execution.continuations.higher_binding import (
            binder_depth,
        )

        return binder_depth(self, expression, sort)

    def literal(
        self,
        action: FieldCellActionID,
        side: int,
        value: int,
    ) -> HigherExpressionID:
        sort = self.state_sort(action, side)
        kind = self.schema.kind(action)
        if kind == "compose":
            raise ValueError("composed field states require a structured pair")
        count = self._primitive_state_count(action, side)
        if type(value) is not int or not 0 <= value < count:
            raise ValueError("higher literal is outside its primitive state domain")
        return self._intern_expression(
            HigherExpression(
                "literal",
                sort,
                action=action,
                side=side,
                value=value,
            )
        )

    def initial(self, action: FieldCellActionID, side: int) -> HigherExpressionID:
        """Construct a composed initial state bottom-up without recursion."""
        self.state_sort(action, side)
        pending = [(action, side, False)]
        built: dict[tuple[int, int], HigherExpressionID] = {}
        while pending:
            current, current_side, ready = pending.pop()
            key = current.local_id, current_side
            if key in built:
                continue
            children = self.schema.children(current)
            if children is None:
                built[key] = self.literal(
                    current,
                    current_side,
                    self.schema.initial(current, current_side),
                )
                continue
            before, after = children
            before_key = before.local_id, current_side
            after_key = after.local_id, current_side
            if not ready:
                pending.append((current, current_side, True))
                if after_key not in built:
                    pending.append((after, current_side, False))
                if before_key not in built:
                    pending.append((before, current_side, False))
                continue
            argument = self.variable(
                self.state_sort(before, 1 - current_side),
                f"higher-initial-opposite:{current_side}",
                (built[before_key], built[after_key]),
            )
            continuation = self.function(argument, built[after_key])
            built[key] = self.pair(
                current,
                current_side,
                built[before_key],
                continuation,
            )
        return built[(action.local_id, side)]

    def symbol(self, action: FieldCellActionID, value: int) -> HigherExpressionID:
        sort = self.symbol_sort(action)
        if type(value) is not int or not 0 <= value <= sort.blank:
            raise ValueError("higher symbol is outside its alphabet")
        return self._intern_expression(
            HigherExpression(
                "symbol",
                sort,
                action=action,
                value=value,
            )
        )

    def constant(self, sort: FieldAtomSort, value: int) -> HigherExpressionID:
        self._validate_sort(sort)
        if type(value) is not int or not 0 <= value < sort.cardinality:
            raise ValueError("higher constant is outside its bounded atom sort")
        return self._intern_expression(HigherExpression("constant", sort, value=value))

    def equal_constant(
        self,
        value: HigherExpressionID,
        expected: int,
    ) -> HigherExpressionID:
        from number_compiler.hashlife.execution.continuations.higher_scalar import (
            canonical_equal_constant,
        )

        return canonical_equal_constant(self, value, expected)

    def add_constant(
        self,
        value: HigherExpressionID,
        offset: int,
        output: FieldAtomSort,
    ) -> HigherExpressionID:
        from number_compiler.hashlife.execution.continuations.higher_scalar import (
            canonical_add_constant,
        )

        return canonical_add_constant(self, value, offset, output)

    def retag(
        self,
        value: HigherExpressionID,
        output: FieldAtomSort,
    ) -> HigherExpressionID:
        from number_compiler.hashlife.execution.continuations.higher_scalar import (
            canonical_retag,
        )

        return canonical_retag(self, value, output)

    def select(
        self,
        condition: HigherExpressionID,
        yes: HigherExpressionID,
        no: HigherExpressionID,
    ) -> HigherExpressionID:
        from number_compiler.hashlife.execution.continuations.higher_scalar import (
            canonical_select,
        )

        return canonical_select(self, condition, yes, no)

    def function_expression(self, function: HigherFunctionID) -> HigherExpressionID:
        record = self.function_record(function)
        return self._intern_expression(
            HigherExpression(
                "function",
                record.signature,
                function=function,
            )
        )

    def constant_function(
        self,
        function: HigherExpressionID,
    ) -> HigherExpressionID | None:
        """Return a function's constant body, or ``None`` when it uses its port."""
        node = self.expression(function)
        if node.kind != "function" or node.function is None:
            return None
        record = self.function_record(node.function)
        return None if record.parameter_used else record.body

    def function(
        self,
        parameter: HigherExpressionID,
        body: HigherExpressionID,
    ) -> HigherFunctionID:
        parameter_node, body_node = self.expression(parameter), self.expression(body)
        if (
            parameter_node.kind != "variable"
            or type(parameter_node.sort) is not FieldStateSort
        ):
            raise ValueError("higher function parameters must be state variables")
        if type(body_node.sort) is not FieldStateSort:
            raise ValueError("higher functions must return field states")
        canonical = self._bound(
            parameter_node.sort,
            self._binder_depth(body, parameter_node.sort),
        )
        normalized = self.substitute(body, parameter, canonical)
        signature = self.function_sort(parameter_node.sort, body_node.sort)
        normalized_node = self.expression(normalized)
        if normalized_node.kind == "apply" and len(normalized_node.children) == 2:
            target = self._expression_handle(normalized_node.children[0])
            supplied = self._expression_handle(normalized_node.children[1])
            target_node = self.expression(target)
            if (
                supplied == canonical
                and target_node.kind == "function"
                and target_node.function is not None
                and canonical not in self._free_variables(target)
            ):
                target_record = self.function_record(target_node.function)
                if target_record.signature == signature:
                    return target_node.function
        free = self._free_variables(normalized)
        return self._intern_function(
            HigherFunction(
                signature,
                canonical,
                normalized,
                tuple(item for item in free if item != canonical),
                canonical in free,
            )
        )

    def _intern_function(self, record: HigherFunction) -> HigherFunctionID:
        found = self._function_keys.get(record)
        if found is not None:
            self._function_hits += 1
            return self._function_handle(found)
        local_id = append_indexed_node(
            self.ledger,
            self._functions,
            self._function_keys,
            self._function_owner,
            self._function_key_owner,
            record,
            record,
        )
        return self._function_handle(local_id)

    def _free_variables(
        self, expression: HigherExpressionID
    ) -> tuple[HigherExpressionID, ...]:
        from number_compiler.hashlife.execution.continuations.higher_binding import (
            free_variables,
        )

        return free_variables(self, expression)

    def _function_free_variables(
        self,
        body: HigherExpressionID,
        parameter: HigherExpressionID,
    ) -> tuple[HigherExpressionID, ...]:
        return tuple(item for item in self._free_variables(body) if item != parameter)

    def pair(
        self,
        action: FieldCellActionID,
        side: int,
        anchor: HigherExpressionID,
        continuation: HigherFunctionID,
    ) -> HigherExpressionID:
        children = self.schema.children(action)
        if self.schema.kind(action) != "compose" or children is None:
            raise ValueError("higher pairs require a composed field action")
        before, after = children
        anchor_node = self.expression(anchor)
        function = self.function_record(continuation)
        expected_anchor = self.state_sort(before, side)
        expected_function = self.function_sort(
            self.state_sort(before, 1 - side),
            self.state_sort(after, side),
        )
        if (
            anchor_node.sort != expected_anchor
            or function.signature != expected_function
        ):
            raise ValueError("higher pair components have incompatible sorts")
        function_expr = self.function_expression(continuation)
        return self._intern_expression(
            HigherExpression(
                "pair",
                self.state_sort(action, side),
                (anchor.local_id, function_expr.local_id),
                action=action,
                side=side,
            )
        )

    def anchor(self, state: HigherExpressionID) -> HigherExpressionID:
        node = self.expression(state)
        if type(node.sort) is not FieldStateSort:
            raise ValueError("higher anchor requires a field state")
        children = self.schema.children(node.sort.action)
        if children is None:
            raise ValueError("primitive state has no higher anchor")
        if node.kind == "pair":
            return self._expression_handle(node.children[0])
        return self._intern_expression(
            HigherExpression(
                "anchor",
                self.state_sort(children[0], node.sort.side),
                (state.local_id,),
                action=node.sort.action,
                side=node.sort.side,
            )
        )

    def continuation(self, state: HigherExpressionID) -> HigherExpressionID:
        node = self.expression(state)
        if type(node.sort) is not FieldStateSort:
            raise ValueError("higher continuation requires a field state")
        children = self.schema.children(node.sort.action)
        if children is None:
            raise ValueError("primitive state has no continuation")
        if node.kind == "pair":
            return self._expression_handle(node.children[1])
        before, after = children
        sort = self.function_sort(
            self.state_sort(before, 1 - node.sort.side),
            self.state_sort(after, node.sort.side),
        )
        return self._intern_expression(
            HigherExpression(
                "continuation",
                sort,
                (state.local_id,),
                action=node.sort.action,
                side=node.sort.side,
            )
        )

    def apply(
        self,
        function: HigherExpressionID,
        argument: HigherExpressionID,
    ) -> HigherExpressionID:
        fn_node, arg_node = self.expression(function), self.expression(argument)
        if (
            type(fn_node.sort) is not FieldFunctionSort
            or arg_node.sort != fn_node.sort.domain
        ):
            raise ValueError("higher application has incompatible argument sort")
        if fn_node.kind == "function" and fn_node.function is not None:
            record = self.function_record(fn_node.function)
            if not record.parameter_used:
                self.ledger.bump("higher_constant_beta_reductions")
                return record.body
            if record.body == record.parameter:
                self.ledger.bump("higher_identity_beta_reductions")
                return argument
            body = self.expression(record.body)
            children = tuple(
                argument
                if child == record.parameter.local_id
                else self._expression_handle(child)
                for child in body.children
            )
            if body.kind == "anchor" and children[0] == argument:
                self.ledger.bump("higher_shallow_beta_reductions")
                return self.anchor(argument)
            if body.kind == "continuation" and children[0] == argument:
                self.ledger.bump("higher_shallow_beta_reductions")
                return self.continuation(argument)
            if (
                body.kind == "primitive-step"
                and body.action is not None
                and record.parameter.local_id in body.children
            ):
                self.ledger.bump("higher_shallow_beta_reductions")
                return self.primitive_step(
                    body.action,
                    body.side,
                    children[0],
                    children[1],
                )
            if (
                body.kind == "primitive-emit"
                and body.action is not None
                and record.parameter.local_id in body.children
            ):
                self.ledger.bump("higher_shallow_beta_reductions")
                return self.primitive_emit(
                    body.action,
                    children[0],
                    children[1],
                    children[2],
                )
            if not self._beta_active:
                from number_compiler.hashlife.execution.continuations.higher_binding import (
                    reachable_size,
                )

                if reachable_size(self, record.body, limit=128) is not None:
                    self._beta_active = True
                    try:
                        result = self.substitute(
                            record.body,
                            record.parameter,
                            argument,
                        )
                    finally:
                        self._beta_active = False
                    self.ledger.bump("higher_bounded_beta_reductions")
                    return result
        return self._intern_expression(
            HigherExpression(
                "apply",
                fn_node.sort.codomain,
                (function.local_id, argument.local_id),
            )
        )

    def primitive_step(
        self,
        action: FieldCellActionID,
        side: int,
        state: HigherExpressionID,
        symbol: HigherExpressionID,
    ) -> HigherExpressionID:
        if self.schema.kind(action) != "primitive":
            raise ValueError("primitive step requires an atomic field action")
        state_node, symbol_node = self.expression(state), self.expression(symbol)
        if state_node.sort != self.state_sort(
            action, side
        ) or symbol_node.sort != self.symbol_sort(action):
            raise ValueError("primitive step operands have incompatible sorts")
        if symbol_node.kind == "symbol":
            if state_node.kind == "literal":
                return self.literal(
                    action,
                    side,
                    self.primitive_tables.step(
                        action,
                        side,
                        state_node.value,
                        symbol_node.value,
                    ),
                )
            count = self._primitive_state_count(action, side)
            outputs = tuple(
                self.primitive_tables.step(action, side, value, symbol_node.value)
                for value in range(count)
            )
            # Preserve extensional identity before constructing a transition
            # node.  Padding symbols commonly induce the identity on one
            # directed boundary.  Missing this reduction makes a temporal
            # square retain an exponentially nested tower of semantically
            # inert continuation applications.
            if outputs == tuple(range(count)):
                return state
            if outputs and all(value == outputs[0] for value in outputs[1:]):
                return self.literal(action, side, outputs[0])
        return self._intern_expression(
            HigherExpression(
                "primitive-step",
                self.state_sort(action, side),
                (state.local_id, symbol.local_id),
                action=action,
                side=side,
            )
        )

    def primitive_emit(
        self,
        action: FieldCellActionID,
        left: HigherExpressionID,
        symbol: HigherExpressionID,
        right: HigherExpressionID,
    ) -> HigherExpressionID:
        if self.schema.kind(action) != "primitive":
            raise ValueError("primitive emit requires an atomic field action")
        left_node, symbol_node, right_node = (
            self.expression(left),
            self.expression(symbol),
            self.expression(right),
        )
        if (
            left_node.sort != self.state_sort(action, 0)
            or right_node.sort != self.state_sort(action, 1)
            or symbol_node.sort != self.symbol_sort(action)
        ):
            raise ValueError("primitive emit operands have incompatible sorts")
        if (
            left_node.kind == "literal"
            and symbol_node.kind == "symbol"
            and right_node.kind == "literal"
        ):
            return self.symbol(
                action,
                self.primitive_tables.emit(
                    action,
                    left_node.value,
                    symbol_node.value,
                    right_node.value,
                ),
            )
        return self._intern_expression(
            HigherExpression(
                "primitive-emit",
                self.symbol_sort(action),
                (left.local_id, symbol.local_id, right.local_id),
                action=action,
            )
        )

    def action_initial(
        self, action: FieldCellActionID, side: int
    ) -> HigherExpressionID:
        return self._intern_expression(
            HigherExpression(
                "action-initial",
                self.state_sort(action, side),
                action=action,
                side=side,
            )
        )

    def action_step(
        self,
        action: FieldCellActionID,
        side: int,
        state: HigherExpressionID,
        symbol: HigherExpressionID,
    ) -> HigherExpressionID:
        if self.expression(state).sort != self.state_sort(action, side):
            raise ValueError("higher action step state sort disagrees")
        self.expression(symbol)
        return self._intern_expression(
            HigherExpression(
                "action-step",
                self.state_sort(action, side),
                (state.local_id, symbol.local_id),
                action=action,
                side=side,
            )
        )

    def action_emit(
        self,
        action: FieldCellActionID,
        left: HigherExpressionID,
        symbol: HigherExpressionID,
        right: HigherExpressionID,
    ) -> HigherExpressionID:
        if self.expression(left).sort != self.state_sort(action, 0) or self.expression(
            right
        ).sort != self.state_sort(action, 1):
            raise ValueError("higher action emit boundary sorts disagree")
        self.expression(symbol)
        return self._intern_expression(
            HigherExpression(
                "action-emit",
                self.symbol_sort(action),
                (left.local_id, symbol.local_id, right.local_id),
                action=action,
            )
        )

    def bind_free(
        self,
        expression: HigherExpressionID,
        variable: HigherExpressionID,
        replacement: HigherExpressionID,
    ) -> HigherExpressionID:
        from number_compiler.hashlife.execution.continuations.substitution import (
            bind_free,
        )

        return bind_free(self, expression, variable, replacement)

    def bind_free_many(
        self,
        expression: HigherExpressionID,
        bindings: tuple[tuple[HigherExpressionID, HigherExpressionID], ...],
    ) -> HigherExpressionID:
        from number_compiler.hashlife.execution.continuations.substitution import (
            bind_free_many,
        )

        return bind_free_many(self, expression, bindings)

    def substitute(
        self,
        expression: HigherExpressionID,
        variable: HigherExpressionID,
        replacement: HigherExpressionID,
    ) -> HigherExpressionID:
        from number_compiler.hashlife.execution.continuations.substitution import (
            substitute,
        )

        return substitute(self, expression, variable, replacement)

    def evaluate(
        self,
        expression: HigherExpressionID,
        inputs: Mapping[HigherExpressionID, object] | None = None,
    ) -> object:
        from number_compiler.hashlife.execution.continuations.higher_evaluation import (
            evaluate_higher,
        )

        return evaluate_higher(self, expression, inputs)

    def metrics(self) -> HigherSemanticMetrics:
        return HigherSemanticMetrics(
            len(self._expressions),
            len(self._functions),
            self._expression_hits,
            self._function_hits,
            self._substitutions,
            self._evaluations,
            self._evaluation_workspace_peak,
        )


__all__ = [
    "FieldAtomSort",
    "FieldFunctionSort",
    "FieldStateSort",
    "FieldSymbolSort",
    "HigherActionSchema",
    "HigherExpression",
    "HigherExpressionID",
    "HigherFunction",
    "HigherFunctionID",
    "HigherSemanticArena",
    "HigherSemanticMetrics",
    "HigherSort",
]
