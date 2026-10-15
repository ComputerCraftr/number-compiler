"""Store-free structured compilation operations."""

from __future__ import annotations

from collections.abc import Generator
from typing import TYPE_CHECKING

from number_compiler.arithmetic.functions.finite_function_types import (
    AtomSort,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_function_types import (
    FunctionSort as SemanticFunctionSort,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.actions.lazy_compiler import UnsupportedInterfaceError
from number_compiler.hashlife.execution.continuations.diamond_expression_eval import (
    ResolveExpr,
)
from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
    ExprID,
    FunctionSort,
    StateSort,
)
from number_compiler.hashlife.interfaces.semantic_bit_transforms import (
    primitive_operation,
)
from number_compiler.hashlife.interfaces.semantic_bits import (
    FactoredFunctionID,
    _Circuit,
)
from number_compiler.hashlife.interfaces.semantic_expression_tasks import (
    StructuredExpressionTask,
)
from number_compiler.hashlife.interfaces.semantic_reachable_profile import (
    ReachableCodec,
    SemanticProfileID,
)
from number_compiler.hashlife.interfaces.semantic_state_codec import (
    StateCodec,
    describe_state,
)
from number_compiler.hashlife.interfaces.semantic_structures import (
    StructureArena,
    StructuredNode,
    StructureID,
    _Builder,
)
from number_compiler.resources.metric_keys import (
    hashlife_interfaces as _interfaces_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.diamond_tasks import (
        Result,
        Task,
    )
    from number_compiler.hashlife.interfaces.semantic_expression_compiler import (
        SemanticExpressionCompiler,
    )


def _structured_program(
    self: SemanticExpressionCompiler,
    task: StructuredExpressionTask,
    structures: StructureArena,
) -> Generator[Task, Result, Result]:
    arena, bits = self.expressions, structures.bits
    node = arena.node(task.expression)
    inputs = self._environment_ports(task.environment)
    if node.kind in ("call", "anchor", "continuation", "apply"):
        # Expose only the requested constructor before compiling children.
        # In particular, projecting a closure's anchor must not compile its
        # unused continuation, and constant application must not compile its
        # discarded argument. Unknown formal projections remain symbolic.
        head = yield ResolveExpr(task.expression)
        if type(head) is not ExprID:
            raise UnsupportedInterfaceError(
                "structured expression has no constructor head"
            )
        if head != task.expression:
            self.ledger.bump(_interfaces_keys.SEMANTIC_EXPRESSION_HEAD_ELISIONS)
            return (
                yield StructuredExpressionTask(
                    head, task.environment, task.depth, task.profile
                )
            )
        if node.kind == "call":
            raise UnsupportedInterfaceError(
                "structured expression has no constructor head"
            )
    if node.kind == "port":
        binding = dict(task.environment).get(task.expression)
        if binding is None:
            raise ValueError("unbound structured semantic port")
        if isinstance(binding, FinitePort):
            return structures.atom(
                bits.variable(inputs, binding, self._atom_sort(node.sort))
            )
        if isinstance(binding, ReachableCodec):
            if self.profiles is None:
                raise AssertionError("reachable binding has no profile arena")
            return self._declare_structure(
                self.profiles.decode(binding, structures), inputs, structures
            )
        return self._declare_structure(binding.structure, inputs, structures)
    if node.kind in ("literal", "symbol"):
        return structures.atom(
            bits.constant(
                FunctionSignature(inputs, self._atom_sort(node.sort)), node.value
            )
        )
    if node.kind == "lambda":
        assert isinstance(node.sort, FunctionSort)
        variable = arena.fresh_variable(
            node.sort.domain,
            "semantic-bound-input",
            (task.expression,) + tuple(item[0] for item in task.environment),
        )
        binding = self._binding(
            variable,
            PortVariable(0, 0, f"semantic-lambda-{task.depth:08}", 0),
            task.profile,
        )
        body = arena.apply(task.expression, variable)
        function = yield StructuredExpressionTask(
            body,
            task.environment + ((variable, binding),),
            task.depth + 1,
            task.profile,
        )
        if type(function) is not StructureID:
            raise AssertionError("structured child returned a different result")
        curried = structures.curry(
            function,
            (binding,) if isinstance(binding, FinitePort) else binding.ports,
        )
        curried_node = structures.resolve(curried)
        assert type(curried_node.signature.output) is SemanticFunctionSort
        declarations = self._input_ports(
            node.sort.domain,
            PortVariable(0, 0, "semantic-argument", 0),
            task.profile,
        )
        signature = FunctionSignature(
            curried_node.signature.inputs,
            SemanticFunctionSort(declarations, curried_node.signature.output.output),
        )
        builder = _Builder(structures)
        return builder.finish(
            builder.intern(
                StructuredNode(
                    signature,
                    "function",
                    curried_node.valid,
                    body=curried_node.body,
                    bound=curried_node.bound,
                )
            )
        )
    if node.kind in ("anchor", "continuation"):
        projected_source = arena._handle(node.children[0])
        binding = dict(task.environment).get(projected_source)
        if isinstance(binding, ReachableCodec):
            if self.profiles is None:
                raise AssertionError("reachable binding has no profile arena")
            projected = self.profiles.component(
                binding, 0 if node.kind == "anchor" else 1, structures
            )
            return self._declare_structure(projected, inputs, structures)
        if isinstance(binding, StateCodec):
            projected = structures.component(
                binding.structure, 0 if node.kind == "anchor" else 1
            )
            return self._declare_structure(projected, inputs, structures)
    children: list[StructureID] = []
    for child_index in node.children:
        child_result = yield StructuredExpressionTask(
            arena._handle(child_index), task.environment, task.depth, task.profile
        )
        if type(child_result) is not StructureID:
            raise AssertionError("structured child returned a different result")
        children.append(child_result)
    if node.kind in ("anchor", "continuation"):
        return structures.component(children[0], 0 if node.kind == "anchor" else 1)
    if node.kind == "pair":
        return structures.product(tuple(children))
    if node.kind == "apply":
        target = structures.resolve(children[0]).signature.output
        original = arena.node(arena._handle(node.children[0])).sort
        if not isinstance(target, SemanticFunctionSort) or not isinstance(
            original, FunctionSort
        ):
            raise UnsupportedInterfaceError(
                "application requires a typed semantic function"
            )
        encoded = self._encode_argument(
            original.domain, target.inputs, children[1], structures, task.profile
        )
        return structures.apply(children[0], encoded)
    arguments = []
    for child in children:
        value = structures.resolve(child).atom
        if value is None:
            raise UnsupportedInterfaceError(
                "primitive operation received structured input"
            )
        arguments.append(value)
    if node.kind in ("finite_apply", "finite_map"):
        mapped, port = self._finite_child(node)
        return structures.atom(
            bits.substitute(self._factored(mapped, bits), {port.variable: arguments[0]})
        )
    if node.kind in ("advance", "emit") and node.action is not None:
        primitive = self.primitives.compile(self.runtime.actions.primitive(node.action))
        zero_left = bits.constant(FunctionSignature(inputs, primitive.left_sort), 0)
        zero_right = bits.constant(FunctionSignature(inputs, primitive.right_sort), 0)
        primitive_function, actual = primitive_operation(
            primitive, node.kind, node.side, tuple(arguments), zero_left, zero_right
        )
        scalar = bits.substitute(
            self._factored(primitive_function, bits),
            dict(zip((port.variable for port in primitive.ports), actual, strict=True)),
        )
        return structures.atom(scalar)
    raise UnsupportedInterfaceError(f"unsupported structured constructor: {node.kind}")


def _encode_argument(
    self: SemanticExpressionCompiler,
    sort: StateSort,
    ports: tuple[FinitePort, ...],
    argument: StructureID,
    structures: StructureArena,
    profile: SemanticProfileID | None = None,
) -> dict[PortVariable, FactoredFunctionID]:
    bits = structures.bits
    if self.expressions.primitive(sort.action) is not None:
        atom = structures.resolve(argument).atom
        if atom is None or len(ports) != 1:
            raise ValueError("primitive application requires one numeric argument")
        return {ports[0].variable: atom}
    if profile is not None:
        self._profile(profile)
        raise UnsupportedInterfaceError(
            "reachable application requires certified ordinal transport"
        )
    spec = describe_state(self.runtime, sort.action, sort.side)
    anchor = structures.resolve(structures.component(argument, 0)).atom
    continuation = structures.component(argument, 1)
    function = structures.resolve(continuation).signature.output
    if (
        anchor is None
        or type(function) is not SemanticFunctionSort
        or len(function.inputs) != 1
    ):
        raise ValueError(
            "paired application requires an anchor and primitive continuation"
        )
    values = [anchor]
    for ordinal in range(spec.opposite_cardinality):
        value = bits.constant(
            FunctionSignature(
                (), AtomSort("codec-original-argument", spec.opposite_cardinality)
            ),
            ordinal,
        )
        selected = structures.apply(continuation, {function.inputs[0].variable: value})
        atom = structures.resolve(selected).atom
        if atom is None:
            raise ValueError("paired codec continuation must return a primitive state")
        values.append(atom)
    if len(values) != len(ports):
        raise ValueError("paired application has another flat input interface")
    result = {}
    for port, value in zip(ports, values):
        node = bits.resolve(value)
        circuit = _Circuit(self.functions, node.signature.inputs)
        roots, valid = circuit.imported(node)
        pending = circuit.normalized(
            FunctionSignature(
                node.signature.inputs, AtomSort("codec-storage", port.cardinality)
            ),
            roots,
            valid,
        )
        result[port.variable] = bits._publish(circuit, (pending,))[0]
    return result
