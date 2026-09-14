"""Jointly quotient nested outputs while preserving outer finite arguments."""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.physical_collatz_kernel import (
    PhysicalCollatzFourBlockEffect,
)
from number_compiler.arithmetic.functions.finite_function_types import FunctionSort
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.actions.lazy_compiler import UnsupportedInterfaceError
from number_compiler.hashlife.execution.continuations.diamond_expression_eval import (
    LowerFinite,
    ResolveExpr,
)
from number_compiler.hashlife.execution.continuations.diamond_higher_tasks import (
    HigherInitial,
    HigherStep,
)
from number_compiler.hashlife.execution.continuations.diamond_tasks import Result, Task
from number_compiler.hashlife.interfaces.semantic_expression_compiler import (
    SemanticExpressionCompiler,
)
from tests.support.diamond_continuation_reduction import literal, machine

if TYPE_CHECKING:
    from number_compiler.arithmetic.functions.finite_function_types import (
        SemanticFunctionID,
    )


def _inner_function(
    functions: SemanticFunctionArena,
    value: SemanticFunctionID,
) -> SemanticFunctionID:
    assert functions.resolve(value).signature.inputs == ()
    terminal = functions.evaluate(value, {})
    assert terminal.kind == "function"
    return functions.terminal_references(value, {})[0]


def test_actual_cubed_step_nested_continuation_evaluates_without_replay(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime, action = machine()
    arena = runtime.higher.expressions
    paired = runtime.actions.compose(action, action)
    cubed = runtime.actions.compose(action, paired)
    state = runtime.execute(HigherInitial(cubed, 0))
    for bit in (1, 0, 1):
        state = runtime.execute(HigherStep(cubed, 0, state, arena.symbol(cubed, bit)))
    outer = runtime.execute(ResolveExpr(arena.continuation(state)))
    kernel = runtime.kernel(action)
    expected = {}
    for x in range(kernel.right_count):
        body = runtime.execute(
            ResolveExpr(arena.apply(outer, literal(runtime, action, 1, x)))
        )
        anchor = runtime.execute(LowerFinite(arena.anchor(body)))
        inner = runtime.execute(ResolveExpr(arena.continuation(body)))
        expected[x] = (
            anchor,
            tuple(
                runtime.execute(
                    LowerFinite(arena.apply(inner, literal(runtime, action, 1, y)))
                )
                for y in range(kernel.right_count)
            ),
        )
    functions = SemanticFunctionArena(runtime.ledger)
    compiler = SemanticExpressionCompiler(runtime, functions)
    compiled = compiler.compile(outer)
    outer_function = _inner_function(functions, compiled.function)
    x_port = functions.resolve(outer_function).signature.inputs[0]

    def forbidden(*args: object, **kwargs: object) -> None:
        pytest.fail("semantic evaluation replayed an expression or primitive")

    monkeypatch.setattr(runtime, "execute", forbidden)
    monkeypatch.setattr(arena, "substitute", forbidden)
    monkeypatch.setattr(arena.closures, "expand", forbidden)
    monkeypatch.setattr(runtime.kernels, "evaluate", forbidden)
    for x in range(kernel.right_count):
        anchor_function, continuation = functions.terminal_references(
            outer_function, {x_port.variable: x}
        )
        inner_function = _inner_function(functions, continuation)
        y_port = functions.resolve(inner_function).signature.inputs[0]
        assert functions.evaluate(anchor_function, {}).value == expected[x][0]
        actual = tuple(
            functions.evaluate(inner_function, {y_port.variable: y}).value
            for y in range(kernel.right_count)
        )
        assert actual == expected[x][1]
    assert not hasattr(compiler, "results")


def test_different_zero_word_recipes_alias_with_outer_dependent_function_terminal() -> (
    None
):
    runtime, action = machine(PhysicalCollatzFourBlockEffect())
    arena = runtime.higher.expressions
    paired = runtime.actions.compose(action, action)
    x = arena.variable(arena.state_sort(action, 0), "outer")
    y = arena.variable(arena.state_sort(action, 1), "inner")
    bodies = []
    for count in (4, 8):
        reset = x
        for _ in range(count):
            reset = arena.primitive_advance(action, 0, reset, arena.symbol(action, 0))
        body = arena.pair(paired, 0, x, arena.lambda_(y, reset))
        bodies.append(arena.lambda_(x, body))
    assert bodies[0] != bodies[1]
    functions = SemanticFunctionArena(runtime.ledger)
    compiler = SemanticExpressionCompiler(runtime, functions)
    first, second = (compiler.compile(body) for body in bodies)
    assert first.function == second.function
    assert first.output_sort == second.output_sort


def test_free_outer_port_and_bound_inner_port_compile_jointly() -> None:
    runtime, action = machine()
    arena = runtime.higher.expressions
    x = arena.variable(arena.state_sort(action, 0), "free-x")
    y = arena.variable(arena.state_sort(action, 1), "bound-y")
    emitted = arena.primitive_emit(action, x, arena.symbol(action, 1), y)
    body = arena.primitive_advance(action, 0, x, emitted)
    function = arena.lambda_(y, body)
    compiler = SemanticExpressionCompiler(
        runtime, SemanticFunctionArena(runtime.ledger)
    )
    compiled = compiler.compile(function, (x,))
    kernel = runtime.kernel(action)
    for left in range(kernel.left_count):
        inner = compiler.functions.terminal_references(
            compiled.function, {compiled.ports[0].variable: left}
        )[0]
        port = compiler.functions.resolve(inner).signature.inputs[0]
        for right in range(kernel.right_count):
            expected = kernel.advance(
                BoundarySide.LEFT, left, kernel.emit(left, 1, right)
            )
            assert (
                compiler.functions.evaluate(inner, {port.variable: right}).value
                == expected
            )


def test_unsupported_composed_input_and_foreign_input_reject_without_mutation() -> None:
    runtime, action = machine()
    arena = runtime.higher.expressions
    paired = runtime.actions.compose(action, action)
    composed = arena.variable(arena.state_sort(paired, 0), "composed-input")
    compiler = SemanticExpressionCompiler(
        runtime, SemanticFunctionArena(runtime.ledger)
    )
    before = runtime.ledger.snapshot()
    with pytest.raises(UnsupportedInterfaceError, match="composed input"):
        compiler.compile(composed, (composed,))
    assert runtime.ledger.snapshot() == before
    foreign, foreign_action = machine()
    other = foreign.higher.expressions.variable(
        foreign.higher.expressions.state_sort(foreign_action, 0), "foreign"
    )
    with pytest.raises((ValueError, TypeError)):
        compiler.compile(other, (other,))
    assert runtime.ledger.snapshot() == before
    x = arena.variable(arena.state_sort(action, 0), "undeclared")
    before = runtime.ledger.snapshot()
    with pytest.raises(ValueError, match="undeclared"):
        compiler.compile(x)
    assert runtime.ledger.snapshot() == before


def test_existing_finite_map_is_lifted_with_invalid_codes_preserved() -> None:
    from tests.support.diamond_continuation_reduction import normalize

    runtime, action = machine()
    arena = runtime.higher.expressions
    x = arena.variable(arena.state_sort(action, 0), "finite-input")
    original = arena.lambda_(
        x, arena.primitive_advance(action, 0, x, arena.symbol(action, 1))
    )
    normalized = normalize(runtime, original)
    functions = SemanticFunctionArena(runtime.ledger)
    compiler = SemanticExpressionCompiler(runtime, functions)
    direct = compiler.compile(original)
    lifted = compiler.compile(normalized)
    assert direct.function == lifted.function
    function = _inner_function(functions, lifted.function)
    port = functions.resolve(function).signature.inputs[0]
    for code in range(port.cardinality, 1 << port.bits):
        assert functions.evaluate(function, {port.variable: code}).kind == "invalid"
    assert runtime.ledger.counters["semantic_expression_finite_lift_frames"] > 0


def test_finite_map_lift_is_canonical_and_its_binding_cache_is_evictable() -> None:
    from tests.support.diamond_continuation_reduction import normalize

    runtime, action = machine()
    arena = runtime.higher.expressions
    value = arena.variable(arena.state_sort(action, 0), "finite-cache-input")
    original = arena.lambda_(
        value,
        arena.primitive_advance(action, 0, value, arena.symbol(action, 1)),
    )
    normalized = normalize(runtime, original)
    compiler = SemanticExpressionCompiler(
        runtime,
        SemanticFunctionArena(runtime.ledger),
    )
    first = compiler.compile(normalized)
    evaluations = runtime.ledger.counters["semantic_expression_finite_lift_evaluations"]
    second = compiler.compile(normalized)
    assert second.function == first.function
    assert (
        runtime.ledger.counters["semantic_expression_finite_lift_evaluations"]
        == evaluations
    )
    assert runtime.ledger.counters["semantic_expression_finite_lift_hits"] > 0
    runtime.ledger.evict_query_memos()
    assert not compiler._finite_lifts
    rebuilt = compiler.compile(normalized)
    assert rebuilt.function == first.function
    assert (
        runtime.ledger.counters["semantic_expression_finite_lift_evaluations"]
        > evaluations
    )


def test_composed_lambda_input_is_rejected_before_semantic_publication() -> None:
    runtime, action = machine()
    arena = runtime.higher.expressions
    composed = runtime.actions.compose(action, action)
    argument = arena.variable(arena.state_sort(composed, 0), "whole-state")
    function = arena.lambda_(argument, argument)
    compiler = SemanticExpressionCompiler(
        runtime, SemanticFunctionArena(runtime.ledger)
    )
    before = runtime.ledger.snapshot()
    with pytest.raises(UnsupportedInterfaceError, match="composed input"):
        compiler.compile(function)
    assert runtime.ledger.snapshot() == before


def test_structured_production_nested_output_never_uses_scalar_product_or_curry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.functions.finite_function_types import (
        AtomSort,
        FunctionSignature,
    )

    runtime, action = machine()
    arena = runtime.higher.expressions
    paired = runtime.actions.compose(action, action)
    cubed = runtime.actions.compose(action, paired)
    state = runtime.execute(HigherInitial(cubed, 0))
    for bit in (1, 0, 1):
        state = runtime.execute(HigherStep(cubed, 0, state, arena.symbol(cubed, bit)))
    outer = runtime.execute(ResolveExpr(arena.continuation(state)))
    kernel = runtime.kernel(action)
    expected = {}
    for x in range(kernel.right_count):
        body = runtime.execute(
            ResolveExpr(arena.apply(outer, literal(runtime, action, 1, x)))
        )
        anchor = runtime.execute(LowerFinite(arena.anchor(body)))
        inner = runtime.execute(ResolveExpr(arena.continuation(body)))
        expected[x] = (
            anchor,
            tuple(
                runtime.execute(
                    LowerFinite(arena.apply(inner, literal(runtime, action, 1, y)))
                )
                for y in range(kernel.right_count)
            ),
        )
    functions = runtime.semantic_functions
    compiler = runtime.semantic_compiler

    def forbidden(*args: object, **kwargs: object) -> None:
        pytest.fail("factored structure used scalar enumeration or expression replay")

    monkeypatch.setattr(functions, "product", forbidden)
    monkeypatch.setattr(functions, "curry", forbidden)
    monkeypatch.setattr(functions, "variable", forbidden)
    monkeypatch.setattr(compiler, "_program", forbidden)
    compiled = compiler.compile_structured(outer)
    structures = compiler.structures
    assert structures is not None
    assert len(structures.nodes) < 100
    outer_sort = structures.resolve(compiled.structure).signature.output
    assert isinstance(outer_sort, FunctionSort)
    x_port = outer_sort.inputs[0]
    monkeypatch.setattr(runtime, "execute", forbidden)
    monkeypatch.setattr(arena, "substitute", forbidden)
    monkeypatch.setattr(arena.closures, "expand", forbidden)
    monkeypatch.setattr(runtime.kernels, "evaluate", forbidden)
    for x in range(kernel.right_count):
        x_value = structures.bits.constant(
            FunctionSignature((), AtomSort("x", x_port.cardinality)), x
        )
        body_structure = structures.apply(
            compiled.structure, {x_port.variable: x_value}
        )
        anchor_structure = structures.component(body_structure, 0)
        continuation = structures.component(body_structure, 1)
        assert structures.evaluate_atom(anchor_structure, {}) == expected[x][0]
        inner_sort = structures.resolve(continuation).signature.output
        assert isinstance(inner_sort, FunctionSort)
        y_port = inner_sort.inputs[0]
        for y in range(kernel.right_count):
            y_value = structures.bits.constant(
                FunctionSignature((), AtomSort("y", y_port.cardinality)), y
            )
            observed = structures.apply(continuation, {y_port.variable: y_value})
            assert structures.evaluate_atom(observed, {}) == expected[x][1][y]


def test_structured_zero_word_alias_preserves_joint_outer_dependency(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime, action = machine(PhysicalCollatzFourBlockEffect())
    arena = runtime.higher.expressions
    paired = runtime.actions.compose(action, action)
    x = arena.variable(arena.state_sort(action, 0), "outer")
    y = arena.variable(arena.state_sort(action, 1), "inner")
    expressions = []
    for count in (4, 8):
        value = x
        for _ in range(count):
            value = arena.primitive_advance(action, 0, value, arena.symbol(action, 0))
        expressions.append(
            arena.lambda_(x, arena.pair(paired, 0, x, arena.lambda_(y, value)))
        )
    assert expressions[0] != expressions[1]
    functions = runtime.semantic_functions
    compiler = runtime.semantic_compiler

    def forbidden(*args: object, **kwargs: object) -> None:
        pytest.fail("structured output entered scalar terminal expansion")

    monkeypatch.setattr(functions, "product", forbidden)
    monkeypatch.setattr(functions, "curry", forbidden)
    first, second = (
        compiler.compile_structured(expression) for expression in expressions
    )
    assert first.structure == second.structure
    assert first.output_sort == second.output_sort


def test_structured_rejects_foreign_and_higher_composed_inputs_before_allocating_arena() -> (
    None
):
    runtime, action = machine()
    arena = runtime.higher.expressions
    composed = runtime.actions.compose(action, action)
    composed = runtime.actions.compose(composed, composed)
    parameter = arena.variable(arena.state_sort(composed, 0), "unsupported")
    compiler = runtime.semantic_compiler
    before = runtime.ledger.snapshot()
    with pytest.raises(UnsupportedInterfaceError, match="composed function domain"):
        compiler.compile_structured(parameter, (parameter,))
    assert compiler.structures is None
    assert runtime.ledger.snapshot() == before
    foreign, foreign_action = machine()
    parameter = foreign.higher.expressions.variable(
        foreign.higher.expressions.state_sort(foreign_action, 0), "foreign"
    )
    with pytest.raises((ValueError, TypeError)):
        compiler.compile_structured(parameter, (parameter,))
    assert runtime.ledger.snapshot() == before


def test_structured_task_yields_resolution_without_nested_execution(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.hashlife.interfaces.semantic_expression_tasks import (
        CompileStructuredExpression,
        StructuredExpressionTask,
    )

    runtime, action = machine()
    arena = runtime.higher.expressions
    x = arena.variable(arena.state_sort(action, 0), "closure-input")
    body = arena.primitive_advance(action, 0, x, arena.symbol(action, 1))
    closure = arena.closures.intern((x,), body)
    call = arena.call(closure, (x,))
    assert arena.node(call).kind == "call"
    compiler = runtime.semantic_compiler

    def forbidden(*args: object, **kwargs: object) -> None:
        pytest.fail("construction generator called the runtime recursively")

    monkeypatch.setattr(runtime, "execute", forbidden)
    entry = compiler.program(CompileStructuredExpression(call, (x,)))
    child = next(entry)
    assert type(child) is StructuredExpressionTask
    child_program = compiler.program(child)
    dependency = next(child_program)
    assert type(dependency) is ResolveExpr and dependency.expression == call
    entry.close()
    child_program.close()


def test_structured_wrapper_uses_one_runtime_entry_and_keeps_no_result_memo(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.hashlife.interfaces.semantic_expression_tasks import (
        CompileStructuredExpression,
    )

    runtime, action = machine()
    arena = runtime.higher.expressions
    x = arena.variable(arena.state_sort(action, 0), "single-entry")
    body = arena.primitive_advance(action, 0, x, arena.symbol(action, 1))
    call = arena.call(arena.closures.intern((x,), body), (x,))
    execute = runtime.execute
    active = False
    entries = []

    def guarded(task: Task) -> Result:
        nonlocal active
        assert not active, "nested scheduler execution"
        active = True
        entries.append(task)
        try:
            return execute(task)
        finally:
            active = False

    monkeypatch.setattr(runtime, "execute", guarded)
    compiled = runtime.semantic_compiler.compile_structured(call, (x,))
    assert len(entries) == 1 and type(entries[0]) is CompileStructuredExpression
    assert runtime.semantic_compiler.probe_task(entries[0]) is None
    assert runtime.semantic_compiler.structures is not None
    assert (
        runtime.semantic_compiler.structures.resolve(compiled.structure).kind == "atom"
    )
    for memo in (
        runtime.initials,
        runtime.transfers,
        runtime.substitutions,
        runtime.continuations,
        runtime.expression_heads,
    ):
        assert entries[0] not in memo


def test_structured_task_environment_and_publication_validate_before_mutation() -> None:
    from number_compiler.arithmetic.functions.finite_function_types import FinitePort
    from number_compiler.hashlife.interfaces.semantic_expression_tasks import (
        CompileStructuredExpression,
        StructuredExpressionTask,
    )

    runtime, action = machine()
    arena = runtime.higher.expressions
    x = arena.variable(arena.state_sort(action, 0), "valid-input")
    compiler = runtime.semantic_compiler
    record = compiler.compile_structured(x, (x,))
    request = CompileStructuredExpression(x, (x,))
    port = record.ports[0]
    before = runtime.ledger.snapshot()
    bad = (
        StructuredExpressionTask(x, ((x, port),), True),
        StructuredExpressionTask(x, ((x, port),), -1),
        StructuredExpressionTask(x, ((x, port), (x, port)), 0),
        StructuredExpressionTask(
            x, ((x, FinitePort(port.variable, port.cardinality + 1)),), 0
        ),
    )
    for task in bad:
        with pytest.raises((TypeError, ValueError)):
            compiler.probe_task(task)
        assert runtime.ledger.snapshot() == before
    foreign, foreign_action = machine()
    other_x = foreign.higher.expressions.variable(
        foreign.higher.expressions.state_sort(foreign_action, 0), "other"
    )
    other_result = foreign.semantic_compiler.compile_structured(other_x, (other_x,))
    with pytest.raises(ValueError):
        compiler.publication(request, other_result.structure)
    assert runtime.ledger.snapshot() == before


def test_standalone_compiler_cannot_hijack_runtime_structured_owner() -> None:
    runtime, action = machine()
    arena = runtime.higher.expressions
    x = arena.variable(arena.state_sort(action, 0), "input")
    standalone = SemanticExpressionCompiler(
        runtime, SemanticFunctionArena(runtime.ledger)
    )
    before = runtime.ledger.snapshot()
    with pytest.raises(ValueError, match="runtime-owned"):
        standalone.compile_structured(x, (x,))
    assert runtime.ledger.snapshot() == before
