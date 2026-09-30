"""A complete function can encode a captured future tape in its constants."""

from __future__ import annotations

from random import Random
from typing import TYPE_CHECKING, Never

import pytest

from devtools.verification.parametric_query import parametric_point
from number_compiler.hashlife.execution.continuations.diamond_expression_eval import (
    ResolveExpr,
)
from number_compiler.hashlife.execution.diamond_continuation_guard import (
    function_program_admission,
)
from number_compiler.hashlife.execution.diamond_continuation_reduction import (
    CompilePrimitiveFunction,
    NormalizePrimitiveLambda,
)
from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
    ExprSubstitutionKey,
)
from tests.support.assertions import assert_rejected_atomically
from tests.support.diamond_observation_adversarial import neighbor_xor
from tests.support.diamond_query import build, oracle
from tests.support.diamond_quotient import (
    capture_root_emissions,
    warmed_neighbor_application,
)

if TYPE_CHECKING:
    pass


@pytest.mark.parametrize("argument_matters", (False, True))
@pytest.mark.validation  # Complete 24-coordinate captured-future adversary.
def test_fake_free_port_cannot_cache_a_complete_future_tape(
    argument_matters: bool, monkeypatch: pytest.MonkeyPatch
) -> None:
    rng = Random(765)
    source = tuple(rng.randrange(2) for _ in range(24))
    app = build(neighbor_xor(), source, 32, 4)
    runtime, arena = app.runtime, app.runtime.higher.expressions
    outputs = capture_root_emissions(app, monkeypatch)
    expected = oracle(neighbor_xor(), source, 32, 4)
    for position in range(24):
        assert parametric_point(runtime, app.root, position) == expected[position]
    intermediate = oracle(neighbor_xor(), source, 32, 3)
    requests: list[CompilePrimitiveFunction] = []
    normalized_requests: list[NormalizePrimitiveLambda] = []
    head_requests: list[ResolveExpr] = []
    substitutions: list[ExprSubstitutionKey] = []
    recovered = []
    for output in outputs:
        node = arena.node(output)
        assert node.kind == "emit" and node.action is not None
        action = node.action
        symbol = arena._handle(node.children[1])
        variable = arena.variable(arena.state_sort(action, 1), "adversarial-free-port")
        if argument_matters:
            left = arena.literal(runtime.boundaries.literal(action, 0, 0))
            symbol = arena.primitive_emit(action, left, symbol, variable)
        body = arena.primitive_advance(action, 1, variable, symbol)
        assert not function_program_admission(arena, body)[0]
        request = CompilePrimitiveFunction(variable, body)
        result = runtime.execute(request)
        # Zero argument recovers the captured T^3 symbol, even in the genuinely
        # nonconstant XOR function variant. Complete functionality is no defense.
        from number_compiler.hashlife.execution.continuations.diamond_context_program import (
            RIGHT_A,
        )
        from number_compiler.hashlife.interfaces.diamond_kernel_bridge import (
            substitution_bindings,
        )

        bindings = substitution_bindings(
            runtime.kernels, 4, RIGHT_A, runtime.kernels.constant(4, 0)
        )
        recovered.append(
            runtime.kernels.evaluate(runtime.kernels.substitute(result, bindings), {})
        )
        if argument_matters:
            one = substitution_bindings(
                runtime.kernels, 4, RIGHT_A, runtime.kernels.constant(4, 1)
            )
            assert (
                runtime.kernels.evaluate(runtime.kernels.substitute(result, one), {})
                == 1 - recovered[-1]
            )
        if not requests:
            closure = arena.closures.intern((variable,), body)
            opaque = arena.call(closure, (variable,))
            assert not function_program_admission(arena, opaque)[0]
        requests.append(request)
        normalization = NormalizePrimitiveLambda(arena.lambda_(variable, body))
        runtime.execute(normalization)
        normalized_requests.append(normalization)
        if argument_matters:
            from number_compiler.hashlife.execution.continuations.diamond_expression_eval import (
                ResolveExpr,
            )

            anchor = arena.variable(arena.state_sort(action, 0), "opaque-anchor")
            captured = arena._handle(node.children[1])
            mixed = arena.primitive_emit(action, anchor, captured, variable)
            open_body = arena.primitive_advance(action, 1, variable, mixed)
            program = arena.closures.intern(
                (anchor,), arena.lambda_(variable, open_body)
            )
            opaque_function = arena.call(
                program, (arena.literal(runtime.boundaries.literal(action, 0, 0)),)
            )
            application = arena.apply(opaque_function, variable)
            head_request = ResolveExpr(application)
            head = runtime.execute(head_request)
            assert arena.node(head).kind == "finite_map"
            head_requests.append(head_request)
            from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
                ExprBinding,
                ExprSubstitutionKey,
            )

            mapped = arena.finite_map(
                arena.state_sort(action, 1),
                arena.state_sort(action, 1),
                result,
                variable,
            )
            boundary = arena.literal(runtime.boundaries.literal(action, 1, 3))
            bound = arena.primitive_advance(action, 1, boundary, captured)
            opposite = arena.variable(arena.state_sort(action, 0), "unused-opposite")
            whole = runtime.actions.compose(action, action)
            incoming = arena.pair(whole, 1, mapped, arena.lambda_(opposite, bound))
            parameter = arena.variable(arena.state_sort(whole, 1), "whole-projection")
            projection = arena.anchor(parameter)
            key = ExprSubstitutionKey(projection, (ExprBinding(parameter, incoming),))
            assert (
                not arena.node(incoming).binding_safe
                and arena.node(mapped).binding_safe
            )
            assert arena.substitute(projection, {parameter: incoming}) == mapped
            substitutions.append(key)
    assert recovered == intermediate[:24]
    assert len(set(requests)) == 24
    assert not any(
        request in runtime.primitive_continuations.maps for request in requests
    )
    assert not any(
        request in runtime.primitive_continuations.normalized
        for request in normalized_requests
    )
    assert not any(request in runtime.expression_heads for request in head_requests)
    assert not any(request in arena.memo for request in substitutions)


def test_actual_reset_function_from_kernel_symbols_remains_memoizable() -> None:
    app = warmed_neighbor_application()
    runtime, arena = app.runtime, app.runtime.higher.expressions
    variable = arena.variable(arena.state_sort(app.root, 1), "actual-carry-input")
    body = arena.primitive_advance(app.root, 1, variable, arena.symbol(app.root, 1))
    assert function_program_admission(arena, body)[0]
    task = CompilePrimitiveFunction(variable, body)
    first = runtime.execute(task)
    assert runtime.primitive_continuations.maps[task] == first
    assert runtime.execute(task) == first
    assert runtime.kernels.evaluate(first, {}) == 1


@pytest.mark.parametrize("warm", (False, True))
def test_foreign_complete_function_cannot_enter_warm_or_cold_binding(
    warm: bool,
) -> None:
    app = build(neighbor_xor(), (0, 1), 4, 1)
    other = build(neighbor_xor(), (0, 1), 4, 1)
    runtime, arena = app.runtime, app.runtime.higher.expressions
    runtime.kernels.intern(runtime.actions.primitive(app.root))
    variable = arena.variable(arena.state_sort(app.root, 1), "declared-port")
    body = arena.primitive_advance(app.root, 1, variable, arena.symbol(app.root, 1))
    request = CompilePrimitiveFunction(variable, body)
    if warm:
        runtime.execute(request)
    foreign = other.runtime.kernels.constant(4, 1)
    assert_rejected_atomically(
        runtime.ledger,
        lambda: runtime.primitive_continuations.publish(request, foreign),
        ValueError,
    )


def test_binding_proof_metadata_equals_independent_full_graph_walk(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    app = build(neighbor_xor(), (0, 1, 1, 0), 8, 4)
    runtime, arena = app.runtime, app.runtime.higher.expressions
    for position in range(4):
        parametric_point(runtime, app.root, position)
    # Child and closure body IDs precede their parents. Derive the admission
    # proof independently without reading the stored flags of any dependency.
    expected: list[bool] = []
    for node in arena.nodes:
        safe = bool(
            node.free_ports
            or node.scope
            or node.kind in ("literal", "symbol", "port", "bound", "lambda", "pair")
        )
        safe |= (
            node.kind in ("finite_apply", "finite_map")
            and len(node.children) == 1
            and arena.nodes[node.children[0]].kind == "literal"
        )
        safe &= all(expected[child] for child in node.children)
        if node.kind == "call":
            assert node.closure is not None
            safe &= expected[arena.closures.resolve(node.closure).body.local_id]
        expected.append(safe)
        assert type(node.binding_safe) is bool and node.binding_safe == safe
    assert any(expected) and not all(expected)


def test_warm_binding_proof_never_reopens_opaque_child_program(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    app = warmed_neighbor_application()
    runtime, arena = app.runtime, app.runtime.higher.expressions
    variable = arena.variable(arena.state_sort(app.root, 1), "warm-declared-port")
    body = arena.primitive_advance(app.root, 1, variable, arena.symbol(app.root, 1))
    closure = arena.closures.intern((variable,), body)
    opaque = arena.call(closure, (variable,))
    task = CompilePrimitiveFunction(variable, opaque)
    first = runtime.execute(task)

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("warm proof replayed the opaque function body")

    monkeypatch.setattr(arena.closures, "resolve", forbidden)
    monkeypatch.setattr(arena.unary, "mapped", forbidden)
    assert function_program_admission(arena, opaque) == (True, 1, 1)
    assert runtime.execute(task) == first
