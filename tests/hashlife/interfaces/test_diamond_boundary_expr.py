import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
    BoundaryExpressionArena,
    ExprID,
    FunctionSort,
    StateSort,
)
from number_compiler.hashlife.interfaces.expression_transactions import (
    ExpressionTransaction as _canonicalExpressionTransaction,
)
from number_compiler.resources.ledger import ResourceLedger
from tests.support.assertions import assert_rejected_atomically
from tests.support.diamond_boundary_expr import context


def test_pair_projection_and_eta_are_reduced_before_publication() -> None:
    ledger, actions, _, arena, first, second = context()
    action = actions.compose(first, second)
    pair_sort = arena.state_sort(action, 0)
    source = arena.variable(pair_sort, "whole-port")
    anchor, continuation = arena.anchor(source), arena.continuation(source)
    before = ledger.snapshot()
    assert arena.pair(action, 0, anchor, continuation) == source
    assert ledger.entries == before.entries
    literal_anchor = arena.variable(StateSort(first, 0), "anchor")
    replacement = arena.pair(action, 0, literal_anchor, continuation)
    before = ledger.snapshot()
    assert arena.anchor(replacement) == literal_anchor
    assert arena.continuation(replacement) == continuation
    assert ledger.entries == before.entries


def test_lambda_is_alpha_canonical_beta_and_eta_reduce_without_capture() -> None:
    ledger, _, boundaries, arena, first, _ = context()
    sort = arena.state_sort(first, 0)
    x, y, z = (arena.variable(sort, name) for name in ("x", "y", "z"))
    identity = arena.lambda_(x, x)
    before = ledger.snapshot()
    assert arena.lambda_(y, y) == identity
    assert ledger.entries == before.entries
    assert arena.apply(identity, z) == z
    function = arena.variable(FunctionSort(sort, sort), "function")
    before = ledger.snapshot()
    assert arena.lambda_(x, arena.apply(function, x)) == function
    assert (
        ledger.nodes <= before.nodes + 1
    )  # public application is its own requested expression
    constant = arena.lambda_(x, y)
    zero = arena.literal(boundaries.literal(first, 0, 0))
    # Substitution y->x keeps x free even though x originally named the binder.
    changed = arena.substitute(constant, {y: x})
    assert arena.apply(changed, zero) == x
    assert arena.apply(constant, zero) == y
    assert arena.substitute(x, {x: y, y: z}) == y  # simultaneous


def test_nested_lambdas_in_structured_ports_preserve_de_bruijn_depth() -> None:
    _, actions, _, arena, first, _ = context()
    composed = actions.compose(first, first)
    left = arena.state_sort(first, 0)
    right = arena.state_sort(first, 1)
    x, y = arena.variable(left, "outer-x"), arena.variable(right, "inner-y")
    # The outer variable occurs beneath an inner continuation binder.
    nested = arena.lambda_(x, arena.pair(composed, 0, x, arena.lambda_(y, x)))
    free = arena.variable(left, "free")
    result = arena.apply(nested, free)
    assert arena.anchor(result) == free
    assert arena.apply(arena.continuation(result), y) == free
    # A function replacement creates a beta redex below both binders.
    function = arena.variable(FunctionSort(left, left), "nested-function")
    parameterized = arena.lambda_(
        x, arena.pair(composed, 0, x, arena.lambda_(y, arena.apply(function, x)))
    )
    reduced = arena.substitute(parameterized, {function: arena.lambda_(x, x)})
    assert reduced == nested
    closed = arena.node(nested)
    assert closed.scope == 0
    open_nodes = [i for i, node in enumerate(arena.nodes) if node.scope]
    assert open_nodes
    for index in open_nodes:
        with pytest.raises(ValueError, match="escape"):
            arena.node(ExprID(arena.token, "diamond-boundary-expression", index))


def test_wrong_scopes_sorts_and_foreign_values_fail_before_warm_shortcuts() -> None:
    ledger, arena, first, foreign, foreign_action, sort = _foreign_state_fixture()
    x, y = arena.variable(sort, "x"), arena.variable(sort, "y")
    arena.substitute(x, {x: y})
    other = foreign.variable(foreign.state_sort(foreign_action, 0), "x")
    wrong_side = arena.variable(arena.state_sort(first, 1), "right")
    before = ledger.snapshot()
    for replacement in (
        other,
        wrong_side,
        ExprID(arena.token, "diamond-boundary-expression", len(arena.nodes)),
    ):
        with pytest.raises(ValueError):
            arena.substitute(x, {x: replacement})
    with pytest.raises(ValueError):
        arena.variable(StateSort(foreign_action, 0), "foreign")
    with pytest.raises(ValueError):
        arena.variable(StateSort(first, True), "boolean-side")
    assert ledger.snapshot() == before


def test_substitution_transaction_reserves_final_program_and_memo_together() -> None:
    ledger, _, _, arena, first, _ = context()
    sort = arena.state_sort(first, 0)
    x, y = arena.variable(sort, "x"), arena.variable(sort, "y")
    symbol = arena.variable(arena.symbol_sort(first), "original-symbol")
    expression = arena.primitive_advance(first, 0, x, symbol)
    before = ledger.snapshot()
    ledger.max_cache_entries = before.entries + 2  # result node+key fit; memo does not
    with pytest.raises(BlockContextBudgetExceeded):
        arena.substitute(expression, {x: y})
    after = ledger.snapshot()
    assert (
        after.entries,
        after.nodes,
        after.peak_entries,
        after.peak_nodes,
        after.inventory,
    ) == (
        before.entries,
        before.nodes,
        before.peak_entries,
        before.peak_nodes,
        before.inventory,
    )
    assert not arena.memo
    ledger.max_cache_entries = None
    result = arena.substitute(expression, {x: y})
    assert result == arena.primitive_advance(first, 0, y, symbol)
    nodes = len(arena.nodes)
    assert arena.substitute(expression, {x: y, y: y}) == result
    ledger.evict_query_memos()
    assert not arena.memo
    assert arena.substitute(expression, {x: y}) == result
    assert len(arena.nodes) == nodes


def test_primitive_nodes_retain_complete_symbolic_dependencies() -> None:
    _, _, _, arena, first, _ = context()
    left = arena.variable(arena.state_sort(first, 0), "left")
    right = arena.variable(arena.state_sort(first, 1), "right")
    symbol = arena.variable(arena.symbol_sort(first), "original-symbol")
    output = arena.primitive_emit(first, left, symbol, right)
    node = arena.node(output)
    assert node.kind == "emit"
    assert node.children == (left.local_id, symbol.local_id, right.local_id)
    assert node.action == first
    assert node.value == -1
    assert node.state is None


def test_constant_function_probe_does_not_schedule_or_read_an_argument() -> None:
    ledger, actions, _, arena, first, _ = context()
    state = arena.state_sort(first, 0)
    x, y = arena.variable(state, "x"), arena.variable(state, "y")
    function = arena.lambda_(x, y)
    dependent = arena.lambda_(x, x)
    before = ledger.snapshot()
    assert arena.constant_function(function) == y
    assert arena.constant_function(dependent) is None
    assert arena.symbol_sort(actions.identity) == arena.symbol_sort(first)
    assert ledger.snapshot() == before


def test_fresh_binder_avoids_incoming_free_port_and_alpha_normalizes() -> None:
    ledger, _, _, arena, first, _ = context()
    sort = arena.state_sort(first, 0)
    incoming = arena.variable(sort, "higher-step-opposite")
    binder = arena.fresh_variable(sort, "higher-step-opposite", (incoming,))
    assert binder != incoming
    constant = arena.lambda_(binder, incoming)
    assert arena.constant_function(constant) == incoming
    before = ledger.snapshot()
    assert arena.fresh_variable(sort, "higher-step-opposite", (incoming,)) == binder
    assert ledger.entries == before.entries
    other = arena.variable(sort, "different-bound-name")
    assert arena.lambda_(other, incoming) == constant


def test_closed_primitive_cofactors_fold_to_universal_finite_literals() -> None:
    ledger, _, boundaries, arena, first, _ = context()
    from number_compiler.arithmetic.contracts.block_effect import BoundarySide

    primitive = arena.primitive(first)
    assert primitive is not None
    left = arena.literal(boundaries.literal(first, 0, 0))
    right = arena.literal(boundaries.literal(first, 1, 0))
    symbol = arena.symbol(first, 2)
    expected_state = primitive.advance(BoundarySide.LEFT, 0, 2)
    expected_symbol = primitive.emit(0, 2, 0)
    stepped = arena.primitive_advance(first, 0, left, symbol)
    emitted = arena.primitive_emit(first, left, symbol, right)
    assert (arena.node(stepped).kind, arena.node(stepped).value) == (
        "literal",
        expected_state,
    )
    assert (arena.node(emitted).kind, arena.node(emitted).value) == (
        "symbol",
        expected_symbol,
    )
    assert all(
        arena.node(expression).state is None for expression in (left, right, stepped)
    )
    port = arena.variable(arena.state_sort(first, 0), "left-parameter")
    program = arena.primitive_advance(first, 0, port, symbol)
    assert arena.substitute(program, {port: left}) == stepped
    assert ledger.counters["boundary_expression_constant_kernel_reductions"] >= 3


def test_unaffected_substitution_and_closed_beta_skip_large_argument_dags(
    monkeypatch: pytest.MonkeyPatch,
) -> None:

    ledger, _, _, arena, first, _ = context()
    sort = arena.state_sort(first, 0)
    x, y, z = (arena.variable(sort, name) for name in ("x", "y", "z"))
    symbol = arena.variable(arena.symbol_sort(first), "symbol")
    large = y
    for _ in range(60):
        large = arena.primitive_advance(first, 0, large, symbol)
    constant = arena.lambda_(x, large)
    before = ledger.counters.get("boundary_expression_rewrite_visits", 0)
    assert arena.apply(constant, z) == large
    assert ledger.counters["boundary_expression_rewrite_visits"] - before == 1
    before = ledger.counters.get("boundary_expression_rewrite_visits", 0)
    assert arena.substitute(large, {x: z}) == large
    assert ledger.counters.get("boundary_expression_rewrite_visits", 0) == before
    result = arena.substitute(large, {y: z})

    def forbidden_rewrite(*args: object) -> object:
        pytest.fail("warm substitution rewrote children")

    monkeypatch.setattr(_canonicalExpressionTransaction, "rewrite", forbidden_rewrite)
    assert arena.substitute(large, {y: z, x: y}) == result


def test_finite_apply_is_extensional_and_rejects_bad_functions_before_warm() -> None:
    from number_compiler.arithmetic.functions.finite_port_action import PortVariable
    from number_compiler.hashlife.execution.continuations.diamond_context_program import (
        LEFT_A,
    )
    from number_compiler.hashlife.interfaces.diamond_kernel import FiniteExpression
    from number_compiler.hashlife.interfaces.diamond_kernel_bridge import (
        input_expression,
    )

    ledger, _, boundaries, arena, first, _ = context()
    primitive = arena.primitive(first)
    assert primitive is not None
    domain = primitive.left_count
    argument = arena.variable(arena.state_sort(first, 0), "argument")
    kernels = boundaries.kernels
    identity = input_expression(kernels, domain, LEFT_A)
    zero = kernels.constant(domain, 0)
    collapsed = arena.finite_apply(first, 0, zero, argument)
    assert arena.node(collapsed).kind == "literal"
    assert arena.node(collapsed).value == 0
    wrapped = arena.finite_apply(first, 0, identity, argument)
    assert wrapped == argument
    nested = arena.finite_apply(first, 0, identity, wrapped)
    assert nested == wrapped
    foreign_port = input_expression(
        kernels, domain, PortVariable(0, 0, "wrong-namespace", 0)
    )
    invalid_range = kernels.intern_expression(
        FiniteExpression(
            domain,
            tuple(
                kernels.functions.constant(True)
                for _ in range((domain - 1).bit_length())
            ),
        )
    )
    before = ledger.snapshot()
    for summary in (foreign_port, invalid_range):
        with pytest.raises(ValueError):
            arena.finite_apply(first, 0, summary, argument)
    assert ledger.snapshot() == before


def test_closure_calls_are_opaque_to_capture_safe_outer_substitution(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _, _, _, arena, first, _ = context()
    sort = arena.state_sort(first, 0)
    parameter = arena.variable(sort, "parameter")
    x, y = (arena.variable(sort, name) for name in ("x", "y"))
    symbol = arena.symbol(first, 2)
    body = arena.primitive_advance(first, 0, parameter, symbol)
    program = arena.closures.intern((parameter,), body)
    call = arena.call(program, (x,))
    assert arena.node(call).kind == "call"
    assert arena.node(call).closure == program
    assert arena.node(call).children == (x.local_id,)
    original_expand = arena.closures.expand

    def forbidden_expand(*args: object) -> object:
        pytest.fail("outer substitution expanded an opaque body")

    monkeypatch.setattr(arena.closures, "expand", forbidden_expand)
    changed = arena.substitute(call, {x: y})
    assert changed == arena.call(program, (y,))
    function = arena.lambda_(x, call)
    assert arena.apply(function, y) == changed
    monkeypatch.setattr(arena.closures, "expand", original_expand)
    assert arena.expand_call(changed) == arena.primitive_advance(first, 0, y, symbol)


def test_closure_ignored_arguments_never_enter_call_identity_but_are_validated() -> (
    None
):
    ledger, arena, first, other, other_action, sort = _foreign_state_fixture()
    a, b, x, y = (arena.variable(sort, name) for name in ("a", "b", "x", "y"))
    body = arena.primitive_advance(first, 0, a, arena.symbol(first, 2))
    program = arena.closures.intern((a, b), body)
    first_call = arena.call(program, (x, x))
    before = ledger.snapshot()
    assert arena.call(program, (x, y)) == first_call
    assert ledger.entries == before.entries
    assert len(arena.node(first_call).children) == 1
    foreign = other.variable(other.state_sort(other_action, 0), "foreign")
    before = assert_rejected_atomically(
        ledger, lambda: arena.call(program, (x, foreign)), ValueError
    )


def _foreign_state_fixture() -> tuple[
    ResourceLedger,
    BoundaryExpressionArena,
    ActionProgramID,
    BoundaryExpressionArena,
    ActionProgramID,
    StateSort,
]:
    ledger, _, _, arena, first, _ = context()
    _, _, _, foreign, foreign_action, _ = context()
    return ledger, arena, first, foreign, foreign_action, arena.state_sort(first, 0)
