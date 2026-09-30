"""Whole-DAG substitution must prune demand without weakening validity."""

from __future__ import annotations

from typing import TYPE_CHECKING

from tests.support.assertions import assert_rejected_atomically

if TYPE_CHECKING:
    import number_compiler.arithmetic.functions.semantic_function_transactions

from typing import TYPE_CHECKING, Never

import pytest

from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSignature,
    SemanticTerminal,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_function_transactions import (
    _Transaction,
)
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitFunctionArena,
    _Circuit,
    substitute_boolean,
)
from number_compiler.resources.ledger import LedgerSnapshot, ResourceLedger

if TYPE_CHECKING:
    from number_compiler.arithmetic.functions.finite_function_types import (
        SemanticFunctionID,
        SemanticNode,
    )
    from number_compiler.hashlife.interfaces.semantic_bits import (
        FactoredFunctionID,
    )


def _restricted_outputs(
    arena: BitFunctionArena, port: FinitePort
) -> tuple[FactoredFunctionID, FactoredFunctionID, FactoredFunctionID]:
    value = arena.variable((port,), port)
    return (
        value,
        arena.map_atoms(value, BOOL, (1, 0, 1, 0)),
        arena.map_atoms(value, BOOL, (1, 1, 0, 0)),
    )


def _function_lengths(arena: BitFunctionArena) -> tuple[int, int, int, int]:
    return (
        len(arena.functions.nodes),
        len(arena.functions.keys),
        len(arena.nodes),
        len(arena.keys),
    )


def _cap_for_failure(
    arena: BitFunctionArena, budget: str, delta: tuple[int, int]
) -> tuple[LedgerSnapshot, tuple[int, int, int, int]]:
    if budget == "nodes":
        arena.ledger.max_nodes = arena.ledger.nodes + delta[0] - 1
    else:
        arena.ledger.max_cache_entries = arena.ledger.entries + delta[1] - 1
    return arena.ledger.snapshot(), _function_lengths(arena)


def _composition_ports() -> tuple[BitFunctionArena, FinitePort, FinitePort]:
    return (
        BitFunctionArena(ResourceLedger()),
        FinitePort(PortVariable(0, 0, "a", 0), 4),
        FinitePort(PortVariable(0, 0, "b", 0), 4),
    )


def _fused_source() -> tuple[
    BitFunctionArena, tuple[FinitePort, ...], _Circuit, int, int, int
]:
    arena = BitFunctionArena(ResourceLedger())
    ports = tuple(
        FinitePort(PortVariable(0, 0, name, 0), 2) for name in ("a", "b", "c")
    )
    source = _Circuit(arena.functions, ports)
    a, b, c = (source.tx.bit(ports, port.variable) for port in ports)
    return arena, ports, source, a, b, c


def _fused_target(
    source: _Circuit,
) -> tuple[FinitePort, FinitePort, _Circuit, int, int, int]:
    x = FinitePort(PortVariable(1, 0, "x", 0), 2)
    y = FinitePort(PortVariable(1, 0, "y", 0), 2)
    target = _Circuit(source.tx.arena, (x, y), source.tx)
    xx, yy = (target.tx.bit(target.inputs, port.variable) for port in (x, y))
    return x, y, target, xx, yy, target.xor(xx, yy)


def test_constant_cofactor_never_visits_the_unselected_subgraph(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena = BitFunctionArena(ResourceLedger())
    flag = FinitePort(PortVariable(0, 0, "flag", 0), 2)
    word = FinitePort(PortVariable(1, 0, "word", 0), 1 << 32)
    c = _Circuit(arena.functions, (flag, word))
    tail = c.one
    for bit in reversed(range(32)):
        variable = PortVariable(1, 0, "word", bit)
        tail = c.tx.decision(c.signature, variable, c.zero, tail)
    root = c.tx.decision(c.signature, flag.variable, c.zero, tail)
    original = _Transaction.node

    def checked(
        self: number_compiler.arithmetic.functions.semantic_function_transactions._Transaction,
        identity: int,
    ) -> SemanticNode:
        if self is c.tx and identity == tail:
            raise AssertionError("substitution entered an erased cofactor")
        return original(self, identity)

    monkeypatch.setattr(_Transaction, "node", checked)
    assert substitute_boolean(c, root, {flag.variable: c.zero}) == c.zero
    assert arena.ledger.counters["semantic_bit_substitution_cofactor_prunes"] == 1


def test_multiple_output_bits_share_one_substitution_traversal() -> None:
    arena = BitFunctionArena(ResourceLedger())
    source = FinitePort(PortVariable(0, 0, "source", 0), 2)
    target = FinitePort(PortVariable(1, 0, "target", 0), 2)
    c = _Circuit(arena.functions, (source,))
    bit = c.tx.bit((source,), source.variable)
    signature = FunctionSignature((source,), AtomSort("word", 1 << 32))
    function = arena._publish(c, (c.normalized(signature, (bit,) * 32, c.one),))[0]
    replacement = arena.variable((target,), target)
    result = arena.substitute(function, {source.variable: replacement})
    assert arena.ledger.counters["semantic_bit_substitution_shared_hits"] >= 31
    assert arena.evaluate(result, {target.variable: 0}) == 0
    assert arena.evaluate(result, {target.variable: 1}) == (1 << 32) - 1


def test_batch_substitution_shares_roots_and_matches_individual_results() -> None:
    arena = BitFunctionArena(ResourceLedger())
    first = FinitePort(PortVariable(0, 0, "first", 0), 4)
    second = FinitePort(PortVariable(0, 1, "second", 0), 4)
    output = AtomSort("word", 4)
    a = arena.variable((first, second), first, output)
    b = arena.variable((first, second), second, output)
    summed = arena.add(a, b, output, wrap=True)
    replacements = {first.variable: b, second.variable: a}
    before_hits = arena.ledger.counters.get("semantic_bit_substitution_shared_hits", 0)
    actual = arena.substitute_many((summed, a), replacements)
    expected = tuple(arena.substitute(f, replacements) for f in (summed, a))
    assert actual == expected
    assert arena.ledger.counters["semantic_bit_substitution_shared_hits"] > before_hits
    assert arena.ledger.counters["semantic_bit_batch_composition_evaluations"] == 1


def test_batch_restriction_preserves_each_output_sort_and_shared_domain() -> None:
    arena = BitFunctionArena(ResourceLedger())
    port = FinitePort(PortVariable(0, 0, "port", 0), 4)
    value, bit, guard = _restricted_outputs(arena, port)
    expected = arena.restrict(value, guard), arena.restrict(bit, guard)
    actual = arena.restrict_many((value, bit), guard)
    assert actual == expected
    for supplied in range(4):
        assert arena.evaluate(actual[0], {port.variable: supplied}) == (
            supplied if supplied < 2 else None
        )
        assert arena.evaluate(actual[1], {port.variable: supplied}) == (
            1 - supplied if supplied < 2 else None
        )


def test_batch_operations_reject_mixed_or_undeclared_interfaces() -> None:
    arena = BitFunctionArena(ResourceLedger())
    first = FinitePort(PortVariable(0, 0, "first", 0), 2)
    second = FinitePort(PortVariable(0, 1, "second", 0), 2)
    a = arena.variable((first,), first)
    b = arena.variable((second,), second)
    first_guard = arena.map_atoms(a, BOOL, (0, 1))
    before = arena.ledger.snapshot()
    with pytest.raises(ValueError, match="one complete input interface"):
        arena.substitute_many((a, b), {first.variable: a})
    with pytest.raises(ValueError, match="undeclared input port"):
        arena.restrict_many((b,), first_guard)
    assert arena.ledger.snapshot() == before


@pytest.mark.parametrize("budget", ("nodes", "entries"))
def test_batch_restriction_budget_failure_publishes_no_partial_result(
    budget: str,
) -> None:
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )

    def fixture() -> tuple[
        BitFunctionArena,
        tuple[FactoredFunctionID, FactoredFunctionID],
        FactoredFunctionID,
    ]:
        arena = BitFunctionArena(ResourceLedger())
        port = FinitePort(PortVariable(0, 0, "batch-budget", 0), 4)
        value, bit, guard = _restricted_outputs(arena, port)
        return arena, (value, bit), guard

    reference, functions, guard = fixture()
    baseline = reference.ledger.nodes, reference.ledger.entries
    reference.restrict_many(functions, guard)
    delta = reference.ledger.nodes - baseline[0], reference.ledger.entries - baseline[1]
    arena, functions, guard = fixture()
    before, lengths = _cap_for_failure(arena, budget, delta)
    with pytest.raises(BlockContextBudgetExceeded):
        arena.restrict_many(functions, guard)
    after = arena.ledger.snapshot()
    assert (after.nodes, after.entries, after.inventory) == (
        before.nodes,
        before.entries,
        before.inventory,
    )
    assert after.peak_nodes >= before.peak_nodes
    assert after.peak_entries >= before.peak_entries
    assert lengths == (
        len(arena.functions.nodes),
        len(arena.functions.keys),
        len(arena.nodes),
        len(arena.keys),
    )


def test_identity_on_unaffected_support_does_not_walk_children(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena = BitFunctionArena(ResourceLedger())
    source = FinitePort(PortVariable(0, 0, "source", 0), 1 << 16)
    unrelated = FinitePort(PortVariable(1, 0, "unrelated", 0), 2)
    c = _Circuit(arena.functions, (source, unrelated))
    tail = c.one
    for bit in reversed(range(16)):
        tail = c.tx.decision(
            c.signature, PortVariable(0, 0, "source", bit), c.zero, tail
        )
    original = _Transaction.node
    calls = []

    def observed(
        self: number_compiler.arithmetic.functions.semantic_function_transactions._Transaction,
        identity: int,
    ) -> SemanticNode:
        calls.append(identity)
        return original(self, identity)

    monkeypatch.setattr(_Transaction, "node", observed)
    assert substitute_boolean(c, tail, {unrelated.variable: c.zero}) == tail
    assert calls == [tail]


def test_identical_numeric_branches_do_not_erase_invalid_condition() -> None:
    arena = BitFunctionArena(ResourceLedger())
    one = arena.constant(FunctionSignature((), BOOL), 1)
    invalid_condition = arena.add(one, one, BOOL)
    value = arena.constant(FunctionSignature((), AtomSort("word", 8)), 5)
    assert arena.evaluate(arena.select(invalid_condition, value, value), {}) is None
    tx = _Transaction(arena.functions)
    signature = FunctionSignature((), BOOL)
    invalid = tx.terminal(signature, SemanticTerminal("invalid"))
    yes = tx.terminal(signature, SemanticTerminal("atom", 1))
    terminal = tx.node(tx.choose(invalid, yes, yes)).terminal
    assert terminal is not None and terminal.kind == "invalid"


def test_unused_replacement_validity_is_preserved() -> None:
    arena = BitFunctionArena(ResourceLedger())
    ignored = FinitePort(PortVariable(0, 0, "ignored", 0), 3)
    value = arena.constant(FunctionSignature((ignored,), AtomSort("word", 8)), 5)
    two = arena.constant(FunctionSignature((), AtomSort("three", 3)), 2)
    invalid = arena.add(two, two, AtomSort("three", 3))
    assert (
        arena.evaluate(arena.substitute(value, {ignored.variable: invalid}), {}) is None
    )


@pytest.mark.parametrize("warm", (False, True))
def test_foreign_replacement_rejected_before_any_shared_lookup(warm: bool) -> None:
    arena, foreign = (
        BitFunctionArena(ResourceLedger()),
        BitFunctionArena(ResourceLedger()),
    )
    port = FinitePort(PortVariable(0, 0, "input", 0), 2)
    function = arena.variable((port,), port)
    own = arena.constant(FunctionSignature((), BOOL), 1)
    other = foreign.constant(FunctionSignature((), BOOL), 1)
    if warm:
        arena.substitute(function, {port.variable: own})
    assert_rejected_atomically(
        arena.ledger,
        lambda: arena.substitute(function, {port.variable: other}),
        ValueError,
    )


def _scalar_fixture() -> tuple[BitFunctionArena, FinitePort, SemanticFunctionID]:
    arena = BitFunctionArena(ResourceLedger())
    port = FinitePort(PortVariable(0, 0, "three", 0), 3)
    return arena, port, arena.functions.variable((port,), port)


def test_scalar_conversion_is_complete_and_warm_probe_precedes_construction(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena, port, scalar = _scalar_fixture()
    factored = arena.from_scalar(scalar)
    assert [arena.evaluate(factored, {port.variable: value}) for value in range(4)] == [
        0,
        1,
        2,
        None,
    ]
    before_frames = arena.ledger.counters["semantic_bit_from_scalar_frames"]

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError(
            "warm canonical conversion must not construct a transaction"
        )

    monkeypatch.setattr(_Transaction, "__init__", forbidden)
    assert arena.from_scalar(scalar) == factored
    assert arena.ledger.counters["semantic_bit_from_scalar_frames"] == before_frames


@pytest.mark.parametrize("warm", (False, True))
def test_scalar_conversion_rejects_foreign_before_memo_mutation(warm: bool) -> None:
    arena, _, scalar = _scalar_fixture()
    other, _, foreign = _scalar_fixture()
    if warm:
        arena.from_scalar(scalar)
    assert_rejected_atomically(
        arena.ledger, lambda: arena.from_scalar(foreign), ValueError
    )
    assert other.ledger is not arena.ledger


@pytest.mark.parametrize("budget", ("nodes", "entries"))
def test_scalar_components_and_source_binding_publish_atomically(budget: str) -> None:
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )

    reference, _, original = _scalar_fixture()
    baseline = reference.ledger.nodes, reference.ledger.entries
    reference.from_scalar(original)
    delta = reference.ledger.nodes - baseline[0], reference.ledger.entries - baseline[1]
    arena, _, scalar = _scalar_fixture()
    before, lengths = _cap_for_failure(arena, budget, delta)
    with pytest.raises(BlockContextBudgetExceeded):
        arena.from_scalar(scalar)
    after = arena.ledger.snapshot()
    assert (
        after.nodes,
        after.entries,
        after.inventory,
        after.peak_nodes,
        after.peak_entries,
    ) == (
        before.nodes,
        before.entries,
        before.inventory,
        before.peak_nodes,
        before.peak_entries,
    )
    assert lengths == (
        len(arena.functions.nodes),
        len(arena.functions.keys),
        len(arena.nodes),
        len(arena.keys),
    )
    assert not arena._scalar_sources


def test_conversion_memo_eviction_preserves_canonical_functions() -> None:
    arena, _, scalar = _scalar_fixture()
    result = arena.from_scalar(scalar)
    arena.ledger.evict_query_memos()
    assert not arena._scalar_sources
    assert arena.from_scalar(scalar) == result


def test_joint_correlated_substitution_avoids_all_intermediate_ite_work() -> None:
    arena = BitFunctionArena(ResourceLedger())
    first = FinitePort(PortVariable(0, 0, "first", 0), 2)
    second = FinitePort(PortVariable(1, 0, "second", 0), 2)
    source = _Circuit(arena.functions, (first, second))
    parity = source.xor(
        source.tx.bit(source.inputs, first.variable),
        source.tx.bit(source.inputs, second.variable),
    )
    xor_function = arena._publish(
        source,
        (
            source.normalized(
                FunctionSignature(source.inputs, BOOL), (parity,), source.one
            ),
        ),
    )[0]
    external = FinitePort(PortVariable(2, 0, "external", 0), 1 << 32)
    target = _Circuit(arena.functions, (external,))
    conjunction = target.one
    for bit in reversed(range(32)):
        conjunction = target.tx.decision(
            target.signature,
            PortVariable(2, 0, "external", bit),
            target.zero,
            conjunction,
        )
    correlated = arena._publish(
        target,
        (
            target.normalized(
                FunctionSignature(target.inputs, BOOL), (conjunction,), target.one
            ),
        ),
    )[0]
    before = arena.ledger.counters.get("semantic_function_ite_frames", 0)
    result = arena.substitute(
        xor_function, {first.variable: correlated, second.variable: correlated}
    )
    assert arena.ledger.counters.get("semantic_function_ite_frames", 0) == before
    for value in (0, 1, (1 << 32) - 1):
        assert arena.evaluate(result, {external.variable: value}) == 0


def test_joint_substitution_keeps_simultaneous_not_sequential_semantics() -> None:
    arena, a, b = _composition_ports()
    output = AtomSort("word", 4)
    aa, bb = arena.variable((a, b), a, output), arena.variable((a, b), b, output)
    plus = arena.add(aa, bb, output, wrap=True)
    result = arena.substitute(aa, {a.variable: plus, b.variable: aa})
    for x in range(4):
        for y in range(4):
            assert arena.evaluate(result, {a.variable: x, b.variable: y}) == (x + y) % 4


def _composition_fixture() -> tuple[
    BitFunctionArena,
    FactoredFunctionID,
    dict[PortVariable, FactoredFunctionID],
    FinitePort,
]:
    arena, a, b = _composition_ports()
    x = FinitePort(PortVariable(1, 0, "x", 0), 4)
    aa, bb = arena.variable((a, b), a), arena.variable((a, b), b)
    function = arena.add(aa, bb, AtomSort("sum", 8))
    value = arena.variable((x,), x)
    return arena, function, {a.variable: value, b.variable: value}, x


def test_whole_composition_probe_precedes_transaction_and_mapping_order_is_canonical(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena, function, replacements, port = _composition_fixture()
    result = arena.substitute(function, replacements)

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError(
            "canonical whole-function cache hit constructed a transaction"
        )

    monkeypatch.setattr(_Circuit, "__init__", forbidden)
    assert (
        arena.substitute(function, dict(reversed(tuple(replacements.items()))))
        == result
    )
    assert arena.ledger.counters["semantic_bit_composition_hits"] == 1
    assert arena.evaluate(result, {port.variable: 3}) == 6


@pytest.mark.parametrize("budget", ("nodes", "entries"))
def test_composition_memo_and_all_function_nodes_publish_atomically(
    budget: str,
) -> None:
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )

    reference, function, replacements, _ = _composition_fixture()
    baseline = reference.ledger.nodes, reference.ledger.entries
    reference.substitute(function, replacements)
    delta = reference.ledger.nodes - baseline[0], reference.ledger.entries - baseline[1]
    arena, function, replacements, _ = _composition_fixture()
    if budget == "nodes":
        arena.ledger.max_nodes = arena.ledger.nodes + delta[0] - 1
    else:
        arena.ledger.max_cache_entries = arena.ledger.entries + delta[1] - 1
    before = arena.ledger.snapshot()
    with pytest.raises(BlockContextBudgetExceeded):
        arena.substitute(function, replacements)
    after = arena.ledger.snapshot()
    assert (
        after.nodes,
        after.entries,
        after.inventory,
        after.peak_nodes,
        after.peak_entries,
    ) == (
        before.nodes,
        before.entries,
        before.inventory,
        before.peak_nodes,
        before.peak_entries,
    )
    assert not arena._compositions


def test_whole_composition_cache_is_evictable_without_invalidating_functions() -> None:
    arena, function, replacements, _ = _composition_fixture()
    result = arena.substitute(function, replacements)
    arena.ledger.evict_query_memos()
    assert not arena._compositions
    assert arena.substitute(function, replacements) == result


def test_fused_integer_environments_bind_each_original_support_layout() -> None:
    from number_compiler.hashlife.interfaces.boolean_composition import (
        substitute_boolean_fused,
    )

    arena, source_ports, source, a, b, c = _fused_source()
    first = source.conjunction(a, source.conjunction(b, c))
    second = source.conjunction(a, c)
    x, y, target, xx, yy, parity = _fused_target(source)
    replacement = dict(zip((port.variable for port in source_ports), (parity, xx, yy)))
    outputs = (
        substitute_boolean_fused(target, first, replacement),
        substitute_boolean_fused(target, second, replacement),
    )
    support_layouts = tuple(
        (
            key.root,
            key.environment,
            len(target.tx.node(key.root).support),
        )
        for key in target._fused_substitutions
    )
    signature = FunctionSignature(target.inputs, AtomSort("two-bits", 4))
    result = arena._publish(
        target, (target.normalized(signature, outputs, target.one),)
    )[0]
    for vx in range(2):
        for vy in range(2):
            expected = ((vx ^ vy) & vx & vy) | (((vx ^ vy) & vy) << 1)
            assert arena.evaluate(result, {x.variable: vx, y.variable: vy}) == expected
    assert all(
        type(root) is int
        and all(type(value) is int for value in environment)
        and len(environment) == support_size
        for root, environment, support_size in support_layouts
    )
    assert support_layouts
    with pytest.raises(RuntimeError, match="closed semantic construction"):
        target.tx.node(support_layouts[0][0])
    assert all(
        type(before) is int
        and type(after) is int
        and all(type(index) is int for index in indices)
        for (before, after), indices in target._fused_projections.items()
    )


def test_fused_projection_cache_preserves_permuted_correlated_inputs() -> None:
    from number_compiler.hashlife.interfaces.boolean_composition import (
        substitute_boolean_fused,
    )

    arena, source_ports, source, a, b, c = _fused_source()
    root = source.choose(a, b, c)
    x, y, target, xx, yy, parity = _fused_target(source)
    variables = tuple(port.variable for port in source_ports)
    first = substitute_boolean_fused(
        target, root, dict(zip(variables, (parity, xx, yy)))
    )
    second = substitute_boolean_fused(
        target, root, dict(zip(variables, (parity, yy, xx)))
    )
    signature = FunctionSignature(target.inputs, AtomSort("two-bits", 4))
    result = arena._publish(
        target, (target.normalized(signature, (first, second), target.one),)
    )[0]
    for vx in range(2):
        for vy in range(2):
            expected = (vx if vx ^ vy else vy) | ((vy if vx ^ vy else vx) << 1)
            assert arena.evaluate(result, {x.variable: vx, y.variable: vy}) == expected
    assert arena.ledger.counters["semantic_bit_fused_projection_hits"] > 0
