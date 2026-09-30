"""Finite semantic aliases are tested against independently evaluated truth tables."""

from __future__ import annotations

from functools import partial
from itertools import product
from typing import Literal, cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSignature,
    FunctionSort,
    ProductSort,
    SemanticFunctionID,
    SemanticSort,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_function_transactions import (
    _Transaction,
)
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.resources.ledger import ResourceLedger
from tests.support.arithmetic_fixtures import ternary_xy_ports
from tests.support.assertions import assert_rejected_atomically


def fixture() -> tuple[
    SemanticFunctionArena,
    FinitePort,
    FinitePort,
    SemanticFunctionID,
    SemanticFunctionID,
]:
    arena = SemanticFunctionArena(ResourceLedger())
    x, y = (FinitePort(PortVariable(0, 0, role, 0), 2) for role in ("x", "y"))
    inputs = (x, y)
    return arena, x, y, arena.variable(inputs, x, BOOL), arena.variable(inputs, y, BOOL)


def atom(
    arena: SemanticFunctionArena,
    inputs: tuple[
        FinitePort,
        FinitePort,
    ],
    value: int,
) -> SemanticFunctionID:
    return arena.atom(FunctionSignature(inputs, BOOL), value)


def test_boolean_truth_functions_and_noncommuting_simultaneous_substitution() -> None:
    arena, x, y, vx, vy = fixture()
    zero, one = atom(arena, (x, y), 0), atom(arena, (x, y), 1)
    not_x, not_y = arena.ite(vx, zero, one), arena.ite(vy, zero, one)
    xor = arena.ite(vx, not_y, vy)
    equivalent = arena.ite(vy, not_x, vx)
    assert xor == equivalent
    # Simultaneous x:=y,y:=not(x) differs from sequential replacement.
    simultaneous = arena.substitute(vx, {x.variable: vy, y.variable: not_x})
    sequential = arena.substitute(
        arena.substitute(vx, {x.variable: vy}), {y.variable: not_x}
    )
    assert simultaneous != sequential
    for a, b in product(range(2), repeat=2):
        values = {x.variable: a, y.variable: b}
        assert arena.evaluate(xor, values).value == a ^ b
        assert arena.evaluate(simultaneous, values).value == b
        assert arena.evaluate(sequential, values).value == 1 - a


def test_curried_product_preserves_outer_port_and_canonical_inner_functions() -> None:
    arena, x, y, vx, vy = fixture()
    zero, one = atom(arena, (x, y), 0), atom(arena, (x, y), 1)
    xor = arena.ite(vx, arena.ite(vy, zero, one), vy)
    xor_alt = arena.ite(vy, arena.ite(vx, zero, one), vx)
    inner = arena.curry(xor, (y,))
    assert inner == arena.curry(xor_alt, (y,))
    outer_x = arena.variable((x,), x, BOOL)
    complete = arena.product((outer_x, inner))
    assert arena.signature(complete).output == ProductSort(
        (BOOL, FunctionSort((y,), BOOL))
    )
    for a in range(2):
        first, function = arena.terminal_references(complete, {x.variable: a})
        assert arena.evaluate(first, {}).value == a
        (inner_id,) = arena.terminal_references(function, {})
        for b in range(2):
            assert arena.evaluate(inner_id, {y.variable: b}).value == a ^ b
    assert arena.apply(inner, {y.variable: vy}) == xor
    # Abstracting another time/role cannot capture the original free x.
    z = FinitePort(PortVariable(1, 0, "x", 0), 2)
    vz = arena.variable((z,), z, BOOL)
    applied = arena.apply(inner, {y.variable: vz})
    for a, b in product(range(2), repeat=2):
        assert arena.evaluate(applied, {x.variable: a, z.variable: b}).value == a ^ b


def test_equal_exits_do_not_identify_different_finite_outputs() -> None:
    arena, x, y, vx, vy = fixture()
    exit_function = atom(arena, (x, y), 0)
    assert arena.product((exit_function, vx)) != arena.product((exit_function, vy))


def test_non_power_of_two_admissibility_and_curried_invalid_codes() -> None:
    arena = SemanticFunctionArena(ResourceLedger())
    x, y, sort = ternary_xy_ports()
    vx = arena.variable((x, y), x, sort)
    curried = arena.curry(vx, (y,))
    for a, b in product(range(4), repeat=2):
        actual = arena.evaluate(vx, {x.variable: a, y.variable: b})
        assert (actual.kind == "invalid") == (a == 3 or b == 3)
        if a != 3:
            (child,) = arena.terminal_references(curried, {x.variable: a})
            assert arena.evaluate(child, {y.variable: b}) == actual
        else:
            assert arena.evaluate(curried, {x.variable: a}).kind == "invalid"


def test_warm_operations_skip_child_rewrites_and_eviction_preserves_ids(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena, _x, _y, vx, vy = fixture()
    cached = arena.product((vx, vy))
    nodes = len(arena.nodes)
    monkeypatch.setattr(
        _Transaction,
        "zip_product",
        lambda *args: pytest.fail("warm operation replayed"),
    )
    assert arena.product((vx, vy)) == cached
    assert len(arena.nodes) == nodes
    monkeypatch.undo()
    arena.ledger.evict_query_memos()
    assert arena.product((vx, vy)) == cached
    assert len(arena.nodes) == nodes


@pytest.mark.parametrize(
    "field,value",
    [
        ("local_id", True),
        ("local_id", 0.0),
        ("local_id", -1),
        ("kind", "other"),
        ("owner", ArenaToken("foreign")),
    ],
)
def test_forged_handles_reject_before_warm_operation_or_scalar_lookup(
    field: str, value: ArenaToken | Literal["other"] | bool | float
) -> None:
    arena, x, y, vx, vy = fixture()
    arena.product((vx, vy))
    forged = object.__new__(SemanticFunctionID)
    for name in ("owner", "kind", "local_id"):
        object.__setattr__(forged, name, value if name == field else getattr(vx, name))
    before = arena.ledger.snapshot()
    with pytest.raises(ValueError):
        arena.product((forged, vy))
    with pytest.raises(ValueError):
        arena.evaluate(forged, {x.variable: 0, y.variable: 0})
    assert arena.ledger.snapshot() == before


def test_failed_product_publication_does_not_retain_nodes_interner_or_memo() -> None:
    arena, _, _, vx, vy = fixture()
    before = arena.ledger.snapshot()
    keys, nodes, memo = (
        tuple(arena.keys.items()),
        tuple(arena.nodes),
        tuple(arena.memo.items()),
    )
    arena.ledger.tighten_limits(None, before.entries + 1)
    with pytest.raises(BlockContextBudgetExceeded):
        arena.product((vx, vy))
    after = arena.ledger.snapshot()
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
    assert (
        tuple(arena.keys.items()),
        tuple(arena.nodes),
        tuple(arena.memo.items()),
    ) == (keys, nodes, memo)


def test_wide_primitive_identity_rejects_before_domain_expansion() -> None:
    arena = SemanticFunctionArena(ResourceLedger())
    port = FinitePort(PortVariable(0, 0, "wide", 0), 1 << 63)
    assert_rejected_atomically(
        arena.ledger,
        lambda: arena.variable((port,), port),
        ValueError,
        match="bit-factored",
    )


@pytest.mark.parametrize("value", [True, 2.0, float("nan"), "2"])
def test_sort_cardinalities_require_exact_integers(value: object) -> None:
    with pytest.raises(ValueError):
        AtomSort("bad", cast("int", value))
    with pytest.raises(ValueError):
        FinitePort(PortVariable(0, 0, "bad", 0), cast("int", value))


def test_all_two_port_truth_tables_agree_across_shannon_orders_and_currying() -> None:
    arena, x, y, vx, vy = fixture()
    constants = (atom(arena, (x, y), 0), atom(arena, (x, y), 1))
    for outputs in product(range(2), repeat=4):
        by_x = arena.ite(
            vx,
            arena.ite(vy, constants[outputs[3]], constants[outputs[2]]),
            arena.ite(vy, constants[outputs[1]], constants[outputs[0]]),
        )
        by_y = arena.ite(
            vy,
            arena.ite(vx, constants[outputs[3]], constants[outputs[1]]),
            arena.ite(vx, constants[outputs[2]], constants[outputs[0]]),
        )
        assert by_x == by_y
        for bound, outer in ((x, y), (y, x)):
            curried = arena.curry(by_x, (bound,))
            assert curried == arena.curry(by_y, (bound,))
            for a, b in product(range(2), repeat=2):
                (child,) = arena.terminal_references(curried, {outer.variable: a})
                expected = outputs[2 * b + a] if bound == x else outputs[2 * a + b]
                assert arena.evaluate(child, {bound.variable: b}).value == expected
        assert arena.apply(arena.curry(by_x, ()), {}) == by_x


def test_simultaneous_substitution_mapping_order_is_canonical_and_foreign_input_rejects() -> (
    None
):
    arena, x, y, vx, vy = fixture()
    pair = arena.product((vx, vy))
    swapped = arena.substitute(pair, {x.variable: vy, y.variable: vx})
    assert swapped == arena.substitute(pair, {y.variable: vx, x.variable: vy})
    assert arena.substitute(swapped, {x.variable: vy, y.variable: vx}) == pair
    foreign = SemanticFunctionArena(ResourceLedger()).atom(
        FunctionSignature((), BOOL), 0
    )
    assert_rejected_atomically(
        arena.ledger,
        lambda: arena.substitute(pair, {x.variable: foreign, y.variable: vx}),
        ValueError,
    )


def test_invalid_integer_evaluation_and_warm_sort_aliases_do_not_mutate() -> None:
    arena, x, y, vx, _ = fixture()
    for value in (True, 0.0, float("nan"), "0"):
        before = assert_rejected_atomically(
            arena.ledger,
            partial(
                arena.evaluate, vx, {x.variable: cast("int", value), y.variable: 0}
            ),
            ValueError,
        )
        forged = object.__new__(AtomSort)
        object.__setattr__(forged, "name", "boolean")
        object.__setattr__(forged, "cardinality", value)
        with pytest.raises(ValueError):
            arena.atom(FunctionSignature((), forged), 0)
        assert arena.ledger.snapshot() == before


def test_forged_cyclic_sort_rejects_before_hashing_or_retention() -> None:
    arena = SemanticFunctionArena(ResourceLedger())
    cyclic = ProductSort((BOOL,))
    object.__setattr__(cyclic, "items", (cyclic,))
    assert_rejected_atomically(
        arena.ledger,
        lambda: arena.invalid(FunctionSignature((), cyclic)),
        ValueError,
        match="cyclic",
    )
    # Shared acyclic children remain valid.
    signature = FunctionSignature((), ProductSort((BOOL, BOOL)))
    assert arena.resolve(arena.invalid(signature)).signature == signature


def test_deep_independent_sort_dags_hash_and_compare_without_recursion() -> None:
    arena = SemanticFunctionArena(ResourceLedger())
    first: SemanticSort = AtomSort("deep-leaf", 2)
    equal: SemanticSort = AtomSort("deep-leaf", 2)
    different: SemanticSort = AtomSort("different-leaf", 2)
    for depth in range(1500):
        if depth % 2:
            first = FunctionSort((), first)
            equal = FunctionSort((), equal)
            different = FunctionSort((), different)
        else:
            # Duplicate child references ensure traversal follows DAG size.
            first = ProductSort((first, first))
            equal = ProductSort((equal, equal))
            different = ProductSort((different, different))
    assert first == equal
    assert hash(first) == hash(equal)
    assert first != different
    one = arena.invalid(FunctionSignature((), first))
    assert one == arena.invalid(FunctionSignature((), equal))
    assert one != arena.invalid(FunctionSignature((), different))


def test_shared_sort_hash_validates_once_and_rejects_a_forged_cycle(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.arithmetic.functions.finite_function_types as semantic

    port = FinitePort(PortVariable(0, 0, "shared-hash", 0), 3)
    shared = FunctionSort((port,), BOOL)
    root = ProductSort((shared, shared))
    calls: list[tuple[FinitePort, ...]] = []
    original_ports = semantic._ports

    def counted_ports(ports: tuple[FinitePort, ...]) -> None:
        calls.append(ports)
        original_ports(ports)

    monkeypatch.setattr(semantic, "_ports", counted_ports)
    atom_hash = hash(("atom", BOOL.name, BOOL.cardinality))
    function_hash = hash(("function", (port,), atom_hash))
    root_hash = hash(("product", (function_hash, function_hash)))
    assert hash(root) == root_hash
    assert calls == [(port,)]

    calls.clear()
    signature = FunctionSignature((), root)
    assert hash(signature) == hash(((), root_hash))
    assert calls == [(), (port,)]

    object.__setattr__(shared, "output", shared)
    try:
        with pytest.raises(ValueError, match="cyclic"):
            hash(root)
        with pytest.raises(ValueError, match="cyclic"):
            FunctionSignature((), root)
    finally:
        object.__setattr__(shared, "output", BOOL)


def test_sort_hash_collision_still_compares_exact_deep_structure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    first = ProductSort((FunctionSort((), AtomSort("first", 2)),))
    other = ProductSort((FunctionSort((), AtomSort("other", 2)),))
    monkeypatch.setattr(
        "number_compiler.arithmetic.functions.finite_function_types._sort_hash",
        lambda value: 7,
    )
    assert hash(first) == hash(other)
    assert first != other
    arena = SemanticFunctionArena(ResourceLedger())
    assert arena.invalid(FunctionSignature((), first)) != arena.invalid(
        FunctionSignature((), other)
    )


def test_direct_sort_hash_and_equality_reject_forged_cycles() -> None:
    cyclic = FunctionSort((), BOOL)
    object.__setattr__(cyclic, "output", cyclic)
    with pytest.raises(ValueError, match="cyclic"):
        hash(cyclic)
    with pytest.raises(ValueError, match="cyclic"):
        _ = cyclic == FunctionSort((), BOOL)
