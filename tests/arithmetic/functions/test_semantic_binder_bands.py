"""Nested binder order preserves lexical scope and selector-first finite DAGs."""

from __future__ import annotations

from itertools import product
from typing import TYPE_CHECKING

from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FinitePort,
    FunctionSignature,
    FunctionSort,
    ProductSort,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitFunctionArena,
    BooleanCircuit,
)
from number_compiler.hashlife.interfaces.semantic_structures import (
    StructureArena,
    _aliases,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics

if TYPE_CHECKING:
    from number_compiler.hashlife.interfaces.semantic_structures import (
        StructureID,
    )


def port(index: int, role: str, cardinality: int = 2) -> FinitePort:
    return FinitePort(PortVariable(index, 0, role, 0), cardinality)


def mux(
    width: int = 8,
) -> tuple[StructureArena, FinitePort, tuple[FinitePort, ...], StructureID]:
    arena = StructureArena(BitFunctionArena(ResourceLedger()))
    selector = port(0, "selector", width)
    entries = tuple(port(index + 1, "entry") for index in range(width))
    inputs = (selector, *entries)
    circuit = BooleanCircuit(arena.functions, inputs)
    leaves = {
        index: circuit.tx.bit(inputs, entry.variable)
        for index, entry in enumerate(entries)
    }
    for bit in reversed(range(selector.bits)):
        condition = circuit.tx.bit(inputs, PortVariable(0, 0, "selector", bit))
        leaves = {
            index: circuit.choose(condition, leaves[index | (1 << bit)], leaves[index])
            for index in range(1 << bit)
        }
    factored = arena.bits.publish_circuit(
        circuit,
        (
            circuit.normalized(
                FunctionSignature(inputs, BOOL), (leaves[0],), circuit.one
            ),
        ),
    )[0]
    body = arena.atom(factored)
    inner = arena.curry(body, (selector,))
    return arena, selector, entries, inner


def test_product_height_uses_maximum_branch_and_skips_occupied_free_slots() -> None:
    a, b, c, d, e = (port(index, "declared") for index in range(5))
    output = ProductSort(
        (
            FunctionSort((a, b), BOOL),
            FunctionSort((c,), FunctionSort((d, e), BOOL)),
            BOOL,
        )
    )
    free = (port(0, "semantic-bound"), port(2, "semantic-bound"))
    declared = (port(5, "outer"), port(6, "outer"))
    aliases = _aliases(free, declared, output)
    # Available slots1,3,4 belong to output height3; this binder uses5,6.
    assert tuple(alias.variable.time for alias in aliases) == (5, 6)
    assert not {alias.variable for alias in aliases} & {item.variable for item in free}
    assert tuple(alias.variable.time for alias in _aliases(free, declared)) == (1, 3)


def test_inner_selector_precedes_outer_entry_band_with_bounded_actual_publication() -> (
    None
):
    arena, _, entries, inner = mux()
    before = len(arena.functions.nodes)
    outer = arena.curry(inner, entries)
    outer_node = arena.resolve(outer)
    assert outer_node.body is not None
    inner_node = arena.resolve(outer_node.body)
    assert inner_node.body is not None
    leaf = arena.resolve(inner_node.body)
    assert max(item.variable.time for item in inner_node.bound) < min(
        item.variable.time for item in outer_node.bound
    )
    assert leaf.atom is not None
    function = arena.bits.resolve(leaf.atom).bits[0]
    reachable = tuple(arena.functions.iter_reachable(function))
    # This is the actual reduced8-way mux: at most7 selector decisions,
    # 8 entry decisions and2 terminals. Also bound ALL new retained nodes.
    assert len(reachable) <= 17
    assert len(arena.functions.nodes) - before <= 8 * len(entries) + 16
    for values in product((0, 1), repeat=len(entries)):
        inputs = {
            alias.variable: value
            for alias, value in zip(outer_node.bound, values, strict=True)
        }
        for selected in range(len(entries)):
            inputs[inner_node.bound[0].variable] = selected
            assert arena.evaluate_atom(inner_node.body, inputs) == values[selected]
    report = collect_ledger_metrics(arena.ledger)
    assert report.resource_audit_complete == 1 and report.forbidden_future_payloads == 0


def test_applying_outer_argument_with_inner_band_name_does_not_capture_it() -> None:
    arena, selector, entries, inner = mux(2)
    outer = arena.curry(inner, entries)
    free = port(0, "semantic-bound")
    variable = arena.bits.variable((free,), free, BOOL)
    one = arena.bits.constant(FunctionSignature((), BOOL), 1)
    specialized = arena.apply(
        outer, {entries[0].variable: variable, entries[1].variable: one}
    )
    assert free.variable in {
        item.variable for item in arena.resolve(specialized).signature.inputs
    }
    assert free.variable not in {
        item.variable for item in arena.resolve(specialized).bound
    }
    for index in (0, 1):
        argument = arena.bits.constant(FunctionSignature((), BOOL), index)
        result = arena.apply(specialized, {selector.variable: argument})
        for value in (0, 1):
            assert arena.evaluate_atom(result, {free.variable: value}) == (
                value if not index else 1
            )
    assert collect_ledger_metrics(arena.ledger).forbidden_future_payloads == 0


def test_nested_eta_derivation_returns_same_complete_structure_identity() -> None:
    arena, _, entries, inner = mux(4)
    outer = arena.curry(inner, entries)
    arguments = {
        entry.variable: arena.bits.variable(entries, entry, BOOL) for entry in entries
    }
    expanded = arena.apply(outer, arguments)
    assert expanded == inner
    assert arena.curry(expanded, entries) == outer
    assert collect_ledger_metrics(arena.ledger).resource_audit_complete == 1
