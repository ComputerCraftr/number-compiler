"""Complete publication has one factored carrier across construction syntaxes."""

from __future__ import annotations

from dataclasses import replace
from itertools import product
from typing import TYPE_CHECKING

import pytest

from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.interfaces.diamond_quotient import (
    COMPONENT_ROLES,
    DiamondQuotientArena,
    MacroComponents,
    MacroInterface,
)
from number_compiler.hashlife.interfaces.semantic_bits import BitFunctionArena
from number_compiler.hashlife.interfaces.semantic_structure_conversion import (
    StructureConversion,
)
from number_compiler.hashlife.interfaces.semantic_structure_publication import (
    publish_structure,
)
from number_compiler.hashlife.interfaces.semantic_structures import (
    StructureArena,
    StructureID,
    _Builder,
)
from number_compiler.resources.ledger import ResourceLedger
from tests.support.diamond_quotient import curried_increment

if TYPE_CHECKING:
    from number_compiler.arithmetic.functions.finite_function_types import (
        SemanticFunctionID,
    )


def converted(
    arena: StructureArena,
    function: SemanticFunctionID,
) -> StructureID:
    builder = _Builder(arena)
    root = StructureConversion(builder).convert(function)
    return publish_structure(builder, root)


@pytest.mark.parametrize("cardinality", (3, 4))
def test_closed_terminal_compatibility_and_joint_outer_functions_have_one_identity(
    cardinality: int,
) -> None:
    functions = SemanticFunctionArena(ResourceLedger())
    bits = BitFunctionArena(functions.ledger, functions)
    arena = StructureArena(bits)
    x = FinitePort(PortVariable(0, 0, "x", 0), cardinality)
    y = FinitePort(PortVariable(0, 0, "y", 0), cardinality)
    word = AtomSort("word", cardinality)
    fx, fy = (functions.variable((x, y), port, word) for port in (x, y))
    bx, by = (arena.atom(bits.variable((x, y), port, word)) for port in (x, y))
    closed = functions.curry(functions.product((fx, fy)), (y,))
    joint = arena.curry(arena.product((bx, by)), (y,))
    assert converted(arena, closed) == joint
    for a, b in product(range(1 << x.bits), repeat=2):
        argument = (
            bits.constant(FunctionSignature((), word), b) if b < cardinality else None
        )
        if argument is None:
            continue
        applied = arena.apply(joint, {y.variable: argument})
        assert arena.evaluate_atom(arena.component(applied, 0), {x.variable: a}) == (
            a if a < cardinality else None
        )
        assert arena.evaluate_atom(arena.component(applied, 1), {x.variable: a}) == (
            b if a < cardinality else None
        )


def test_nested_functions_preserve_outer_dependencies_and_share_factored_quotient() -> (
    None
):
    functions = SemanticFunctionArena(ResourceLedger())
    bits = BitFunctionArena(functions.ledger, functions)
    structures = StructureArena(bits)
    x = FinitePort(PortVariable(0, 0, "x", 0), 2)
    y = FinitePort(PortVariable(0, 0, "y", 0), 2)
    joint_x = functions.variable((x, y), x, BOOL)
    joint_y = functions.variable((x, y), y, BOOL)
    output = functions.curry(functions.product((joint_x, joint_y)), (y,))
    outer = functions.variable((x,), x, BOOL)
    scalar = functions.product((outer, output))
    direct = structures.product(
        (
            structures.atom(bits.variable((x,), x, BOOL)),
            structures.curry(
                structures.product(
                    tuple(
                        structures.atom(bits.variable((x, y), port, BOOL))
                        for port in (x, y)
                    )
                ),
                (y,),
            ),
        )
    )
    assert converted(structures, scalar) == direct
    arena = DiamondQuotientArena(functions, structures=structures)
    zero, one = (
        functions.atom(FunctionSignature((x,), BOOL), value) for value in (0, 1)
    )
    components = MacroComponents(*(zero for _ in COMPONENT_ROLES))
    outputs = tuple(
        structures.resolve(direct).signature.output if role == "output" else BOOL
        for role in COMPONENT_ROLES
    )
    signature = arena.intern_interface(
        MacroInterface(SemanticIdentity("test-structured-v1", ()), (x,), outputs, one)
    )
    first = arena.intern(signature, replace(components, output=scalar))
    assert arena.intern(signature, replace(components, output=direct)) == first
    assert all(
        type(ref) is StructureID for ref in arena.resolve(first).components.functions()
    )


def test_partial_nested_structured_output_rejects_before_quotient_mutation() -> None:
    functions = SemanticFunctionArena(ResourceLedger())
    bits = BitFunctionArena(functions.ledger, functions)
    structures = StructureArena(bits)
    x = FinitePort(PortVariable(0, 0, "x", 0), 4)
    y = FinitePort(PortVariable(0, 0, "y", 0), 2)
    word = AtomSort("word", 4)
    partial = curried_increment(structures, x, y, word)
    arena = DiamondQuotientArena(functions, structures=structures)
    zero, one = (
        functions.atom(FunctionSignature((x,), BOOL), value) for value in (0, 1)
    )
    outputs = tuple(
        structures.resolve(partial).signature.output if role == "output" else BOOL
        for role in COMPONENT_ROLES
    )
    signature = arena.intern_interface(
        MacroInterface(SemanticIdentity("test-partial-v1", ()), (x,), outputs, one)
    )
    components = MacroComponents(
        *(partial if role == "output" else zero for role in COMPONENT_ROLES)
    )
    before = arena.ledger.snapshot()
    with pytest.raises(ValueError, match="undefined"):
        arena.intern(signature, components)
    after = arena.ledger.snapshot()
    assert (after.entries, after.nodes, after.inventory) == (
        before.entries,
        before.nodes,
        before.inventory,
    )
