"""Kernel truth tables reduce before any source letter is selected."""

from __future__ import annotations

from itertools import product
from typing import TYPE_CHECKING, Literal

import pytest

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.block_kernel import (
    BaseBlockEffect,
    _load_base10_t2_kernel,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena
from number_compiler.hashlife.interfaces.diamond_truth_function import (
    compile_truth_function,
)
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import TransferSummaryID
    from number_compiler.hashlife.interfaces.diamond_kernel import (
        DiamondKernelArena,
        FiniteExpression,
        PrimitiveKernel,
    )


def minterm_reference(
    arena: DiamondKernelArena,
    kernel: PrimitiveKernel,
    operation: Literal["advance", "emit"],
    side: BoundarySide,
    nodes: tuple[FiniteExpression, ...]
    | tuple[
        FiniteExpression,
        FiniteExpression,
    ],
) -> TransferSummaryID:
    """Independent complete-table oracle; no call to the production builder."""
    domain = kernel.blank + 1 if operation == "emit" else len(kernel.domain(side))
    result = arena.constant(domain, 0)
    for values in product(*(range(node.domain) for node in nodes)):
        condition = arena.functions.constant(True)
        for value, node in zip(values, nodes, strict=True):
            for bit, function in enumerate(node.bits):
                selected = (
                    function if value & (1 << bit) else arena.functions.negate(function)
                )
                condition = arena.functions.choose(
                    selected, condition, arena.functions.constant(False)
                )
        value = (
            kernel.emit(*values)
            if operation == "emit"
            else kernel.advance(side, *values)
        )
        result = arena.choose(condition, arena.constant(domain, value), result)
    return result


@pytest.mark.parametrize("effect", [BaseBlockEffect(3), CollatzPhysicalBlockEffect()])
@pytest.mark.parametrize(
    "operation,side",
    [
        ("emit", BoundarySide.LEFT),
        ("advance", BoundarySide.LEFT),
        ("advance", BoundarySide.RIGHT),
    ],
)
def test_direct_boolean_builder_matches_reference_function_ids(
    effect: BaseBlockEffect | CollatzPhysicalBlockEffect,
    operation: Literal["advance", "emit"],
    side: BoundarySide,
) -> None:
    arena = DiamondKernelArena()
    kernel = arena.kernel(arena.intern(effect))
    domains = (
        (kernel.left_count, kernel.blank + 1, kernel.right_count)
        if operation == "emit"
        else (len(kernel.domain(side)), kernel.blank + 1)
    )
    arguments = tuple(
        arena.variable(domain, PortVariable(0, index, "truth", 0))
        for index, domain in enumerate(domains)
    )
    nodes = tuple(arena.expression(value) for value in arguments)
    reference = minterm_reference(arena, kernel, operation, side, nodes)
    assert compile_truth_function(arena, kernel, operation, side, nodes) == reference


def test_correlated_and_nontrivial_argument_functions_use_exact_ite_fallback() -> None:
    arena = DiamondKernelArena()
    kernel = arena.kernel(arena.intern(CollatzPhysicalBlockEffect()))
    port = PortVariable(0, 0, "shared", 0)
    left = arena.variable(kernel.left_count, port)
    symbol = arena.variable(kernel.blank + 1, port)
    condition = arena.functions.variable(PortVariable(0, 0, "gate", 0))
    left = arena.choose(condition, left, arena.constant(kernel.left_count, 0))
    nodes = (arena.expression(left), arena.expression(symbol))
    reference = minterm_reference(arena, kernel, "advance", BoundarySide.LEFT, nodes)
    assert (
        compile_truth_function(arena, kernel, "advance", BoundarySide.LEFT, nodes)
        == reference
    )


def test_verified_t2_slice_publishes_only_final_finite_expression() -> None:
    arena = DiamondKernelArena()
    kernel = arena.kernel(arena.intern(_load_base10_t2_kernel()))
    left_port, right_port = PortVariable(0, 0, "t2", 0), PortVariable(0, 2, "t2", 0)
    arguments = (
        arena.variable(kernel.left_count, left_port),
        arena.constant(20, 7),
        arena.variable(kernel.right_count, right_port),
    )
    before = len(arena._expressions)
    result = compile_truth_function(
        arena,
        kernel,
        "emit",
        BoundarySide.LEFT,
        tuple(arena.expression(value) for value in arguments),
    )
    assert len(arena._expressions) == before + 1
    assert arena.ledger.counters["primitive_output_evaluations"] == 757 * 179
    assert arena.ledger.counters["diamond_kernel_shannon_peak_frames"] <= 18
    # Deterministic coverage of allleft/right ranges, plus invalidbinary codes.
    for left, right in product(
        (0, 1, 17, 231, 756, 757, 1023), (0, 1, 37, 178, 179, 255)
    ):
        inputs = {
            PortVariable(0, 0, "t2", bit): bool(left & (1 << bit)) for bit in range(10)
        }
        inputs.update(
            {
                PortVariable(0, 2, "t2", bit): bool(right & (1 << bit))
                for bit in range(8)
            }
        )
        expected = (
            kernel.effect.emit(left, 7, right) if left < 757 and right < 179 else 0
        )
        assert arena.evaluate(result, inputs) == expected
    assert all(row.accounting_delta == 0 for row in arena.ledger.inventory())


def test_foreign_boolean_argument_rejects_before_allocating() -> None:
    arena, other = DiamondKernelArena(), DiamondKernelArena()
    kernel = arena.kernel(arena.intern(CollatzPhysicalBlockEffect()))
    left = other.expression(
        other.variable(kernel.left_count, PortVariable(0, 0, "foreign", 0))
    )
    symbol = arena.expression(arena.constant(kernel.blank + 1, 0))
    before = arena.ledger.snapshot()
    with pytest.raises(ValueError):
        compile_truth_function(
            arena, kernel, "advance", BoundarySide.LEFT, (left, symbol)
        )
    assert arena.ledger.snapshot() == before
