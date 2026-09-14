"""Finite MTDD/BDD conversion keeps complete function IDs canonical."""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.execution.continuations.diamond_runtime import (
    DiamondRuntime,
)
from number_compiler.hashlife.interfaces.diamond_kernel_bridge import (
    from_expression,
    input_variable,
    to_expression,
)
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID


def fixture() -> tuple[DiamondRuntime, ActionProgramID]:
    ledger = ResourceLedger()
    compiler = LazyCompiler(ledger)
    atom = compiler.atom(BaseBlockEffect(3))
    source = SourceGeometry(
        ledger, ExactSource((1,), 3, blank=5, extent=2, alphabet_size=5)
    )
    source.span((1,), 5, 2)
    runtime = DiamondRuntime(compiler, source)
    return runtime, runtime.actions.intern(atom)


@pytest.mark.parametrize("input_side", [0, 1])
@pytest.mark.parametrize("constant", [False, True])
def test_primitive_function_roundtrip_is_same_canonical_action(
    input_side: int, constant: bool
) -> None:
    runtime, action = fixture()
    arena, kernels = runtime.boundaries, runtime.kernels
    input_size = arena._domain_size(action, input_side)
    output_size = arena._domain_size(action, 1 - input_side)
    assert input_size is not None and output_size is not None
    values = [
        arena.literal(
            action, 1 - input_side, 1 if constant else (i * 3 + 1) % output_size
        )
        for i in range(input_size)
    ]
    function = arena.finite_function(values, action, input_side)
    signature = arena.action(function).signature
    assert signature is not None
    port, variable = input_variable(arena, action, input_side)
    expression = to_expression(arena, function, port)
    assert from_expression(arena, expression, signature, port) == function
    for value in range(input_size):
        variables = {
            port.__class__(
                port.time,
                port.side,
                port.role,
                port.bit + len(kernels.expression(variable).bits) - 1 - bit,
            ): bool(value & (1 << bit))
            for bit in range(len(kernels.expression(variable).bits))
        }
        actual = kernels.evaluate(expression, variables)
        assert actual == arena.state(values[value]).literal
    if constant:
        assert function == arena.constant(values[0], action, input_side)
    assert all(row.accounting_delta == 0 for row in runtime.ledger.inventory())


def test_same_ledger_distinct_kernel_arenas_have_distinct_domain_owners() -> None:
    from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena

    ledger = ResourceLedger()
    first, second = DiamondKernelArena(ledger), DiamondKernelArena(ledger)
    a, b = first.intern(BaseBlockEffect(10)), second.intern(BaseBlockEffect(10))
    assert a != b
    assert first.kernel(a).left == second.kernel(b).left
    assert first.kernel(a).left is not second.kernel(b).left
    assert all(row.accounting_delta == 0 for row in ledger.inventory())
