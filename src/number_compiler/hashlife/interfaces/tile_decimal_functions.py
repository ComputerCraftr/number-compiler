"""Reduced exact decimal output law for one reverse-add pair cell.

The local ``F5 x F2 x F2`` law lives in :class:`BaseBlockEffect`. This
compiler publishes its reduced Boolean decision function directly, without
retaining a Cartesian output table or constructing a larger arithmetic DAG
that is discarded after reduction.
"""

from __future__ import annotations

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.functions.finite_function_types import (
    AtomSort,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.diamond_kernel import PrimitiveKernel
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitFunctionArena,
    FactoredFunctionID,
    _Circuit,
)


def decimal_leaf_output(
    bits: BitFunctionArena,
    kernel: PrimitiveKernel,
    symbol: int,
    ports: tuple[FinitePort, ...],
    left_port: FinitePort,
    right_port: FinitePort,
    output_sort: AtomSort,
) -> FactoredFunctionID:
    """Compile one exact output law with bounded, immediately reduced work."""
    if type(bits) is not BitFunctionArena:
        raise TypeError("decimal output requires the shared factored-function arena")
    if type(kernel.effect) is not BaseBlockEffect or kernel.effect.base != 10:
        raise ValueError("decimal output requires the primitive base-ten kernel")
    if type(symbol) is not int or not 0 <= symbol <= kernel.blank:
        raise ValueError("decimal output symbol lies outside the kernel alphabet")
    expected_left = PortVariable(0, 0, "tile-left", 0)
    expected_right = PortVariable(0, 1, "tile-right", 0)
    if (
        type(ports) is not tuple
        or len(ports) != 2
        or left_port not in ports
        or right_port not in ports
        or left_port.variable != expected_left
        or right_port.variable != expected_right
        or left_port.cardinality != kernel.left_count
        or right_port.cardinality != kernel.right_count
        or output_sort.cardinality != kernel.blank + 1
    ):
        raise ValueError("decimal output requires its exact two-sided signature")
    circuit = _Circuit(bits.functions, ports)
    variables = tuple(
        PortVariable(port.variable.time, port.variable.side, port.variable.role, bit)
        for port in (left_port, right_port)
        for bit in range(port.bits)
    )
    pending: list[tuple[int, int, int, bool]] = [(0, 0, 0, False)]
    values: list[tuple[int, ...]] = []
    width = (output_sort.cardinality - 1).bit_length()
    while pending:
        depth, left, right, ready = pending.pop()
        if depth == len(variables):
            if left >= kernel.left_count or right >= kernel.right_count:
                output = 0
            else:
                output = kernel.emit(left, symbol, right)
            values.append(
                tuple(
                    circuit.one if output & (1 << bit) else circuit.zero
                    for bit in range(width)
                )
            )
            continue
        if ready:
            circuit.join_branch(values, variables[depth])
            continue
        variable = variables[depth]
        if variable.side == left_port.variable.side:
            high_left, high_right = left | (1 << variable.bit), right
        else:
            high_left, high_right = left, right | (1 << variable.bit)
        pending.extend(
            (
                (depth, left, right, True),
                (depth + 1, high_left, high_right, False),
                (depth + 1, left, right, False),
            )
        )
    if len(values) != 1:
        raise AssertionError("decimal output compiler produced multiple roots")
    result = circuit.normalized(
        FunctionSignature(ports, output_sort),
        values[0],
        circuit.admitted(),
    )
    return bits._publish(circuit, (result,))[0]


__all__ = ["decimal_leaf_output"]
