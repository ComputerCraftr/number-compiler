"""Factored physical-Collatz output consumer for tile interfaces.

The low-side state already records which physical branch is active.  After
that geometry has been consumed, the odd ``3*n+1`` branch is a function of
the left carry state alone, while the even ``n/2`` branch consumes the one
right-neighbour symbol.  Keeping that choice explicit avoids publishing the
old joint ``left x right`` leaf table and gives temporal composition the
smallest exact consumer functions from its first generation onward.
"""

from __future__ import annotations

from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.diamond_kernel import PrimitiveKernel
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitFunctionArena,
    FactoredFunctionID,
)
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect


def collatz_physical_leaf_output(
    bits: BitFunctionArena,
    kernel: PrimitiveKernel,
    symbol: int,
    ports: tuple[FinitePort, ...],
    left_port: FinitePort,
    right_port: FinitePort,
    output_sort: AtomSort,
) -> FactoredFunctionID:
    """Compile the exact physical output after its branch geometry is known."""
    if type(bits) is not BitFunctionArena:
        raise TypeError("physical Collatz output requires the shared bit arena")
    if type(kernel.effect) is not CollatzPhysicalBlockEffect:
        raise ValueError("physical Collatz output requires its primitive kernel")
    expected_left = PortVariable(0, 0, "tile-left", 0)
    expected_right = PortVariable(0, 1, "tile-right", 0)
    if (
        type(symbol) is not int
        or not 0 <= symbol <= kernel.blank
        or type(ports) is not tuple
        or len(ports) != 2
        or left_port not in ports
        or right_port not in ports
        or left_port.variable != expected_left
        or right_port.variable != expected_right
        or left_port.cardinality != 6
        or right_port.cardinality != 3
        or output_sort.cardinality != 3
    ):
        raise ValueError("physical Collatz output requires its exact finite ports")

    effect = kernel.effect
    left = bits.variable(ports, left_port)
    right = bits.variable(ports, right_port)
    consumers = tuple(effect.output_consumer(state, symbol) for state in range(6))
    local = bits.map_atoms(
        left, output_sort, tuple(value for _uses_right, value in consumers)
    )
    shifted = bits.map_atoms(right, output_sort, (0, 1, 2))
    consumes_right = bits.map_atoms(
        left, BOOL, tuple(int(uses_right) for uses_right, _value in consumers)
    )
    result = bits.select(consumes_right, shifted, local)
    bits.ledger.bump("collatz_physical_factored_output_compilations")
    bits.ledger.bump("collatz_physical_joint_output_tables_elided")
    return result


__all__ = ["collatz_physical_leaf_output"]
