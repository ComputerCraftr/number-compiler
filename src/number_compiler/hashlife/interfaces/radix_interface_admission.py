"""Read-only admission of closed division functions over their full domain."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FinitePort,
    FunctionSignature,
    SemanticNode,
    SemanticTerminal,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.radix_division import SymbolicBinaryDivisionEffect
from number_compiler.arithmetic.radix_port_functions import RadixPortFunction

if TYPE_CHECKING:
    from number_compiler.hashlife.interfaces.diamond_quotient import (
        DiamondQuotientArena,
        MacroComponents,
        MacroInterface,
    )


def _is_constant(function: RadixPortFunction, value: int) -> bool:
    return function.kind == "constant" and function.value == value


def _validate_channel_roles(values: tuple[object, ...]) -> None:
    functions = tuple(value for value in values if type(value) is RadixPortFunction)
    if len(functions) != 13:
        raise ValueError("numeric division requires all thirteen arithmetic channels")
    for function in functions:
        function.__post_init__()
    left, right, output, activity, first, last, extent = functions[:7]
    halo_left, halo_right, growth, termination, normalization, frame = functions[7:]
    if not _is_constant(left, 0) or right.kind != "carry":
        raise ValueError("numeric division has invalid directional transfer channels")
    if any(
        function.kind != "output" and not _is_constant(function, 2)
        for function in (output, halo_left, halo_right)
    ):
        raise ValueError("numeric division has invalid output or halo channels")
    if any(
        function.kind != "active" and not _is_constant(function, 0)
        for function in (activity, first, last, extent, growth)
    ):
        raise ValueError("numeric division has invalid activity summary channels")
    if termination.kind != "inactive" and not _is_constant(termination, 1):
        raise ValueError("numeric division has an invalid termination channel")
    if not _is_constant(normalization, 0) or not _is_constant(frame, 0):
        raise ValueError("numeric division has invalid normalization or frame channels")


def _admissibility_root(
    arena: DiamondQuotientArena,
    signature: FunctionSignature,
    right: FinitePort,
) -> int:
    if type(right) is not FinitePort:
        raise TypeError("numeric division requires a finite right port")
    bits = right.bits
    cardinality = right.cardinality
    one = arena.functions.keys.get(
        SemanticNode(signature, terminal=SemanticTerminal("atom", 1))
    )
    if one is None:
        raise ValueError("numeric interface has no certified true predicate")
    if cardinality == 1 << bits:
        return one
    invalid = arena.functions.keys.get(
        SemanticNode(signature, terminal=SemanticTerminal("invalid"))
    )
    if invalid is None:
        raise ValueError("numeric interface has no certified terminal predicates")
    current = {0: invalid, 1: one}
    for bit in range(bits - 1, -1, -1):
        divisor = 1 << bit
        limits = {cardinality // divisor, (cardinality + divisor - 1) // divisor}
        following: dict[int, int] = {}
        variable = PortVariable(0, 1, "tile-right", bit)
        for limit in limits:
            low = current.get((limit + 1) // 2)
            high = current.get(limit // 2)
            if low is None or high is None:
                raise ValueError("numeric admissibility threshold is not closed")
            result = (
                low
                if low == high
                else arena.functions.keys.get(
                    SemanticNode(signature, variable, low, high)
                )
            )
            if result is None:
                raise ValueError(
                    "numeric interface has no certified full-domain predicate"
                )
            following[limit] = result
        current = following
    result = current.get(cardinality)
    if result is None:
        raise ValueError("numeric admissibility omitted its complete port domain")
    return result


def validate_radix_components(
    arena: DiamondQuotientArena, interface: MacroInterface, components: MacroComponents
) -> None:
    values = components.functions()
    if not any(type(value) is RadixPortFunction for value in values):
        return
    if not all(type(value) is RadixPortFunction for value in values):
        raise ValueError("numeric division requires all thirteen arithmetic channels")
    _validate_channel_roles(values)
    first = values[0]
    assert type(first) is RadixPortFunction
    radix = first.radix
    expected = SymbolicBinaryDivisionEffect(radix).canonical_key()
    behavior = interface.kernel.behavior
    from number_compiler.hashlife.execution.tile_kernel import _CONTRACT

    if behavior != (_CONTRACT, expected):
        raise ValueError(
            "numeric division functions require their exact kernel certificate"
        )
    left, right = interface.inputs
    if left.variable != PortVariable(
        0, 0, "tile-left", 0
    ) or right.variable != PortVariable(0, 1, "tile-right", 0):
        raise ValueError("numeric division requires its declared directional roles")
    if any(
        type(value) is RadixPortFunction and value.radix != radix for value in values
    ):
        raise ValueError("numeric division components have different moduli")
    # Reconstruct the canonical predicate key bottom-up.  Only the floor and
    # ceiling threshold survive at each bit, so validation retains two small
    # maps rather than a depth-sized pending/done graph.
    signature = FunctionSignature(interface.inputs, BOOL)
    if interface.admissible.local_id != _admissibility_root(arena, signature, right):
        raise ValueError("numeric interface cannot silently change admissibility")


__all__ = ["validate_radix_components"]
