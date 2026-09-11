"""Admission of closed carry functions without Boolean domain expansion."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.carry.reverse_port_functions import (
    ReversePortCodec,
    ReversePortFunction,
)
from number_compiler.arithmetic.contracts.block_effect import _effect_key
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FunctionSignature,
    SemanticNode,
    SemanticTerminal,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.radix_port_functions import RadixPortFunction

if TYPE_CHECKING:
    from number_compiler.hashlife.interfaces.diamond_quotient import (
        DiamondQuotientArena,
        MacroComponents,
        MacroInterface,
    )


def has_closed_components(components: MacroComponents) -> bool:
    return any(
        type(value) in (RadixPortFunction, ReversePortFunction)
        for value in components.functions()
    )


def validate_reverse_channel_roles(values: tuple[object, ...]) -> None:
    """Validate closed channel meaning without evaluating semantic functions."""
    if len(values) != 13 or not all(
        type(value) is ReversePortFunction for value in values
    ):
        raise ValueError(
            "reverse carry interfaces require all thirteen closed channels"
        )
    functions = tuple(value for value in values if type(value) is ReversePortFunction)
    (
        boundary_left,
        boundary_right,
        output,
        activity,
        first_active,
        last_active,
        extent,
        halo_left,
        halo_right,
        growth,
        termination,
        normalization,
        frame,
    ) = functions
    base = boundary_left.base
    for value in functions:
        value.__post_init__()
        if value.base != base:
            raise ValueError("reverse carry functions have different alphabets")
    if boundary_left.kind != "left-transfer" or boundary_right.kind != "right-transfer":
        raise ValueError("reverse carry interface changed its directional transfers")
    if any(value.kind != "output" for value in (output, halo_left, halo_right)):
        raise ValueError("reverse carry interface changed its output or halo channels")
    summaries = (activity, first_active, last_active, extent, growth, termination)
    if any(value.kind != "predicate" for value in summaries):
        raise ValueError("reverse carry interface changed its summary predicates")
    mask = (1 << ReversePortCodec(base).left_count) - 1
    if (
        extent.truth_bits != activity.truth_bits
        or growth.truth_bits != activity.truth_bits
    ):
        raise ValueError("reverse carry interface has inconsistent activity summaries")
    if first_active.truth_bits & ~activity.truth_bits:
        raise ValueError("reverse first-active channel exceeds interval activity")
    if last_active.truth_bits & ~activity.truth_bits:
        raise ValueError("reverse last-active channel exceeds interval activity")
    if termination.truth_bits != (~activity.truth_bits) & mask:
        raise ValueError("reverse termination is not the activity complement")
    for value in (normalization, frame):
        if value.kind != "constant" or value.value != 0:
            raise ValueError("reverse normalization and frame channels must be neutral")


def _full_domain_root(arena: DiamondQuotientArena, signature: FunctionSignature) -> int:
    result = arena.functions.keys.get(
        SemanticNode(signature, terminal=SemanticTerminal("atom", 1))
    )
    invalid = arena.functions.keys.get(
        SemanticNode(signature, terminal=SemanticTerminal("invalid"))
    )
    if result is None or invalid is None:
        raise ValueError("closed carry interface has no admitted domain predicate")
    for port in reversed(signature.inputs):
        if port.cardinality == 1 << port.bits:
            continue
        current = {0: invalid, 1: result}
        for bit in range(port.bits - 1, -1, -1):
            scale = 1 << bit
            following: dict[int, int] = {}
            variable = PortVariable(
                port.variable.time, port.variable.side, port.variable.role, bit
            )
            for limit in (
                port.cardinality // scale,
                (port.cardinality + scale - 1) // scale,
            ):
                low, high = current[(limit + 1) // 2], current[limit // 2]
                found = (
                    low
                    if low == high
                    else arena.functions.keys.get(
                        SemanticNode(signature, variable, low, high)
                    )
                )
                if found is None:
                    raise ValueError("closed carry domain predicate is incomplete")
                following[limit] = found
            current = following
        result = current[port.cardinality]
    return result


def validate_closed_components(
    arena: DiamondQuotientArena,
    interface: MacroInterface,
    components: MacroComponents,
) -> None:
    values = components.functions()
    if any(type(value) is RadixPortFunction for value in values):
        from number_compiler.hashlife.interfaces.radix_interface_admission import (
            validate_radix_components,
        )

        validate_radix_components(arena, interface, components)
        return
    if not any(type(value) is ReversePortFunction for value in values):
        return
    if not all(type(value) is ReversePortFunction for value in values):
        raise ValueError(
            "reverse carry interfaces require all thirteen closed channels"
        )
    from number_compiler.hashlife.execution.tile_kernel import _CONTRACT

    first = values[0]
    assert type(first) is ReversePortFunction
    base = first.base
    if interface.kernel.behavior != (_CONTRACT, _effect_key(BaseBlockEffect(base))):
        raise ValueError("reverse carry functions require their exact kernel identity")
    left, right = interface.inputs
    if left.variable != PortVariable(
        0, 0, "tile-left", 0
    ) or right.variable != PortVariable(0, 1, "tile-right", 0):
        raise ValueError("reverse carry functions require their directional port roles")
    validate_reverse_channel_roles(values)
    # Reuse the published full-domain constant. Creating a speculative
    # predicate here would do semantic work on every warm interner lookup.
    node = arena.functions.resolve(interface.admissible)
    if node.signature != FunctionSignature(interface.inputs, BOOL):
        raise ValueError("reverse carry admissibility has another signature")
    # Exact canonical root identity is checked by the existing constant
    # interner, not sampled evaluation of a few port assignments.
    if interface.admissible.local_id != _full_domain_root(arena, node.signature):
        raise ValueError("reverse carry interface changed its admissible port domain")


__all__ = [
    "has_closed_components",
    "validate_closed_components",
    "validate_reverse_channel_roles",
]
