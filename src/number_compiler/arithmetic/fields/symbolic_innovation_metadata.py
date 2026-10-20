"""Bounded validation and ledger sizing for symbolic innovation nodes."""

from __future__ import annotations

from number_compiler.arithmetic.contracts.input_validation import is_object_tuple
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.fields.radial_innovation import (
    InnovationCharted,
    InnovationInterval,
    InnovationNode,
    InnovationRadial,
    InnovationScale,
)

MAX_PRIMITIVE_IDENTITY_UNITS = 256
MAX_PRIMITIVE_IDENTITY_DEPTH = 32


def validate_bounded_primitive_identity(identity: SemanticIdentity) -> None:
    """Validate the finite structural envelope of a primitive identity."""
    pending: list[tuple[object, int]] = [(identity, 0)]
    seen: set[int] = set()
    identities: list[SemanticIdentity] = []
    units = 0
    while pending:
        value, depth = pending.pop()
        units += 1
        if units > MAX_PRIMITIVE_IDENTITY_UNITS:
            raise ValueError("primitive innovation identity exceeds its finite bound")
        if depth > MAX_PRIMITIVE_IDENTITY_DEPTH:
            raise ValueError("primitive innovation identity exceeds its depth bound")
        if value is None or type(value) is bool:
            continue
        if type(value) is int:
            if abs(value).bit_length() > 64:
                raise ValueError("primitive innovation identity embeds a wide integer")
            continue
        if isinstance(value, (str, bytes)):
            if len(value) > MAX_PRIMITIVE_IDENTITY_UNITS:
                raise ValueError("primitive innovation identity embeds a wide scalar")
            continue
        object_id = id(value)
        if object_id in seen:
            continue
        seen.add(object_id)
        if is_object_tuple(value):
            if type(value) is not tuple:
                raise TypeError(
                    "primitive innovation identity has a nonsemantic payload"
                )
            for child_index in range(len(value)):
                child: object = value[child_index]
                pending.append((child, depth + 1))
        elif type(value) is SemanticIdentity:
            identities.append(value)
            pending.append((value.behavior, depth + 1))
        else:
            raise TypeError("primitive innovation identity has a nonsemantic payload")
    # Digest validation runs only after the complete reachable identity has
    # passed the finite structural bound above.
    for value in identities:
        value.validate()


def integer_limb_units(*values: int) -> int:
    """Return 64-bit ledger units for retained exact-integer metadata."""
    retained_bits = sum(max(1, abs(value).bit_length()) for value in values)
    return max(1, (retained_bits + 63) // 64)


def innovation_node_units(node: InnovationNode) -> int:
    """Return ledger units retained by one node, including wide integers."""
    if isinstance(node, InnovationInterval):
        return integer_limb_units(node.length)
    if isinstance(node, InnovationRadial):
        return integer_limb_units(node.multiplier.no_growth, node.multiplier.growth)
    if isinstance(node, InnovationCharted):
        return integer_limb_units(
            node.chart.slope,
            node.chart.offset,
            node.chart.extent_scale,
            node.chart.growth_scale,
        )
    if isinstance(node, InnovationScale):
        return integer_limb_units(node.coefficient)
    return 1


__all__ = [
    "MAX_PRIMITIVE_IDENTITY_DEPTH",
    "MAX_PRIMITIVE_IDENTITY_UNITS",
    "innovation_node_units",
    "integer_limb_units",
    "validate_bounded_primitive_identity",
]
