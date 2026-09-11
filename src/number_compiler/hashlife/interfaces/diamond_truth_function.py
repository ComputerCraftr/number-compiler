"""Compile bounded kernel truth functions directly into Boolean action IDs.

Only original immutable primitive interfaces are enumerated. Each live result
is a tuple of at most64 Boolean function IDs, not a row of emitted symbols.
Intermediate Shannon nodes do not need finite-expression wrappers or general
ITE evaluation when their input variables are already strictly ordered.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Literal

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.scoped_handles import TransferSummaryID
from number_compiler.arithmetic.functions.finite_port_action import PortVariable

if TYPE_CHECKING:
    from number_compiler.hashlife.interfaces.diamond_kernel import (
        DiamondKernelArena,
        FiniteExpression,
        PrimitiveKernel,
    )


def compile_truth_function(
    arena: DiamondKernelArena,
    primitive: PrimitiveKernel,
    operation: Literal["advance", "emit"],
    side: BoundarySide,
    nodes: tuple[FiniteExpression, ...],
) -> TransferSummaryID:
    """Exact Shannon construction, including the invalid-code zero extension."""
    from number_compiler.hashlife.interfaces.diamond_kernel import FiniteExpression

    if (
        primitive.ledger is not arena.ledger
        or type(side) is not BoundarySide
        or not any(candidate is primitive for candidate in arena._kernels)
    ):
        raise ValueError("kernel truth compiler requires its admitted resource owner")
    if operation not in ("advance", "emit"):
        raise ValueError("unknown primitive operation")
    domains = (
        (len(primitive.domain(side)), primitive.blank + 1)
        if operation == "advance"
        else (primitive.left_count, primitive.blank + 1, primitive.right_count)
    )
    if (
        type(nodes) is not tuple
        or any(type(node) is not FiniteExpression for node in nodes)
        or tuple(node.domain for node in nodes) != domains
    ):
        raise ValueError("kernel truth compiler domains disagree")
    coordinates: list[tuple[PortVariable, int, int, TransferSummaryID]] = []
    values = [0] * len(nodes)
    ordered = True
    for argument, node in enumerate(nodes):
        for bit, condition in enumerate(node.bits):
            decision = arena.functions._nodes[arena.functions._resolve(condition)]
            if decision.variable is None:
                values[argument] |= condition.local_id << bit
            else:
                ordered = ordered and decision.low == 0 and decision.high == 1
                coordinates.append((decision.variable, argument, bit, condition))
    coordinates.sort(key=lambda coordinate: coordinate[:3])
    ordered = ordered and len({entry[0] for entry in coordinates}) == len(coordinates)
    domain = (
        len(primitive.domain(side)) if operation == "advance" else primitive.blank + 1
    )
    output_width = (domain - 1).bit_length()
    frames: list[tuple[int, tuple[int, ...] | None]] = []
    depth = 0
    while True:
        admissible = all(
            value < size for value, size in zip(values, domains, strict=True)
        )
        if admissible and depth < len(coordinates):
            frames.append((depth, None))
            arena.ledger.bump("diamond_kernel_shannon_branches")
            peak = arena.ledger.counters.get("diamond_kernel_shannon_peak_frames", 0)
            arena.ledger.bump(
                "diamond_kernel_shannon_peak_frames", max(0, len(frames) - peak)
            )
            depth += 1
            continue
        if admissible:
            arena.ledger.bump("diamond_kernel_shannon_leaf_evaluations")
            value = (
                primitive.advance(side, values[0], values[1])
                if operation == "advance"
                else primitive.emit(*values)
            )
        else:
            arena.ledger.bump("diamond_kernel_invalid_subtrees")
            value = 0
        result = tuple((value >> bit) & 1 for bit in range(output_width))
        while frames:
            position, lower = frames.pop()
            variable, argument, bit, condition = coordinates[position]
            if lower is None:
                frames.append((position, result))
                values[argument] = arena.ledger.observe_arithmetic(
                    values[argument] | (1 << bit)
                )
                depth = position + 1
                break
            values[argument] &= ~(1 << bit)
            if result != lower:
                if ordered:
                    result = tuple(
                        arena.functions._intern(variable, low, high)
                        for low, high in zip(lower, result, strict=True)
                    )
                    arena.ledger.bump("diamond_kernel_ordered_function_joins")
                else:
                    result = tuple(
                        arena.functions._resolve(
                            arena.functions.choose(
                                condition,
                                arena.functions._handle(high),
                                arena.functions._handle(low),
                            )
                        )
                        for low, high in zip(lower, result, strict=True)
                    )
        else:
            return arena._intern_expression(
                FiniteExpression(
                    domain,
                    tuple(arena.functions._handle(bit) for bit in result),
                )
            )
