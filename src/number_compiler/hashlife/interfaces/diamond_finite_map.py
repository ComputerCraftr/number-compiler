"""Admission of a finite map between two already declared primitive ports."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.scoped_handles import TransferSummaryID
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.execution.continuations.diamond_context_program import (
    LEFT_A,
    RIGHT_A,
)
from number_compiler.hashlife.interfaces.diamond_kernel_bridge import (
    _valid_argument,
    input_expression,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.interfaces.diamond_boundary_expr import (
        BoundaryExpressionArena,
        StateSort,
    )


def admit_map(
    arena: BoundaryExpressionArena,
    source: StateSort,
    target: StateSort,
    summary: TransferSummaryID,
) -> tuple[TransferSummaryID, int | None, bool]:
    """Validate before allocation, then normalize irrelevant input codes.

    Traversal and the ordinal check cover one immutable primitive domain. No
    composed boundary universe, spatial word, or temporal history is enumerated.
    """
    arena._validate_sort(source)
    arena._validate_sort(target)
    before, after = arena.primitive(source.action), arena.primitive(target.action)
    if before is None or after is None:
        raise ValueError("finite map requires two admitted primitive interfaces")
    if (before.base, before.blank) != (after.base, after.blank):
        raise ValueError("finite map primitive alphabets disagree")
    domain = len(before.domain(BoundarySide(source.side)))
    codomain = len(after.domain(BoundarySide(target.side)))
    kernels = arena.boundaries.kernels
    expression = kernels.expression(summary)
    if expression.domain != codomain:
        raise ValueError("finite map has another primitive codomain")
    port = LEFT_A if source.side == 0 else RIGHT_A
    width = (domain - 1).bit_length()
    allowed = {
        PortVariable(port.time, port.side, port.role, port.bit + bit)
        for bit in range(width)
    }
    functions = kernels.functions
    pending = list(expression.bits)
    checked: set[TransferSummaryID] = set()
    visits = 0
    while pending:
        bit = pending.pop()
        visits += 1
        if bit in checked:
            continue
        checked.add(bit)
        decision = functions._nodes[functions._resolve(bit)]
        if decision.variable is not None:
            if decision.variable not in allowed:
                raise ValueError("finite map contains another primitive input port")
            pending.extend(
                (functions._handle(decision.low), functions._handle(decision.high))
            )
    constant_value: int | None = None
    constant, identity, invalid = True, source == target, False
    reads = 0
    for code in range(1 << width):
        output = 0
        for bit_number, bit in enumerate(expression.bits):
            index = bit.local_id
            while index >= 2:
                decision = functions._nodes[index]
                assert decision.variable is not None
                bit_index = width - 1 - (decision.variable.bit - port.bit)
                index = decision.high if code & (1 << bit_index) else decision.low
                reads += 1
            output |= index << bit_number
        if code >= domain:
            invalid |= output != 0
            continue
        if output >= codomain:
            raise ValueError("finite map emits outside its primitive codomain")
        identity &= output == code
        if constant_value is None:
            constant_value = output
        constant &= constant_value == output
    arena.ledger.bump("boundary_expression_finite_admission_visits", visits)
    arena.ledger.bump("boundary_expression_finite_admission_value_visits", reads)
    if constant or identity:
        return summary, constant_value if constant else None, identity
    if invalid:
        argument = input_expression(kernels, domain, port)
        summary = kernels.choose(
            _valid_argument(kernels, argument), summary, kernels.constant(codomain, 0)
        )
        arena.ledger.bump("boundary_expression_finite_admissibility_normalizations")
    return summary, None, False
