"""Finite-interface conversion between boundary MTDDs and Boolean components.

Only a declared primitive input/codomain is accepted. Traversal visits decision
nodes, not spatial cells or temporal generations, and uses explicit stacks.
"""

from __future__ import annotations

from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    TransferSummaryID,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.diamond_boundary import (
    BoundaryActionArena,
    BoundaryActionID,
    BoundaryFunctionSignature,
)
from number_compiler.hashlife.interfaces.diamond_kernel import (
    DiamondKernelArena,
    FiniteExpression,
)


def _variable(port: PortVariable, width: int, bit: int) -> PortVariable:
    return PortVariable(port.time, port.side, port.role, port.bit + width - 1 - bit)


def input_expression(
    kernels: DiamondKernelArena, domain: int, port: PortVariable
) -> TransferSummaryID:
    """Use MSB-first variable order to agree with the boundary MTDD order."""
    if (
        type(domain) is not int
        or not 1 <= domain <= 1 << 64
        or type(port) is not PortVariable
    ):
        raise ValueError("invalid primitive input variable")
    width = (domain - 1).bit_length()
    return kernels._intern_expression(
        FiniteExpression(
            domain,
            tuple(
                kernels.functions.variable(_variable(port, width, bit))
                for bit in range(width)
            ),
        )
    )


def input_variable(
    boundaries: BoundaryActionArena, action: ActionProgramID, side: int
) -> tuple[PortVariable, TransferSummaryID]:
    domain = boundaries._domain_size(action, side)
    if domain is None:
        raise ValueError("only primitive input domains have finite variables")
    port = PortVariable(0, side, "diamond-argument", 0)
    return port, input_expression(boundaries.kernels, domain, port)


def substitution_bindings(
    kernels: DiamondKernelArena,
    domain: int,
    port: PortVariable,
    replacement: TransferSummaryID,
) -> dict[PortVariable, TransferSummaryID]:
    node = kernels.expression(replacement)
    if node.domain != domain:
        raise ValueError("replacement finite input domain disagrees")
    width = len(node.bits)
    return {
        _variable(port, width, bit): expression
        for bit, expression in enumerate(node.bits)
    }


def observation_inputs(
    domain: int, port: PortVariable, value: int
) -> dict[PortVariable, bool]:
    """A bounded transient port assignment, without specializing the function."""
    if (
        type(domain) is not int
        or not 1 <= domain <= 1 << 64
        or type(port) is not PortVariable
        or type(value) is not int
        or not 0 <= value < domain
    ):
        raise ValueError("invalid finite observation input")
    width = (domain - 1).bit_length()
    return {
        _variable(port, width, bit): bool(value & (1 << bit)) for bit in range(width)
    }


def to_expression(
    boundaries: BoundaryActionArena, function: BoundaryActionID, port: PortVariable
) -> TransferSummaryID:
    if type(port) is not PortVariable:
        raise ValueError("invalid primitive input variable")
    kernels = boundaries.kernels
    signature = boundaries.action(function).signature
    if signature is None or signature.input_size is None:
        raise ValueError("conversion requires a complete primitive input domain")
    output_size = boundaries._domain_size(
        signature.output_action, signature.output_side
    )
    if output_size is None:
        raise ValueError("conversion requires a primitive codomain")
    width = (signature.input_size - 1).bit_length()
    values: dict[BoundaryActionID, TransferSummaryID] = {}
    stack = [(function, False)]
    while stack:
        peak = kernels.ledger.counters.get("diamond_finite_bridge_stack_peak_frames", 0)
        kernels.ledger.bump(
            "diamond_finite_bridge_stack_peak_frames", max(0, len(stack) - peak)
        )
        handle, ready = stack.pop()
        if handle in values:
            continue
        kernels.ledger.bump("diamond_finite_bridge_visits")
        node = boundaries.action(handle)
        if node.signature != signature:
            raise ValueError("mixed boundary signatures")
        if node.kind == "constant":
            assert node.value is not None
            value = boundaries.state(node.value)
            if value.literal < 0:
                raise ValueError("structured output is not a finite primitive value")
            values[handle] = kernels.constant(output_size, value.literal)
        elif node.kind == "decision":
            assert node.low is not None and node.high is not None
            if not ready:
                stack.extend(((handle, True), (node.high, False), (node.low, False)))
            else:
                condition = kernels.functions.variable(_variable(port, width, node.bit))
                values[handle] = kernels.choose(
                    condition, values[node.high], values[node.low]
                )
        else:
            raise ValueError("only reduced primitive-domain functions can be converted")
    peak = kernels.ledger.counters.get("diamond_finite_bridge_peak_result_entries", 0)
    kernels.ledger.bump(
        "diamond_finite_bridge_peak_result_entries", max(0, len(values) - peak)
    )
    return values[function]


def _valid_argument(
    kernels: DiamondKernelArena, argument: TransferSummaryID
) -> TransferSummaryID:
    value = kernels.expression(argument)
    functions = kernels.functions
    equal, less = functions.constant(True), functions.constant(False)
    if value.domain == 1 << len(value.bits):
        return equal
    for index in range(len(value.bits) - 1, -1, -1):
        bit = value.bits[index]
        if value.domain & (1 << index):
            step = functions.choose(
                equal, functions.negate(bit), functions.constant(False)
            )
            less = functions.choose(step, functions.constant(True), less)
            equal = functions.choose(bit, equal, functions.constant(False))
        else:
            equal = functions.choose(bit, functions.constant(False), equal)
    return less


def from_expression(
    boundaries: BoundaryActionArena,
    expression: TransferSummaryID,
    signature: BoundaryFunctionSignature,
    port: PortVariable,
) -> BoundaryActionID:
    kernels = boundaries.kernels
    node = kernels.expression(expression)
    expected = boundaries._signature(
        signature.input_action,
        signature.input_side,
        signature.output_action,
        signature.output_side,
    )
    output_size = boundaries._domain_size(
        signature.output_action, signature.output_side
    )
    if (
        expected != signature
        or signature.input_size is None
        or output_size != node.domain
    ):
        raise ValueError("expression does not match a complete primitive interface")
    width = (signature.input_size - 1).bit_length()
    if type(port) is not PortVariable:
        raise ValueError("invalid primitive input variable")
    variables = {_variable(port, width, bit): False for bit in range(width)}
    # Reject foreign variables before conversion can publish any interner node.
    checked: set[TransferSummaryID] = set()
    pending = list(node.bits)
    admission_visits = admission_peak = 0
    while pending:
        admission_visits += 1
        admission_peak = max(admission_peak, len(pending))
        bit = pending.pop()
        if bit in checked:
            continue
        checked.add(bit)
        decision = kernels.functions._nodes[kernels.functions._resolve(bit)]
        if decision.variable is not None:
            if decision.variable not in variables:
                raise ValueError("expression contains a foreign finite input variable")
            pending.extend(
                (
                    kernels.functions._handle(decision.low),
                    kernels.functions._handle(decision.high),
                )
            )
    kernels.ledger.bump("diamond_finite_bridge_admission_visits", admission_visits)
    peak = kernels.ledger.counters.get("diamond_finite_bridge_admission_stack_peak", 0)
    kernels.ledger.bump(
        "diamond_finite_bridge_admission_stack_peak", max(0, admission_peak - peak)
    )
    peak = kernels.ledger.counters.get("diamond_finite_bridge_admission_peak_ids", 0)
    kernels.ledger.bump(
        "diamond_finite_bridge_admission_peak_ids", max(0, len(checked) - peak)
    )
    argument = input_expression(kernels, signature.input_size, port)
    default = kernels.evaluate(expression, variables)
    normalized = kernels.choose(
        _valid_argument(kernels, argument),
        expression,
        kernels.constant(node.domain, default),
    )
    roots = kernels.expression(normalized).bits
    results: dict[tuple[TransferSummaryID, ...], BoundaryActionID] = {}
    splits: dict[
        tuple[TransferSummaryID, ...],
        tuple[int, tuple[TransferSummaryID, ...], tuple[TransferSummaryID, ...]],
    ] = {}
    stack = [(roots, False)]
    while stack:
        peak = kernels.ledger.counters.get("diamond_finite_bridge_stack_peak_frames", 0)
        kernels.ledger.bump(
            "diamond_finite_bridge_stack_peak_frames", max(0, len(stack) - peak)
        )
        current, ready = stack.pop()
        if current in results:
            continue
        kernels.ledger.bump("diamond_finite_bridge_visits")
        decisions = [
            kernels.functions._nodes[kernels.functions._resolve(bit)] for bit in current
        ]
        if all(decision.variable is None for decision in decisions):
            value = sum(bit.local_id << index for index, bit in enumerate(current))
            state = boundaries.literal(
                signature.output_action, signature.output_side, value
            )
            results[current] = boundaries.constant(
                state, signature.input_action, signature.input_side
            )
            continue
        if not ready:
            variable = min(
                decision.variable
                for decision in decisions
                if decision.variable is not None
            )
            if variable not in variables:
                raise ValueError("expression contains a foreign finite input variable")
            logical_bit = width - 1 - (variable.bit - port.bit)
            low = tuple(
                kernels.functions._handle(decision.low)
                if decision.variable == variable
                else bit
                for decision, bit in zip(decisions, current, strict=True)
            )
            high = tuple(
                kernels.functions._handle(decision.high)
                if decision.variable == variable
                else bit
                for decision, bit in zip(decisions, current, strict=True)
            )
            splits[current] = logical_bit, low, high
            stack.extend(((current, True), (high, False), (low, False)))
        else:
            logical_bit, low, high = splits[current]
            results[current] = boundaries.decision(
                logical_bit, results[low], results[high]
            )
    for name, count in (
        ("diamond_finite_bridge_peak_result_entries", len(results)),
        ("diamond_finite_bridge_peak_split_entries", len(splits)),
    ):
        peak = kernels.ledger.counters.get(name, 0)
        kernels.ledger.bump(name, max(0, count - peak))
    return results[roots]
