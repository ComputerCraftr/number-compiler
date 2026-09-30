"""Composition on one declared primitive port, without intermediate ITE DAGs.

The alternatives are the immutable primitive carry states, never coordinates
or temporal histories. Only the completed reduced function is interned.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import Literal

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    TransferSummaryID,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.diamond_kernel import (
    DiamondKernelArena,
    FiniteExpression,
    PrimitiveKernel,
)
from number_compiler.hashlife.interfaces.diamond_kernel_bridge import (
    _valid_argument,
    input_expression,
    observation_inputs,
    scan_primitive_support,
    substitution_bindings,
)
from number_compiler.resources.ledger import OwnedMemo


@dataclass(frozen=True, slots=True)
class UnaryComposition:
    kernel: ActionProgramID
    side: int
    before: TransferSummaryID
    after: TransferSummaryID
    port: PortVariable


@dataclass(frozen=True, slots=True)
class UnaryKernelApplication:
    input_kernel: ActionProgramID
    input_side: int
    port: PortVariable
    kernel: ActionProgramID
    operation: Literal["advance", "emit"]
    side: int
    arguments: tuple[TransferSummaryID, ...]


class PrimitiveUnaryFunctions:
    def __init__(self, kernels: DiamondKernelArena) -> None:
        self.kernels, self.ledger = kernels, kernels.ledger
        self.ledger.register_execution_root(self)
        self.owner = self.ledger.register(
            f"diamond-unary-{len(self.ledger.inventory())}", "unary_function_memo"
        )
        self._memo: OwnedMemo[
            UnaryComposition | UnaryKernelApplication, TransferSummaryID
        ] = OwnedMemo(self.ledger, self.owner, evictable=True)

    def compose(
        self,
        kernel: ActionProgramID,
        side: int,
        before: TransferSummaryID,
        after: TransferSummaryID,
        port: PortVariable,
    ) -> TransferSummaryID:
        primitive = self.kernels.kernel(kernel)
        a, b = self.kernels.expression(before), self.kernels.expression(after)
        if (
            type(side) is not int
            or side not in (0, 1)
            or type(port) is not PortVariable
        ):
            raise ValueError("invalid primitive function interface")
        domain = len(primitive.domain(BoundarySide(side)))
        if a.domain != domain:
            raise ValueError(
                "substitution does not preserve the declared primitive port"
            )
        key = UnaryComposition(kernel, side, before, after, port)
        self.ledger.bump("unary_function_composition_requests")
        cached = self._memo.get(key)
        if cached is not None:
            self.ledger.bump("unary_function_composition_hits")
            return cached
        width = (domain - 1).bit_length()
        variables = {
            PortVariable(port.time, port.side, port.role, port.bit + bit)
            for bit in range(width)
        }
        scan_primitive_support(
            self.kernels,
            [*a.bits, *b.bits],
            variables,
            "unary_function_admission",
            "unary composition contains another input port",
        )
        answer = self.kernels.substitute(
            after, substitution_bindings(self.kernels, domain, port, before)
        )
        self._memo[key] = answer
        self.ledger.bump("unary_function_composition_evaluations")
        return answer

    def mapped(
        self,
        input_kernel: ActionProgramID,
        input_side: int,
        port: PortVariable,
        kernel: ActionProgramID,
        operation: Literal["advance", "emit"],
        side: int,
        arguments: tuple[TransferSummaryID, ...],
    ) -> TransferSummaryID:
        source, target = self.kernels.kernel(input_kernel), self.kernels.kernel(kernel)
        expressions = tuple(self.kernels.expression(argument) for argument in arguments)
        if (
            type(input_side) is not int
            or input_side not in (0, 1)
            or type(side) is not int
            or side not in (0, 1)
            or type(port) is not PortVariable
            or operation not in ("advance", "emit")
        ):
            raise ValueError("invalid mapped primitive interface")
        domain = len(source.domain(BoundarySide(input_side)))
        expected = (
            (len(target.domain(BoundarySide(side))), target.blank + 1)
            if operation == "advance"
            else (target.left_count, target.blank + 1, target.right_count)
        )
        if tuple(expression.domain for expression in expressions) != expected:
            raise ValueError("mapped primitive arguments have incompatible domains")
        key = UnaryKernelApplication(
            input_kernel, input_side, port, kernel, operation, side, arguments
        )
        self.ledger.bump("unary_kernel_application_requests")
        cached = self._memo.get(key)
        if cached is not None:
            self.ledger.bump("unary_kernel_application_hits")
            return cached
        width = (domain - 1).bit_length()
        variables = {
            PortVariable(port.time, port.side, port.role, port.bit + bit)
            for bit in range(width)
        }
        scan_primitive_support(
            self.kernels,
            [bit for expression in expressions for bit in expression.bits],
            variables,
            "unary_function_admission",
            "mapped primitive contains another input port",
        )
        answer = self._mapped_correlated(
            domain, port, target, operation, BoundarySide(side), expressions
        )
        self._memo[key] = answer
        self.ledger.bump("unary_kernel_application_evaluations")
        return answer

    def _mapped_correlated(
        self,
        domain: int,
        port: PortVariable,
        target: PrimitiveKernel,
        operation: Literal["advance", "emit"],
        side: BoundarySide,
        expressions: tuple[FiniteExpression, ...],
    ) -> TransferSummaryID:
        """Compose one primitive with correlated finite arguments by BDD cofactoring.

        The product walk is bounded before any Boolean result nodes are published.
        If correlated support exceeds a small multiple of the primitive input
        universe, fall back to the old exact finite-domain reducer; this prevents
        a symbolic product from becoming a larger hidden workspace than the
        finite port it was supposed to replace.
        """
        if type(target) is not PrimitiveKernel or type(side) is not BoundarySide:
            raise TypeError(
                "correlated primitive reduction requires an admitted kernel"
            )
        if any(type(expression) is not FiniteExpression for expression in expressions):
            raise TypeError(
                "correlated primitive reduction requires finite expressions"
            )
        nodes = tuple(expressions)
        widths = tuple(len(expression.bits) for expression in nodes)
        roots = tuple(
            self.kernels.functions._resolve(bit)
            for expression in nodes
            for bit in expression.bits
        )
        output_domain = (
            len(target.domain(side)) if operation == "advance" else target.blank + 1
        )
        output_width = (output_domain - 1).bit_length()
        functions = self.kernels.functions
        terminals: dict[tuple[int, ...], tuple[int, ...]] = {}
        splits: dict[
            tuple[int, ...], tuple[PortVariable, tuple[int, ...], tuple[int, ...]]
        ] = {}
        scheduled: set[tuple[int, ...]] = {roots}
        stack: list[tuple[int, ...]] = [roots]
        visits = terminal_evaluations = 0
        peak = 1
        source_width = (domain - 1).bit_length()
        product_limit = max(1024, 4 * (1 << source_width))
        overflow = False
        while stack:
            peak = max(peak, len(stack) + len(terminals) + len(splits))
            key = stack.pop()
            if key in terminals or key in splits:
                continue
            visits += 1
            variables = [
                functions._nodes[index].variable for index in key if index >= 2
            ]
            if not variables:
                values: list[int] = []
                offset = 0
                admissible = True
                for width, expression in zip(widths, nodes, strict=True):
                    value = sum(key[offset + bit] << bit for bit in range(width))
                    offset += width
                    values.append(value)
                    admissible &= value < expression.domain
                if admissible:
                    terminal_evaluations += 1
                    value = (
                        target.advance(side, values[0], values[1])
                        if operation == "advance"
                        else target.emit(values[0], values[1], values[2])
                    )
                    self.ledger.observe_arithmetic(value)
                else:
                    value = 0
                terminals[key] = tuple(
                    (value >> bit) & 1 for bit in range(output_width)
                )
            else:
                variable = min(
                    candidate for candidate in variables if candidate is not None
                )
                low = tuple(
                    functions._nodes[index].low
                    if index >= 2 and functions._nodes[index].variable == variable
                    else index
                    for index in key
                )
                high = tuple(
                    functions._nodes[index].high
                    if index >= 2 and functions._nodes[index].variable == variable
                    else index
                    for index in key
                )
                splits[key] = variable, low, high
                for child in (high, low):
                    if child not in scheduled:
                        scheduled.add(child)
                        stack.append(child)
            if len(terminals) + len(splits) > product_limit:
                overflow = True
                break
        self.ledger.bump("unary_correlated_cofactor_visits", visits)
        self.ledger.bump("unary_correlated_terminal_evaluations", terminal_evaluations)
        old_peak = self.ledger.counters.get("unary_correlated_workspace_peak", 0)
        self.ledger.bump("unary_correlated_workspace_peak", max(0, peak - old_peak))
        if overflow:
            self.ledger.bump("unary_correlated_fallbacks")

            def evaluate(code: int) -> int:
                inputs = observation_inputs(domain, port, code)
                values = tuple(
                    self.kernels.evaluate(argument, inputs)
                    for argument in (
                        self.kernels._intern_expression(expression)
                        for expression in nodes
                    )
                )
                if operation == "advance":
                    return target.advance(side, values[0], values[1])
                return target.emit(values[0], values[1], values[2])

            return self._reduce(domain, output_domain, port, evaluate)
        # Every split removes the least remaining ROBDD variable from the
        # correlated tuple.  Its children therefore either terminate or have
        # a strictly greater least variable.  Evaluating split records in
        # reverse variable order is a deterministic topological order and,
        # unlike the old shared-child DFS ready markers, cannot publish a
        # parent before a child reached from another branch has a result.
        results = dict(terminals)
        for key in sorted(splits, key=lambda item: splits[item][0], reverse=True):
            variable, low, high = splits[key]
            results[key] = tuple(
                functions._intern(variable, a, b)
                for a, b in zip(results[low], results[high], strict=True)
            )
        answer = self.kernels._intern_expression(
            FiniteExpression(
                output_domain,
                tuple(functions._handle(bit) for bit in results[roots]),
            )
        )
        source_argument = input_expression(self.kernels, domain, port)
        return self.kernels.choose(
            _valid_argument(self.kernels, source_argument),
            answer,
            self.kernels.constant(output_domain, 0),
        )

    def _reduce(
        self,
        domain: int,
        output_domain: int,
        port: PortVariable,
        evaluate: Callable[[int], int],
    ) -> TransferSummaryID:
        functions = self.kernels.functions
        width = (domain - 1).bit_length()
        output_width = (output_domain - 1).bit_length()
        frames: list[tuple[int, int, tuple[TransferSummaryID, ...] | None]] = []
        depth = code = 0
        while True:
            if code < domain and depth < width:
                frames.append((depth, code, None))
                peak = self.ledger.counters.get("unary_function_workspace_peak", 0)
                self.ledger.bump(
                    "unary_function_workspace_peak", max(0, len(frames) - peak)
                )
                depth += 1
                continue
            value = 0
            if code < domain:
                value = evaluate(code)
                self.ledger.observe_arithmetic(value)
                self.ledger.bump("unary_function_port_evaluations")
            result = tuple(
                functions.constant(bool(value & (1 << bit)))
                for bit in range(output_width)
            )
            while frames:
                position, prefix, lower = frames.pop()
                if lower is None:
                    frames.append((position, prefix, result))
                    depth, code = position + 1, prefix | (1 << (width - 1 - position))
                    break
                variable = PortVariable(
                    port.time, port.side, port.role, port.bit + position
                )
                result = tuple(
                    functions._handle(
                        functions._intern(variable, low.local_id, high.local_id)
                    )
                    for low, high in zip(lower, result, strict=True)
                )
            else:
                return self.kernels._intern_expression(
                    FiniteExpression(output_domain, result)
                )
