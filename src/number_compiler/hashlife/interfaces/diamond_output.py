"""Complete finite kernel output functions, independent of source coordinates.

Each result is a function of one free primitive-alphabet symbol. A cache binding
contains fixed kernel actions and finite ports, never a cell or observed digit.
Higher temporal interfaces stay in the executable continuation program.
"""

from __future__ import annotations

from collections.abc import Generator
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.scoped_handles import TransferSummaryID
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.execution.continuations.diamond_tasks import (
    OutputFunction,
    Result,
    Task,
)
from number_compiler.hashlife.interfaces.diamond_kernel_bridge import (
    _valid_argument,
    input_expression,
    observation_inputs,
)
from number_compiler.resources.ledger import OwnedMemo

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )


ORIGINAL_SYMBOL = PortVariable(0, 0, "diamond-original-symbol", 0)


def _expression(result: Result) -> TransferSummaryID:
    if type(result) is not TransferSummaryID:
        raise AssertionError("expected a complete finite output function")
    return result


class DiamondOutputFunctions:
    def __init__(self, runtime: DiamondRuntime) -> None:
        self.runtime, self.ledger = runtime, runtime.ledger
        self.ledger.register_execution_root(self)
        self.owner = self.ledger.register(
            f"diamond-output-{len(self.ledger.inventory())}", "output_function_memo"
        )
        self.bindings: OwnedMemo[OutputFunction, TransferSummaryID] = OwnedMemo(
            self.ledger, self.owner, evictable=True
        )

    def compile(self, task: OutputFunction) -> Generator[Task, Result, Result]:
        runtime, kernels = self.runtime, self.runtime.kernels
        domain = runtime.cells.source_geometry._construction.source.blank + 1
        variable = input_expression(kernels, domain, ORIGINAL_SYMBOL)
        node = runtime.actions.node(task.action)
        if node.kind == "identity":
            return variable
        primitive = runtime.kernel(task.action)
        left, right = (
            runtime.boundaries.state(task.left),
            runtime.boundaries.state(task.right),
        )
        result = kernels.emit_expression(
            runtime.primitive_ids[task.action],
            kernels.constant(primitive.left_count, left.literal),
            variable,
            kernels.constant(primitive.right_count, right.literal),
        )
        # A finite-domain function uses f(0) for unused binary codes, matching
        # boundary MTDDs. Impossible codes must not hide a true constant port.
        default = kernels.evaluate(
            result, observation_inputs(domain, ORIGINAL_SYMBOL, 0)
        )
        return kernels.choose(
            _valid_argument(kernels, variable),
            result,
            kernels.constant(domain, default),
        )
        yield  # The shared scheduler also accepts dependency-free programs.

    def constant(self, function: TransferSummaryID) -> int | None:
        kernels = self.runtime.kernels
        expression = kernels.expression(function)
        self.ledger.bump("primitive_output_constant_checks")
        value = 0
        for position, bit in enumerate(expression.bits):
            index = kernels.functions._resolve(bit)
            self.ledger.bump("primitive_output_constant_bit_checks")
            if index >= 2:
                return None
            value = self.ledger.observe_arithmetic(value | (index << position))
        if value >= expression.domain:
            raise AssertionError("constant function left its finite output domain")
        return value

    def observe(self, function: TransferSummaryID, symbol: int) -> int:
        kernels = self.runtime.kernels
        expression = kernels.expression(function)
        self.ledger.bump("output_function_observations")
        return kernels.evaluate(
            function, observation_inputs(expression.domain, ORIGINAL_SYMBOL, symbol)
        )
