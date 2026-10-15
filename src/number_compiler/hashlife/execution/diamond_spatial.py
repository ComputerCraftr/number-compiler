"""State-parametric primitive spatial transfers over original source parents."""

from __future__ import annotations

from collections.abc import Generator
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BoundarySide, _effect_key
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    TransferSummaryID,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.execution.continuations.diamond_context_program import (
    LEFT_A,
    RIGHT_A,
)
from number_compiler.hashlife.execution.continuations.diamond_tasks import (
    Result,
    SpatialSummary,
    Task,
)
from number_compiler.hashlife.interfaces.diamond_boundary import BoundaryStateID
from number_compiler.hashlife.interfaces.diamond_kernel_bridge import (
    input_expression,
    observation_inputs,
    scan_primitive_support,
)
from number_compiler.hashlife.interfaces.diamond_output import _expression
from number_compiler.resources.ledger import OwnedMemo
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )


class PrimitiveSpatialTransfers:
    """Source bindings are separate from canonical finite function identities."""

    def __init__(self, runtime: DiamondRuntime) -> None:
        self.runtime, self.ledger = runtime, runtime.ledger
        self.ledger.register_execution_root(self)
        owner = self.ledger.register(
            f"diamond-spatial-{len(self.ledger.inventory())}", "primitive_spatial_memo"
        )
        self.bindings: OwnedMemo[SpatialSummary, TransferSummaryID] = OwnedMemo(
            self.ledger, owner, evictable=True
        )

    def validate(self, task: SpatialSummary) -> tuple[int, int, int, int]:
        runtime = self.runtime
        if (
            type(task) is not SpatialSummary
            or type(task.side) is not int
            or task.side not in (0, 1)
        ):
            raise ValueError("invalid primitive spatial interface")
        node = runtime.actions.resolve(task.action)
        source = runtime.cells.source_geometry._construction.source
        if node.kind != "atom" or (node.base, node.blank) != (
            source.base,
            source.blank,
        ):
            raise ValueError("spatial summary requires a matching primitive action")
        return runtime.pair_macros._require_source(task.cell)

    def compile(self, task: SpatialSummary) -> Generator[Task, Result, Result]:
        self.runtime.pair_macros._record_source_admission(self.validate(task))
        runtime, kernels = self.runtime, self.runtime.kernels
        primitive = runtime.kernel(task.action)
        kernel = runtime.primitive_ids[task.action]
        domain = len(primitive.domain(BoundarySide(task.side)))
        port = LEFT_A if task.side == 0 else RIGHT_A
        cell = runtime.cells.node(task.cell)
        if not cell.level:
            variable = input_expression(kernels, domain, port)
            symbol = kernels.constant(
                primitive.blank + 1, runtime.cells.source_symbol(task.cell)
            )
            result = kernels.advance_expression(
                kernel, BoundarySide(task.side), variable, symbol
            )
            self.ledger.bump(_execution_keys.PRIMITIVE_SPATIAL_LEAF_EVALUATIONS)
            return result
        left, right = runtime.cells.split(task.cell)
        before, after = (left, right) if task.side == 0 else (right, left)
        first = _expression((yield SpatialSummary(task.action, before, task.side)))
        second = _expression((yield SpatialSummary(task.action, after, task.side)))
        result = runtime.pair_macros.unary.compose(
            kernel, task.side, first, second, port
        )
        self.ledger.bump(_execution_keys.PRIMITIVE_SPATIAL_PARENT_EVALUATIONS)
        return result

    def observe(
        self,
        action: ActionProgramID,
        side: int,
        summary: TransferSummaryID,
        state: BoundaryStateID,
    ) -> BoundaryStateID:
        runtime = self.runtime
        runtime._validate_state(state, action, side)
        node = runtime.actions.resolve(action)
        source = runtime.cells.source_geometry._construction.source
        if node.kind != "atom" or (node.base, node.blank) != (
            source.base,
            source.blank,
        ):
            raise ValueError("spatial observation requires a matching primitive action")
        expression = runtime.kernels.expression(summary)
        # A valid literal state already has an admitted primitive interface.
        # Reading that existing kernel must not populate runtime.kernel's memo
        # before every supplied function and its free variables are validated.
        handle = runtime.kernels._kernel_ids.get(
            _effect_key(runtime.actions.primitive(action))
        )
        if handle is None:
            raise ValueError("literal state has no admitted primitive interface")
        primitive = runtime.kernels.kernel(handle)
        domain = len(primitive.domain(BoundarySide(side)))
        if expression.domain != domain:
            raise ValueError("spatial function has another boundary codomain")
        code = runtime.boundaries.state(state).literal
        port = LEFT_A if side == 0 else RIGHT_A
        allowed = {
            PortVariable(port.time, port.side, port.role, port.bit + bit)
            for bit in range((domain - 1).bit_length())
        }
        scan_primitive_support(
            runtime.kernels,
            list(expression.bits),
            allowed,
            "primitive_spatial_admission",
            "spatial function contains another input port",
        )
        value = runtime.kernels.evaluate(
            summary, observation_inputs(domain, port, code)
        )
        self.ledger.bump(_execution_keys.PRIMITIVE_SPATIAL_OBSERVATIONS)
        return runtime.boundaries.literal(action, side, value)
