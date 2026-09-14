"""Parametric spatial parent transfers for two complete primitive interfaces.

The four retained functions are A's two boundary transfers and B's transfer on
A's output in each direction. They contain finite port functions, not emitted
symbols. The coordinate-parametric output program remains a separate action.
"""

from __future__ import annotations

from collections.abc import Generator, MutableMapping, MutableSequence
from dataclasses import dataclass

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
    TransferSummaryID,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.actions.diamond_actions import CellID
from number_compiler.hashlife.execution.continuations.diamond_context_program import (
    ContextObservation,
    ContextProgramArena,
    ContextProgramID,
)
from number_compiler.hashlife.execution.continuations.diamond_tasks import (
    PairSummary,
    Result,
    Task,
)
from number_compiler.hashlife.interfaces.diamond_boundary import (
    BoundaryActionArena,
    BoundaryStateID,
)
from number_compiler.hashlife.interfaces.diamond_kernel_bridge import (
    from_expression,
    input_expression,
    observation_inputs,
    substitution_bindings,
    to_expression,
)

LEFT_A = PortVariable(0, 0, "diamond-pair-left-a", 0)
RIGHT_A = PortVariable(0, 1, "diamond-pair-right-a", 0)
LEFT_B = PortVariable(0, 0, "diamond-pair-left-b", 0)
RIGHT_B = PortVariable(0, 1, "diamond-pair-right-b", 0)


@dataclass(frozen=True, slots=True)
class PairMacroRecord:
    action: ActionProgramID
    left_transfer: TransferSummaryID
    right_transfer: TransferSummaryID
    left_context: ContextProgramID
    right_context: ContextProgramID

    def __post_init__(self) -> None:
        if (
            type(self.action) is not ActionProgramID
            or self.action.kind != "diamond-action"
        ):
            raise ValueError("pair macro requires a scoped temporal action")
        functions = (self.left_transfer, self.right_transfer)
        if any(
            type(function) is not TransferSummaryID
            or function.kind != "diamond-finite-expression"
            or function.owner is not self.left_transfer.owner
            for function in functions
        ):
            raise ValueError(
                "pair macro components require one finite expression arena"
            )
        if any(
            type(program) is not ContextProgramID
            or program.kind != "diamond-context-program"
            or program.owner is not self.left_context.owner
            for program in (self.left_context, self.right_context)
        ):
            raise ValueError("pair macro contexts require one finite program arena")


@dataclass(frozen=True, slots=True)
class PairMacroKey:
    action: ActionProgramID
    cell: CellID


class PrimitivePairMacros:
    """Compile each demanded source parent once, independently of bound states."""

    def __init__(self, boundaries: BoundaryActionArena) -> None:
        self.boundaries = boundaries
        self.actions, self.kernels, self.cells = (
            boundaries.temporals,
            boundaries.kernels,
            boundaries.cells,
        )
        self.ledger = boundaries.ledger
        self.contexts = ContextProgramArena(boundaries)
        self.unary = self.contexts.unary
        self.ledger.register_execution_root(self)
        self.token = ArenaToken("diamond-pair-macros")
        prefix = f"diamond-pair-macros-{len(self.ledger.inventory())}"
        self._node_owner = self.ledger.register(
            prefix + "-programs", "macro_transfer_program"
        )
        self._index_owner = self.ledger.register(
            prefix + "-program-ids", "macro_transfer_program_interner"
        )
        self._binding_owner = self.ledger.register(
            prefix + "-bindings", "macro_transfer_memo"
        )
        self._nodes: MutableSequence[PairMacroRecord] = self.ledger.make_list(
            self._node_owner
        )
        self._ids: MutableMapping[PairMacroRecord, TransferSummaryID] = (
            self.ledger.make_dict(self._index_owner)
        )
        self._bindings: MutableMapping[PairMacroKey, TransferSummaryID] = (
            self.ledger.make_dict(self._binding_owner)
        )
        self.ledger.register_container(
            self._binding_owner,
            self._bindings,
            payloads=lambda: self._bindings.items(),
            evict=self._evict_bindings,
        )

    def _evict_bindings(self) -> None:
        count = len(self._bindings)
        self._bindings.clear()
        self.ledger.release(self._binding_owner, entries=count)

    def supports(self, action: ActionProgramID) -> bool:
        node = self.actions.resolve(action)
        return node.kind == "compose" and all(
            self.actions.node(self.actions.reference(child)).kind == "atom"
            for child in (node.first, node.second)
        )

    def resolve(self, summary: TransferSummaryID) -> PairMacroRecord:
        if type(summary) is not TransferSummaryID:
            raise ValueError("expected a pair-macro effect ID")
        summary.validate(self.token, "diamond-pair-macro", size=len(self._nodes))
        return self._nodes[summary.local_id]

    def _intern(self, record: PairMacroRecord) -> TransferSummaryID:
        found = self._ids.get(record)
        if found is not None:
            self.ledger.bump("pair_macro_program_interner_hits")
            return found
        self.ledger.reserve_many(((self._node_owner, 1, 1), (self._index_owner, 1, 0)))
        result = TransferSummaryID(self.token, "diamond-pair-macro", len(self._nodes))
        self._nodes.append(record)
        self._ids[record] = result
        self.ledger.bump("pair_macro_program_interner_evaluations")
        return result

    def _publish(self, key: PairMacroKey, record: PairMacroRecord) -> TransferSummaryID:
        result = self._ids.get(record)
        reservations = [(self._binding_owner, 1, 0)]
        if result is None:
            reservations.extend(((self._node_owner, 1, 1), (self._index_owner, 1, 0)))
        self.ledger.reserve_many(tuple(reservations))
        if result is None:
            result = TransferSummaryID(
                self.token, "diamond-pair-macro", len(self._nodes)
            )
            self._nodes.append(record)
            self._ids[record] = result
            self.ledger.bump("pair_macro_program_interner_evaluations")
        else:
            self.ledger.bump("pair_macro_program_interner_hits")
        self._bindings[key] = result
        return result

    def _interfaces(
        self, action: ActionProgramID
    ) -> tuple[ActionProgramID, ActionProgramID, ActionProgramID, ActionProgramID]:
        if not self.supports(action):
            raise ValueError("pair macro requires two primitive temporal children")
        node = self.actions.node(action)
        first, second = (
            self.actions.reference(node.first),
            self.actions.reference(node.second),
        )
        return (
            first,
            second,
            self.kernels.intern(self.actions.primitive(first)),
            self.kernels.intern(self.actions.primitive(second)),
        )

    def _replace(
        self,
        expression: TransferSummaryID,
        replacements: tuple[tuple[PortVariable, int, TransferSummaryID], ...],
    ) -> TransferSummaryID:
        bindings = {}
        for port, domain, value in replacements:
            bindings.update(substitution_bindings(self.kernels, domain, port, value))
        return self.kernels.substitute(expression, bindings)

    def cache_probe(
        self, action: ActionProgramID, cell: CellID
    ) -> TransferSummaryID | None:
        if not self.supports(action):
            raise ValueError("pair macro requires primitive temporal children")
        source_admission = self._require_source(cell)
        node = self.actions.node(action)
        original = self.cells.source_geometry._construction.source
        if (node.base, node.blank) != (original.base, original.blank):
            raise ValueError("macro and original source have incompatible alphabets")
        self._record_source_admission(source_admission)
        self.ledger.bump("macro_transfer_requests")
        found = self._bindings.get(PairMacroKey(action, cell))
        if found is not None:
            self.ledger.bump("macro_transfer_cache_hits")
        return found

    def _require_source(self, cell: CellID) -> tuple[int, int, int, int]:
        self.cells.require_original(cell)
        return 1, 1, 0, 0

    def _record_source_admission(self, stats: tuple[int, int, int, int]) -> None:
        visits, unique, pending_peak, workspace_peak = stats
        self.ledger.bump("spatial_source_admission_frame_visits", visits)
        self.ledger.bump("spatial_source_admission_unique_visits", unique)
        for counter, value in (
            ("spatial_source_admission_pending_peak", pending_peak),
            ("spatial_source_admission_workspace_peak", workspace_peak),
            ("spatial_source_admission_unique_peak", unique),
        ):
            self.ledger.bump(
                counter, max(0, value - self.ledger.counters.get(counter, 0))
            )

    def build_children(self, cell: CellID) -> tuple[CellID, CellID]:
        node = self.cells.resolve(cell)
        if node.kind not in ("source", "join"):
            raise ValueError("parametric source macros cannot contain future images")
        return self.cells.split(cell)

    def _leaf(self, action: ActionProgramID, cell: CellID) -> PairMacroRecord:
        _, _, a_id, _ = self._interfaces(action)
        a = self.kernels.kernel(a_id)
        original_symbol = self.cells.source_symbol(cell)
        symbol = self.kernels.constant(a.blank + 1, original_symbol)
        left = input_expression(self.kernels, a.left_count, LEFT_A)
        right = input_expression(self.kernels, a.right_count, RIGHT_A)
        context = self.contexts.leaf(action, original_symbol)
        self.ledger.bump("pair_macro_leaf_evaluations")
        return PairMacroRecord(
            action,
            self.kernels.advance_expression(a_id, BoundarySide.LEFT, left, symbol),
            self.kernels.advance_expression(a_id, BoundarySide.RIGHT, right, symbol),
            context,
            context,
        )

    def _parent(
        self, action: ActionProgramID, left: PairMacroRecord, right: PairMacroRecord
    ) -> PairMacroRecord:
        if left.action != action or right.action != action:
            raise ValueError("spatial macro children have another temporal interface")
        _, _, a_id, _ = self._interfaces(action)
        middle_left, middle_right = left.left_transfer, right.right_transfer
        context = self.contexts.join(
            action, left.left_context, right.left_context, middle_left, middle_right
        )
        self.ledger.bump("pair_macro_parent_evaluations")
        return PairMacroRecord(
            action,
            self.unary.compose(a_id, 0, middle_left, right.left_transfer, LEFT_A),
            self.unary.compose(a_id, 1, middle_right, left.right_transfer, RIGHT_A),
            context,
            context,
        )

    def compose(
        self, action: ActionProgramID, left: TransferSummaryID, right: TransferSummaryID
    ) -> TransferSummaryID:
        first, second = self.resolve(left), self.resolve(right)
        self.actions.resolve(action)
        return self._intern(self._parent(action, first, second))

    def summary(self, action: ActionProgramID, cell: CellID) -> TransferSummaryID:
        found = self.cache_probe(action, cell)
        if found is not None:
            return found
        stack = [(cell, False, True)]
        while stack:
            peak = self.ledger.counters.get("pair_macro_stack_peak", 0)
            self.ledger.bump("pair_macro_stack_peak", max(0, len(stack) - peak))
            current, ready, probed = stack.pop()
            key = PairMacroKey(action, current)
            if (
                not ready
                and not probed
                and self.cache_probe(action, current) is not None
            ):
                continue
            node = self.cells.resolve(current)
            if node.level:
                left, right = self.build_children(current)
                if not ready:
                    stack.extend(
                        (
                            (current, True, True),
                            (right, False, False),
                            (left, False, False),
                        )
                    )
                    continue
                record = self._parent(
                    action,
                    self.resolve(self._bindings[PairMacroKey(action, left)]),
                    self.resolve(self._bindings[PairMacroKey(action, right)]),
                )
            else:
                record = self._leaf(action, current)
            self._publish(key, record)
            self.ledger.bump("macro_transfer_evaluations")
        return self._bindings[PairMacroKey(action, cell)]

    def _validate_state(
        self, state: BoundaryStateID, action: ActionProgramID, side: int
    ) -> int:
        value = self.boundaries.state(state)
        if (value.action, value.side) != (action, side) or value.literal < 0:
            raise ValueError(
                "macro observation has another primitive boundary interface"
            )
        return value.literal

    def apply_context_program(
        self,
        summary: TransferSummaryID,
        left: BoundaryStateID,
        right: BoundaryStateID,
        incoming: BoundaryStateID,
        side: int,
    ) -> Generator[Task, Result, Result]:
        record = self.resolve(summary)
        first, second, a_id, b_id = self._interfaces(record.action)
        if type(side) is not int or side not in (0, 1):
            raise ValueError("invalid context direction")
        left_value = self._validate_state(left, first, 0)
        right_value = self._validate_state(right, first, 1)
        value = self._validate_state(incoming, second, side)
        a, b = self.kernels.kernel(a_id), self.kernels.kernel(b_id)
        domain = b.left_count if side == 0 else b.right_count
        expression = record.left_context if side == 0 else record.right_context
        self.ledger.bump("pair_macro_context_applications")
        output = yield ContextObservation(
            expression,
            self.kernels.constant(a.left_count, left_value),
            self.kernels.constant(a.right_count, right_value),
            self.kernels.constant(domain, value),
            side,
        )
        assert type(output) is TransferSummaryID
        return self.boundaries.literal(second, side, self.kernels.evaluate(output, {}))

    def advance_program(
        self, action: ActionProgramID, cell: CellID, state: BoundaryStateID, side: int
    ) -> Generator[Task, Result, Result]:
        value = self.boundaries.state(state)
        self.actions.resolve(action)
        if (
            type(side) is not int
            or side not in (0, 1)
            or (value.action, value.side) != (action, side)
        ):
            raise ValueError("macro application has another boundary interface")
        if value.anchor is None or value.continuation is None:
            raise ValueError("macro application requires a composed boundary")
        summary = yield PairSummary(action, cell)
        assert type(summary) is TransferSummaryID
        record = self.resolve(summary)
        first, _, a_id, _ = self._interfaces(action)
        a = self.kernels.kernel(a_id)
        anchor = self._validate_state(value.anchor, first, side)
        port = RIGHT_A if side == 0 else LEFT_A
        function = to_expression(self.boundaries, value.continuation, port)
        function = self.unary.compose(
            a_id,
            1 - side,
            record.right_transfer if side == 0 else record.left_transfer,
            function,
            port,
        )
        anchor_domain = a.left_count if side == 0 else a.right_count
        anchor_expression = self.kernels.constant(anchor_domain, anchor)
        variable = input_expression(
            self.kernels, a.right_count if side == 0 else a.left_count, port
        )
        left, right = (
            (anchor_expression, variable)
            if side == 0
            else (variable, anchor_expression)
        )
        output = yield ContextObservation(
            record.left_context if side == 0 else record.right_context,
            left,
            right,
            function,
            side,
        )
        assert type(output) is TransferSummaryID
        signature = self.boundaries.action(value.continuation).signature
        assert signature is not None
        continuation = from_expression(self.boundaries, output, signature, port)
        next_anchor = record.left_transfer if side == 0 else record.right_transfer
        inputs = observation_inputs(
            anchor_domain, LEFT_A if side == 0 else RIGHT_A, anchor
        )
        target = self.boundaries.literal(
            first, side, self.kernels.evaluate(next_anchor, inputs)
        )
        self.ledger.bump("pair_macro_boundary_applications")
        return self.boundaries.pair(action, side, target, continuation)

    def _standalone(self, program: Generator[Task, Result, Result]) -> BoundaryStateID:
        """Compatibility driver for direct finite-interface tests and clients.

        Production yields these dependencies into DiamondRuntime's one scheduler.
        """
        try:
            task = next(program)
            while True:
                match task:
                    case PairSummary():
                        result = self.summary(task.action, task.cell)
                    case ContextObservation():
                        result = self.contexts.execute(
                            task.program,
                            task.left,
                            task.right,
                            task.incoming,
                            task.side,
                        )
                    case _:
                        raise AssertionError(
                            "unexpected primitive interface dependency"
                        )
                task = program.send(result)
        except StopIteration as completed:
            value = completed.value
            if type(value) is not BoundaryStateID:
                raise AssertionError(
                    "finite interface did not produce a boundary state"
                )
            return value
        finally:
            program.close()

    def advance(
        self, action: ActionProgramID, cell: CellID, state: BoundaryStateID, side: int
    ) -> BoundaryStateID:
        return self._standalone(self.advance_program(action, cell, state, side))

    def apply_context(
        self,
        summary: TransferSummaryID,
        left: BoundaryStateID,
        right: BoundaryStateID,
        incoming: BoundaryStateID,
        side: int,
    ) -> BoundaryStateID:
        return self._standalone(
            self.apply_context_program(summary, left, right, incoming, side)
        )
