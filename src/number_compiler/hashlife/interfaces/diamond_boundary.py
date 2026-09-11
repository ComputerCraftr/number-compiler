"""Scoped boundary values and domain-typed complete continuation functions.

Primitive domains can be reduced to finite decision diagrams. Higher domains
retain the exact bimachine substitution program, never an input/output word.
Constant reduction preserves the function's domain and codomain signature.
"""

from __future__ import annotations

from collections.abc import MutableMapping, MutableSequence
from dataclasses import dataclass
from typing import Literal

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaHandle,
    ArenaToken,
)
from number_compiler.hashlife.actions.diamond_actions import (
    CellID,
    FormalSymbolID,
    ImageCellArena,
    InputCellID,
    TemporalActionArena,
)
from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena


@dataclass(frozen=True, slots=True)
class BoundaryStateID(ArenaHandle):
    pass


@dataclass(frozen=True, slots=True)
class BoundaryActionID(ArenaHandle):
    pass


def _temporal_reference(value: ActionProgramID) -> None:
    if type(value) is not ActionProgramID or value.kind != "diamond-action":
        raise ValueError("expected a scoped temporal action")


def _direction(side: int) -> None:
    if type(side) is not int or side not in (0, 1):
        raise ValueError("invalid boundary direction")


@dataclass(frozen=True, slots=True)
class BoundaryStateNode:
    action: ActionProgramID
    side: int
    literal: int = -1
    anchor: BoundaryStateID | None = None
    continuation: BoundaryActionID | None = None

    def __post_init__(self) -> None:
        _temporal_reference(self.action)
        _direction(self.side)
        if type(self.literal) is not int or not -1 <= self.literal < 1 << 64:
            raise ValueError("invalid finite boundary literal")
        if self.literal >= 0:
            if self.anchor is not None or self.continuation is not None:
                raise ValueError("literal boundary cannot contain a continuation")
        elif (
            type(self.anchor) is not BoundaryStateID
            or type(self.continuation) is not BoundaryActionID
            or self.anchor.kind != "diamond-boundary-state"
            or self.continuation.kind != "diamond-boundary-action"
            or self.anchor.owner is not self.continuation.owner
        ):
            raise ValueError(
                "structured boundary requires scoped anchor and continuation"
            )


@dataclass(frozen=True, slots=True)
class ImageBinding:
    """Observation-only port binding; it is never an image-cell identity."""

    action: ActionProgramID
    cell: InputCellID
    left: BoundaryStateID
    right: BoundaryStateID

    def __post_init__(self) -> None:
        _temporal_reference(self.action)
        if not (
            (type(self.cell) is CellID and self.cell.kind == "diamond-cell")
            or (
                type(self.cell) is FormalSymbolID
                and self.cell.kind == "diamond-formal-symbol"
            )
        ):
            raise ValueError(
                "image binding requires a scoped cell or formal original symbol"
            )
        if (
            type(self.left) is not BoundaryStateID
            or type(self.right) is not BoundaryStateID
            or self.left.kind != "diamond-boundary-state"
            or self.right.kind != "diamond-boundary-state"
            or self.left.owner is not self.right.owner
        ):
            raise ValueError("image boundary ports require one owner")


@dataclass(frozen=True, slots=True)
class ContinuationStep:
    first: ActionProgramID
    second: ActionProgramID
    side: int
    previous: BoundaryActionID
    provider: ImageBinding
    anchor: BoundaryStateID

    def __post_init__(self) -> None:
        _temporal_reference(self.first)
        _temporal_reference(self.second)
        _direction(self.side)
        if (
            self.first.owner is not self.second.owner
            or type(self.provider) is not ImageBinding
        ):
            raise ValueError(
                "substitution requires a typed image and one temporal arena"
            )
        if (
            type(self.previous) is not BoundaryActionID
            or type(self.anchor) is not BoundaryStateID
            or self.previous.kind != "diamond-boundary-action"
            or self.anchor.kind != "diamond-boundary-state"
            or self.previous.owner is not self.anchor.owner
            or self.anchor.owner is not self.provider.left.owner
        ):
            raise ValueError("substitution boundary references require one owner")


@dataclass(frozen=True, slots=True)
class BoundaryFunctionSignature:
    input_action: ActionProgramID
    input_side: int
    output_action: ActionProgramID
    output_side: int
    input_size: int | None

    def __post_init__(self) -> None:
        _temporal_reference(self.input_action)
        _temporal_reference(self.output_action)
        _direction(self.input_side)
        _direction(self.output_side)
        if self.input_action.owner is not self.output_action.owner:
            raise ValueError("continuation interface requires one temporal arena")
        if self.input_size is not None and (
            type(self.input_size) is not int or not 1 <= self.input_size <= 1 << 64
        ):
            raise ValueError("invalid primitive-domain cardinality")


@dataclass(frozen=True, slots=True)
class ContinuationNode:
    kind: Literal["invalid", "constant", "decision", "substitution"]
    value: BoundaryStateID | None = None
    bit: int = -1
    low: BoundaryActionID | None = None
    high: BoundaryActionID | None = None
    step: ContinuationStep | None = None
    signature: BoundaryFunctionSignature | None = None

    def __post_init__(self) -> None:
        if (
            type(self.signature) is not BoundaryFunctionSignature
            or type(self.bit) is not int
        ):
            raise ValueError("continuation requires an admitted interface shape")
        if self.kind == "constant":
            valid = (
                type(self.value) is BoundaryStateID
                and self.value.kind == "diamond-boundary-state"
                and self.bit == -1
                and all(value is None for value in (self.low, self.high, self.step))
            )
        elif self.kind == "decision":
            valid = (
                self.bit >= 0
                and self.value is None
                and self.step is None
                and type(self.low) is BoundaryActionID
                and type(self.high) is BoundaryActionID
                and self.low.kind == self.high.kind == "diamond-boundary-action"
                and self.low.owner is self.high.owner
            )
        elif self.kind == "substitution":
            valid = (
                type(self.step) is ContinuationStep
                and self.bit == -1
                and all(value is None for value in (self.value, self.low, self.high))
            )
        elif self.kind == "invalid":
            valid = self.bit == -1 and all(
                value is None for value in (self.value, self.low, self.high, self.step)
            )
        else:
            valid = False
        if not valid:
            raise ValueError("invalid continuation constructor")


class BoundaryActionArena:
    """One owner for immutable boundary values and typed function DAGs."""

    def __init__(
        self,
        actions: TemporalActionArena,
        kernels: DiamondKernelArena,
        cells: ImageCellArena,
    ) -> None:
        if kernels.ledger is not actions.ledger or cells.actions is not actions:
            raise ValueError(
                "boundary arenas must share their action and resource owners"
            )
        self.temporals, self.kernels, self.cells = actions, kernels, cells
        self.ledger = actions.ledger
        self.ledger.register_execution_root(self)
        self.token = ArenaToken("diamond-boundaries")
        prefix = f"diamond-boundaries-{len(self.ledger.inventory())}"
        self.state_owner = self.ledger.register(prefix + "-states", "finite_port")
        self.state_key_owner = self.ledger.register(
            prefix + "-state-keys", "finite_port_interner"
        )
        self.action_owner = self.ledger.register(
            prefix + "-actions", "canonical_transfer"
        )
        self.action_key_owner = self.ledger.register(
            prefix + "-action-keys", "transfer_interner"
        )
        self.states: MutableSequence[BoundaryStateNode] = self.ledger.make_list(
            self.state_owner
        )
        self.state_keys: MutableMapping[BoundaryStateNode, BoundaryStateID] = (
            self.ledger.make_dict(self.state_key_owner)
        )
        self.actions: MutableSequence[ContinuationNode] = self.ledger.make_list(
            self.action_owner
        )
        self.action_keys: MutableMapping[ContinuationNode, BoundaryActionID] = (
            self.ledger.make_dict(self.action_key_owner)
        )

    @staticmethod
    def _side(side: int) -> None:
        _direction(side)

    def state(self, handle: BoundaryStateID) -> BoundaryStateNode:
        if type(handle) is not BoundaryStateID:
            raise ValueError("expected a diamond boundary state")
        handle.validate(self.token, "diamond-boundary-state", size=len(self.states))
        return self.states[handle.local_id]

    def action(self, handle: BoundaryActionID) -> ContinuationNode:
        if type(handle) is not BoundaryActionID:
            raise ValueError("expected a diamond boundary function")
        handle.validate(self.token, "diamond-boundary-action", size=len(self.actions))
        return self.actions[handle.local_id]

    def _domain_size(self, action: ActionProgramID, side: int) -> int | None:
        node = self.temporals.resolve(action)
        self._side(side)
        if node.kind == "identity":
            return 1
        if node.kind == "compose":
            return None
        primitive = self.kernels.kernel(
            self.kernels.intern(self.temporals.primitive(action))
        )
        return len(primitive.domain(BoundarySide(side)))

    def _signature(
        self,
        input_action: ActionProgramID,
        input_side: int,
        output_action: ActionProgramID,
        output_side: int,
    ) -> BoundaryFunctionSignature:
        first, second = (
            self.temporals.resolve(input_action),
            self.temporals.resolve(output_action),
        )
        self._side(input_side)
        self._side(output_side)
        if (
            first.kind != "identity"
            and second.kind != "identity"
            and (first.base, first.blank) != (second.base, second.blank)
        ):
            raise ValueError(
                "continuation domain and codomain have incompatible alphabets"
            )
        return BoundaryFunctionSignature(
            input_action,
            input_side,
            output_action,
            output_side,
            self._domain_size(input_action, input_side),
        )

    def _state(self, node: BoundaryStateNode) -> BoundaryStateID:
        found = self.state_keys.get(node)
        if found is not None:
            return found
        self.ledger.reserve_many(
            ((self.state_owner, 1, 1), (self.state_key_owner, 1, 0))
        )
        result = BoundaryStateID(self.token, "diamond-boundary-state", len(self.states))
        self.states.append(node)
        self.state_keys[node] = result
        return result

    def literal(
        self, action: ActionProgramID, side: int, value: int
    ) -> BoundaryStateID:
        self.temporals.resolve(action)
        self._side(side)
        if type(value) is not int or value < 0 or value.bit_length() > 64:
            raise ValueError("invalid primitive boundary state")
        size = self._domain_size(action, side)
        if size is None or value >= size:
            raise ValueError("literal outside complete primitive boundary domain")
        return self._state(BoundaryStateNode(action, side, value))

    def pair(
        self,
        action: ActionProgramID,
        side: int,
        anchor: BoundaryStateID,
        continuation: BoundaryActionID,
    ) -> BoundaryStateID:
        node, value, function = (
            self.temporals.resolve(action),
            self.state(anchor),
            self.action(continuation),
        )
        self._side(side)
        if node.kind != "compose":
            raise ValueError("structured boundaries require a composed action")
        first, second = (
            self.temporals.reference(node.first),
            self.temporals.reference(node.second),
        )
        if value.action != first or value.side != side:
            raise ValueError("structured boundary anchor has the wrong action or side")
        signature = function.signature
        if signature is None or (
            signature.input_action,
            signature.input_side,
            signature.output_action,
            signature.output_side,
        ) != (first, 1 - side, second, side):
            raise ValueError("structured boundary continuation has the wrong interface")
        if function.kind == "invalid":
            raise ValueError("an inadmissible argument sentinel is not a continuation")
        return self._state(
            BoundaryStateNode(action, side, anchor=anchor, continuation=continuation)
        )

    def _action(self, node: ContinuationNode) -> BoundaryActionID:
        found = self.action_keys.get(node)
        if found is not None:
            return found
        self.ledger.reserve_many(
            ((self.action_owner, 1, 1), (self.action_key_owner, 1, 0))
        )
        result = BoundaryActionID(
            self.token, "diamond-boundary-action", len(self.actions)
        )
        self.actions.append(node)
        self.action_keys[node] = result
        return result

    def constant(
        self, state: BoundaryStateID, input_action: ActionProgramID, input_side: int
    ) -> BoundaryActionID:
        output = self.state(state)
        signature = self._signature(
            input_action, input_side, output.action, output.side
        )
        return self._action(
            ContinuationNode("constant", value=state, signature=signature)
        )

    def decision(
        self, bit: int, low: BoundaryActionID, high: BoundaryActionID
    ) -> BoundaryActionID:
        first, second = self.action(low), self.action(high)
        signature = first.signature
        if (
            signature is None
            or signature != second.signature
            or signature.input_size is None
        ):
            raise ValueError(
                "decision children require the same complete primitive interface"
            )
        if (
            type(bit) is not int
            or not 0 <= bit < (signature.input_size - 1).bit_length()
        ):
            raise ValueError("invalid finite-domain decision bit")
        if any(
            child.kind == "decision" and child.bit >= bit for child in (first, second)
        ):
            raise ValueError(
                "decision variables must follow canonical descending order"
            )
        if low == high:
            return low
        return self._action(
            ContinuationNode(
                "decision", bit=bit, low=low, high=high, signature=signature
            )
        )

    def validate_binding(self, provider: ImageBinding) -> None:
        if type(provider) is not ImageBinding:
            raise ValueError("expected a parametric image binding")
        self.temporals.resolve(provider.action)
        self.cells.validate_input(provider.cell)
        left, right = self.state(provider.left), self.state(provider.right)
        if (left.action, left.side, right.action, right.side) != (
            provider.action,
            0,
            provider.action,
            1,
        ):
            raise ValueError("image ports do not match their action and direction")

    def substitution(self, step: ContinuationStep) -> BoundaryActionID:
        if type(step) is not ContinuationStep:
            raise ValueError("expected a continuation substitution")
        self.temporals.resolve(step.first)
        self.temporals.resolve(step.second)
        self._side(step.side)
        previous, anchor = self.action(step.previous), self.state(step.anchor)
        self.validate_binding(step.provider)
        expected = self._signature(step.first, 1 - step.side, step.second, step.side)
        if previous.signature != expected or previous.kind == "invalid":
            raise ValueError(
                "previous continuation does not match substituted interface"
            )
        if (anchor.action, anchor.side) != (step.first, step.side):
            raise ValueError("substitution anchor has the wrong first-action interface")
        return self._action(
            ContinuationNode("substitution", step=step, signature=expected)
        )

    def finite_function(
        self,
        values: list[BoundaryStateID],
        input_action: ActionProgramID,
        input_side: int,
    ) -> BoundaryActionID:
        """Reduce exactly one certified primitive domain, never a composed one."""
        size = self._domain_size(input_action, input_side)
        if size is None or len(values) != size:
            raise ValueError("finite function must cover its complete primitive domain")
        outputs = [self.state(value) for value in values]
        first = outputs[0]
        if any(
            (value.action, value.side) != (first.action, first.side)
            for value in outputs
        ):
            raise ValueError("finite function values have incompatible codomains")
        signature = self._signature(input_action, input_side, first.action, first.side)
        counters: dict[str, int] = {}

        def measure(name: str, value: int = 1) -> None:
            counters[name] = counters.get(name, 0) + value

        measure("boundary_function_reduction_requests")
        measure("boundary_function_reduction_evaluations")
        measure("boundary_function_domain_visits", len(values))
        staged: dict[ContinuationNode, BoundaryActionID] = {}
        new_nodes: list[ContinuationNode] = []

        def intern(node: ContinuationNode) -> BoundaryActionID:
            measure("boundary_function_candidate_requests")
            found = self.action_keys.get(node)
            if found is not None:
                measure("boundary_function_existing_node_hits")
            else:
                found = staged.get(node)
                if found is not None:
                    measure("boundary_function_staged_node_hits")
            if found is None:
                found = BoundaryActionID(
                    self.token,
                    "diamond-boundary-action",
                    len(self.actions) + len(new_nodes),
                )
                staged[node] = found
                new_nodes.append(node)
            return found

        def workspace(frontier: int, next_frontier: int = 0) -> None:
            # Slots in distinct algorithm work containers, including both
            # frontiers while a reduction level is being constructed.
            peak = self.ledger.counters.get(
                "boundary_function_workspace_peak", 0
            ) + counters.get("boundary_function_workspace_peak", 0)
            live = (
                frontier + next_frontier + len(new_nodes) + len(staged) + len(outputs)
            )
            measure("boundary_function_workspace_peak", max(0, live - peak))

        nodes: list[BoundaryActionID] = []
        for value in values:
            nodes.append(
                intern(ContinuationNode("constant", value=value, signature=signature))
            )
            workspace(len(nodes))
        width = 1 << (size - 1).bit_length()
        if width > size:
            # select validates admissibility before traversing even a constant.
            # A fixed extension by f(0) keeps equal functions canonical without
            # retaining artificial invalid branches in a constant function.
            nodes.extend([nodes[0]] * (width - size))
        workspace(len(nodes))
        bit = 0
        while len(nodes) > 1:
            measure("boundary_function_pair_reductions", len(nodes) // 2)
            reduced: list[BoundaryActionID] = []
            for i in range(0, len(nodes), 2):
                reduced.append(
                    nodes[i]
                    if nodes[i] == nodes[i + 1]
                    else intern(
                        ContinuationNode(
                            "decision",
                            bit=bit,
                            low=nodes[i],
                            high=nodes[i + 1],
                            signature=signature,
                        )
                    )
                )
                workspace(len(nodes), len(reduced))
            nodes = reduced
            bit += 1
        count = len(new_nodes)
        if nodes[0].local_id < len(self.actions):
            measure("boundary_function_result_alias_hits")
        self.ledger.reserve_many(
            ((self.action_owner, count, count), (self.action_key_owner, count, 0))
        )
        for name, amount in counters.items():
            self.ledger.bump(name, amount)
        for node in new_nodes:
            result = BoundaryActionID(
                self.token, "diamond-boundary-action", len(self.actions)
            )
            self.actions.append(node)
            self.action_keys[node] = result
        return nodes[0]

    def select(
        self, action: BoundaryActionID, argument: BoundaryStateID
    ) -> BoundaryStateID | None:
        state, node = self.state(argument), self.action(action)
        signature = node.signature
        if signature is None or (state.action, state.side) != (
            signature.input_action,
            signature.input_side,
        ):
            raise ValueError("argument belongs to another continuation domain")
        if (
            signature.input_size is not None
            and not 0 <= state.literal < signature.input_size
        ):
            raise ValueError("argument outside admissible primitive domain")
        while node.kind == "decision":
            if node.low is None or node.high is None:
                raise AssertionError("incomplete finite decision")
            self.ledger.bump("boundary_decision_visits")
            action = node.high if (state.literal >> node.bit) & 1 else node.low
            node = self.action(action)
        if node.kind == "invalid":
            raise ValueError("argument outside admissible primitive domain")
        return node.value if node.kind == "constant" else None
