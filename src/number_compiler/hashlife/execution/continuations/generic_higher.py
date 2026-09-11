"""Runtime K/U projection for admitted generic temporal action programs.

The projection changes only the carrier: source-independent temporal programs
become scoped field actions while original digits remain in ``SourceCellArena``.
All midpoint behavior is evaluated through canonical K/U summaries.
"""

from __future__ import annotations

from collections.abc import MutableMapping, MutableSequence
from dataclasses import dataclass
from typing import TYPE_CHECKING, Literal

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
)
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.continuations.higher_bimachine import (
    HigherBimachineRuntime,
)
from number_compiler.hashlife.execution.continuations.higher_operations import (
    evaluate_operation,
    force_value,
)
from number_compiler.hashlife.execution.continuations.higher_semantic import (
    HigherSemanticArena,
)
from number_compiler.hashlife.execution.continuations.higher_values import RuntimeAtom
from number_compiler.hashlife.execution.field_images import (
    SourceCellArena,
    SourceCellID,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )
    from number_compiler.hashlife.interfaces.diamond_kernel import PrimitiveKernel


@dataclass(frozen=True, slots=True)
class _GenericHigherAction:
    original: ActionProgramID
    children: tuple[FieldCellActionID, FieldCellActionID] | None


class GenericHigherActionSchema:
    """Atomically project one temporal DAG into the common higher action sort."""

    _KIND = "field-cell-action"

    def __init__(self, runtime: DiamondRuntime) -> None:
        self.runtime, self.ledger = runtime, runtime.ledger
        self.owner = ArenaToken("generic-higher-actions")
        source = runtime.cells.source_geometry._construction.source
        self._alphabet = source.base, source.blank
        prefix = f"generic-higher-actions-{len(self.ledger.inventory())}"
        self._node_owner = self.ledger.register(prefix + "-nodes", "field_cell_action")
        self._key_owner = self.ledger.register(
            prefix + "-keys", "field_action_interner"
        )
        self._nodes: MutableSequence[_GenericHigherAction] = self.ledger.make_list(
            self._node_owner,
        )
        self._keys: MutableMapping[ActionProgramID, int] = self.ledger.make_dict(
            self._key_owner,
        )
        self.ledger.register_container(
            self._node_owner,
            self._nodes,
            payloads=lambda: self._nodes,
            node_count=lambda: len(self._nodes),
        )
        self.ledger.register_container(
            self._key_owner,
            self._keys,
            payloads=self._keys.items,
        )
        self.ledger.register_execution_root(self)

    def _handle(self, local_id: int) -> FieldCellActionID:
        return FieldCellActionID(self.owner, self._KIND, local_id)

    def _resolve(self, action: FieldCellActionID) -> _GenericHigherAction:
        if type(action) is not FieldCellActionID:
            raise TypeError("generic higher actions require exact scoped IDs")
        action.validate(self.owner, self._KIND, size=len(self._nodes))
        return self._nodes[action.local_id]

    def import_action(self, root: ActionProgramID) -> FieldCellActionID:
        self.runtime.actions.resolve(root)
        found = self._keys.get(root)
        if found is not None:
            self.ledger.bump("generic_higher_action_early_hits")
            return self._handle(found)
        order: list[ActionProgramID] = []
        seen: set[ActionProgramID] = set()
        stack = [(root, False)]
        while stack:
            action, ready = stack.pop()
            if action in self._keys or action in seen:
                continue
            node = self.runtime.actions.resolve(action)
            if node.kind == "compose" and not ready:
                stack.append((action, True))
                stack.append((self.runtime.actions.reference(node.right), False))
                stack.append((self.runtime.actions.reference(node.left), False))
                continue
            if node.kind == "atom":
                self.runtime.kernel(action)
            seen.add(action)
            order.append(action)
        offset = len(self._nodes)
        planned = {action: offset + index for index, action in enumerate(order)}
        records: list[_GenericHigherAction] = []
        for action in order:
            node = self.runtime.actions.resolve(action)
            children = None
            if node.kind == "compose":
                original = (
                    self.runtime.actions.reference(node.left),
                    self.runtime.actions.reference(node.right),
                )
                children = (
                    self._handle(
                        self._keys[original[0]]
                        if original[0] in self._keys
                        else planned[original[0]]
                    ),
                    self._handle(
                        self._keys[original[1]]
                        if original[1] in self._keys
                        else planned[original[1]]
                    ),
                )
            records.append(_GenericHigherAction(action, children))
        count = len(records)
        self.ledger.reserve_many(
            ((self._node_owner, count, count), (self._key_owner, count, 0)),
        )
        for action, record in zip(order, records, strict=True):
            self._keys[action] = len(self._nodes)
            self._nodes.append(record)
        self.ledger.bump("generic_higher_action_publications", count)
        return self._handle(self._keys[root])

    def validate_action(self, action: FieldCellActionID) -> None:
        record = self._resolve(action)
        self.runtime.actions.resolve(record.original)

    def children(
        self,
        action: FieldCellActionID,
    ) -> tuple[FieldCellActionID, FieldCellActionID] | None:
        return self._resolve(action).children

    def kind(
        self,
        action: FieldCellActionID,
    ) -> Literal["identity", "primitive", "compose"]:
        kind = self.runtime.actions.resolve(self._resolve(action).original).kind
        return "primitive" if kind == "atom" else kind

    def alphabet(self, action: FieldCellActionID) -> tuple[int, int]:
        record = self._resolve(action)
        node = self.runtime.actions.resolve(record.original)
        if node.kind != "identity" and (node.base, node.blank) != self._alphabet:
            raise ValueError("generic action and original source alphabets disagree")
        return self._alphabet

    @staticmethod
    def _side(side: int) -> BoundarySide:
        if type(side) is not int or side not in (0, 1):
            raise ValueError("generic higher side must be zero or one")
        return BoundarySide(side)

    def _kernel(self, action: FieldCellActionID) -> PrimitiveKernel:
        original = self._resolve(action).original
        if self.runtime.actions.resolve(original).kind != "atom":
            raise ValueError("generic primitive operation requires an atom")
        return self.runtime.kernel(original)

    def state_count(self, action: FieldCellActionID, side: int) -> int:
        direction = self._side(side)
        if self.kind(action) == "identity":
            return 1
        kernel = self._kernel(action)
        return (
            kernel.left_count if direction is BoundarySide.LEFT else kernel.right_count
        )

    def initial(self, action: FieldCellActionID, side: int) -> int:
        direction = self._side(side)
        return (
            0
            if self.kind(action) == "identity"
            else self._kernel(action).initial(direction)
        )

    def step(
        self,
        action: FieldCellActionID,
        side: int,
        state: int,
        symbol: int,
    ) -> int:
        direction = self._side(side)
        if self.kind(action) == "identity":
            _, blank = self.alphabet(action)
            if type(state) is not int or state != 0:
                raise ValueError("identity state must be zero")
            if type(symbol) is not int or not 0 <= symbol <= blank:
                raise ValueError("identity symbol is outside the source alphabet")
            return 0
        return self._kernel(action).advance(direction, state, symbol)

    def emit(
        self,
        action: FieldCellActionID,
        left: int,
        symbol: int,
        right: int,
    ) -> int:
        if self.kind(action) == "identity":
            _, blank = self.alphabet(action)
            if (
                type(left) is not int
                or type(right) is not int
                or left != 0
                or right != 0
            ):
                raise ValueError("identity boundary states must be zero")
            if type(symbol) is not int or not 0 <= symbol <= blank:
                raise ValueError("identity symbol is outside the source alphabet")
            return symbol
        return self._kernel(action).emit(left, symbol, right)

    def runtime_blank_identity(
        self, action: FieldCellActionID, side: int
    ) -> bool | None:
        self._side(side)
        return True if self.kind(action) == "identity" else None


@dataclass(frozen=True, slots=True)
class _WidthCell:
    start: int
    cell: SourceCellID
    left: RuntimeAtom


class GenericHigherRuntime:
    """One index-owned structural runtime shared by all generic observations."""

    def __init__(self, runtime: DiamondRuntime) -> None:
        self.runtime, self.ledger = runtime, runtime.ledger
        self.schema = GenericHigherActionSchema(runtime)
        self.sources = SourceCellArena(runtime.cells.source_geometry)
        source = runtime.cells.source_geometry._read_root
        if source is None:
            raise ValueError("generic higher runtime requires an exact source")
        self.source = self.sources.forest(0, source.length)
        self.semantics = HigherSemanticArena(self.schema)
        self.machine = HigherBimachineRuntime(self.semantics, self.sources)

    def _action(self, action: ActionProgramID) -> FieldCellActionID:
        return self.schema.import_action(action)

    def point(self, action: ActionProgramID, coordinate: int) -> int:
        extent = self.sources.binding_extent(self.source)
        if type(coordinate) is not int or not 0 <= coordinate < extent:
            raise IndexError(coordinate)
        self.runtime.actions.resolve(action)
        projected = self._action(action)
        if self.schema.kind(projected) == "identity":
            self.ledger.bump("higher_point_observations")
            return self.sources.binding_read(self.source, coordinate)
        return self.machine.point_structural(projected, self.source, coordinate)

    def _transfer(
        self,
        action: FieldCellActionID,
        cell: SourceCellID,
        state: RuntimeAtom,
        side: int,
    ) -> RuntimeAtom:
        summary = self.machine.summaries.runtime_unary(action, cell, side)
        return self.machine.summaries.transfer_value(summary, state)

    def _active(
        self,
        action: FieldCellActionID,
        observer: FieldCellActionID,
        cell: SourceCellID,
        left: RuntimeAtom,
        right: RuntimeAtom,
        incoming: RuntimeAtom,
    ) -> bool:
        summary = self.machine.summaries.runtime_context(action, observer, cell)
        result = force_value(
            self.semantics,
            self.machine.summaries.context_value(summary, left, right, incoming, 1),
        )
        if type(result) is not int or result not in (0, 1):
            raise AssertionError("activity observer left its Boolean port")
        return bool(result)

    def width(
        self,
        action: ActionProgramID,
        observer: ActionProgramID,
        maxwidth: int,
    ) -> int:
        extent = self.sources.binding_extent(self.source)
        if type(maxwidth) is not int or not 0 <= maxwidth <= extent:
            raise ValueError("width bound must fit the original source extent")
        self.runtime.actions.resolve(action)
        self.runtime.actions.resolve(observer)
        projected, observed = self._action(action), self._action(observer)
        self.ledger.bump("higher_width_observations")
        if not maxwidth:
            return 0
        left = evaluate_operation(self.semantics, "initial", projected, 0, ())
        right = evaluate_operation(self.semantics, "initial", projected, 1, ())
        incoming = evaluate_operation(self.semantics, "initial", observed, 1, ())
        prefix = self.machine._range_cells(self.source, 0, maxwidth)
        contexts: list[_WidthCell] = []
        start = 0
        for index, cell in enumerate(prefix):
            contexts.append(_WidthCell(start, cell, left))
            start += self.sources.resolve(cell).width
            self.ledger.bump("parametric_width_forest_visits")
            if index + 1 < len(prefix):
                left = self._transfer(projected, cell, left, 0)
        counter = "parametric_width_contexts_peak"
        self.ledger.bump(
            counter,
            max(0, len(contexts) - self.ledger.counters.get(counter, 0)),
        )
        for cell in reversed(self.machine._range_cells(self.source, maxwidth, extent)):
            right = self._transfer(projected, cell, right, 1)
        for context in reversed(contexts):
            start, cell, left = context.start, context.cell, context.left
            self.ledger.bump("parametric_width_parent_visits")
            if not self._active(projected, observed, cell, left, right, incoming):
                right = self._transfer(projected, cell, right, 1)
                continue
            while self.sources.resolve(cell).level:
                low, high = self.sources.children(cell)
                middle = start + self.sources.resolve(low).width
                middle_left = self._transfer(projected, low, left, 0)
                self.ledger.bump("parametric_width_descent_steps")
                if self._active(
                    projected, observed, high, middle_left, right, incoming
                ):
                    start, cell, left = middle, high, middle_left
                else:
                    right = self._transfer(projected, high, right, 1)
                    cell = low
            return start + 1
        return 0


def generic_higher_runtime(runtime: DiamondRuntime) -> GenericHigherRuntime:
    """Return the one per-index generic structural executor."""
    value = getattr(runtime, "_generic_higher_runtime", None)
    if value is None:
        if (
            runtime.ledger.max_cache_entries is not None
            and runtime.ledger.entries >= runtime.ledger.max_cache_entries
        ):
            from number_compiler.arithmetic.contracts.block_effect import (
                BlockContextBudgetExceeded,
            )

            raise BlockContextBudgetExceeded(
                "generic higher runtime needs one source binding",
            )
        value = GenericHigherRuntime(runtime)
        setattr(runtime, "_generic_higher_runtime", value)
    if type(value) is not GenericHigherRuntime or value.runtime is not runtime:
        raise ValueError("generic higher runtime binding is invalid")
    return value


__all__ = [
    "GenericHigherActionSchema",
    "GenericHigherRuntime",
    "generic_higher_runtime",
]
