"""Exact four-port, source-word action for one ``2rev10`` temporal square.

The source word is stored most-significant digit first.  The first carry wave
travels left to right and the second travels right to left.  A block summary
retains both outgoing carries and its complete fixed-width output for each of
the four incoming-port pairs.  The fold operates directly in the caller's SLP
arena, including binary powering of ``REPEAT`` nodes.

This certifies one exact successor action on an admitted source word.  It does
not assert that the source's future port word is periodic.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, field

from number_compiler.arithmetic.automata.slp import SLPArena, SLPNode
from number_compiler.arithmetic.automata.slp_interval import fold_slp_dag

_FOUR_PORT_PROJECTION_ISSUER = object()


def _validated_arena(candidate: object) -> SLPArena:
    if not isinstance(candidate, SLPArena):
        raise TypeError("four-port carry actions require an SLP arena")
    return candidate


@dataclass(frozen=True, slots=True)
class TwoStepCarryPorts:
    """One digit's two-pass output and its outward carry ports."""

    digit: int
    forward_out: int
    reverse_out: int


class TwoStepCarryCell:
    """The shared scalar producer for the four conditional carry ports."""

    __slots__ = ()

    @staticmethod
    def apply(digit: int, forward_in: int, reverse_in: int) -> TwoStepCarryPorts:
        """Apply both doublings to one source digit with explicit inlets."""
        if (
            type(digit) is not int
            or not 0 <= digit <= 9
            or type(forward_in) is not int
            or forward_in not in (0, 1)
            or type(reverse_in) is not int
            or reverse_in not in (0, 1)
        ):
            raise ValueError("invalid two-step decimal carry ports")
        forward_out, first = divmod(2 * digit + forward_in, 10)
        reverse_out, output = divmod(2 * first + reverse_in, 10)
        return TwoStepCarryPorts(output, forward_out, reverse_out)


@dataclass(frozen=True, slots=True, eq=False)
class FourPortCarryRow:
    """A fixed-width block output under one pair of external carry inlets."""

    forward_out: int
    reverse_out: int
    _arena: SLPArena = field(repr=False)
    _output_root: int = field(repr=False)
    _output_node: SLPNode = field(repr=False, compare=False)

    def __post_init__(self) -> None:
        arena = _validated_arena(self._arena)
        if (
            type(self.forward_out) is not int
            or self.forward_out not in (0, 1)
            or type(self.reverse_out) is not int
            or self.reverse_out not in (0, 1)
            or type(self._output_root) is not int
            or not 0 <= self._output_root < len(arena.nodes)
            or arena.nodes[self._output_root] is not self._output_node
        ):
            raise ValueError("malformed or foreign four-port output row")

    def output_in(self, arena: SLPArena) -> int:
        """Resolve the local root only through its issuing arena object."""
        if arena is not self._arena:
            raise ValueError("four-port output belongs to another SLP arena")
        if (
            not 0 <= self._output_root < len(arena.nodes)
            or arena.nodes[self._output_root] is not self._output_node
        ):
            raise ValueError("four-port output root is stale")
        return self._output_root

    def validate_for(self, arena: SLPArena, input_width: int | None = None) -> None:
        """Check arena authority and, when supplied, the fixed row width."""
        root = self.output_in(arena)
        if input_width is not None and arena.nodes[root].length != input_width:
            raise ValueError("four-port output row has the wrong width")


@dataclass(frozen=True, slots=True, eq=False)
class FourPortCarryAction:
    """Composable two-wave action over an original MSB-first SLP block."""

    _arena: SLPArena = field(repr=False)
    input_width: int
    rows: tuple[
        FourPortCarryRow,
        FourPortCarryRow,
        FourPortCarryRow,
        FourPortCarryRow,
    ]

    def __post_init__(self) -> None:
        arena = _validated_arena(self._arena)
        if type(self.input_width) is not int or self.input_width < 0:
            raise ValueError("invalid four-port action width")
        if type(self.rows) is not tuple or len(self.rows) != 4:
            raise ValueError("four-port action must publish exactly four rows")
        if any(type(row) is not FourPortCarryRow for row in self.rows):
            raise ValueError("malformed, stale, or foreign four-port action row")
        for row in self.rows:
            if (
                type(row.forward_out) is not int
                or row.forward_out not in (0, 1)
                or type(row.reverse_out) is not int
                or row.reverse_out not in (0, 1)
            ):
                raise ValueError("malformed, stale, or foreign four-port action row")
            row.validate_for(arena, self.input_width)
        # The first wave runs independently of the second wave's inlet.
        if (
            self.rows[0].forward_out != self.rows[1].forward_out
            or self.rows[2].forward_out != self.rows[3].forward_out
        ):
            raise ValueError("forward carry depends on the reverse inlet")
        if self.input_width == 0 and any(
            (row.forward_out, row.reverse_out) != (index // 2, index % 2)
            for index, row in enumerate(self.rows)
        ):
            raise ValueError("empty four-port action must preserve both carry inlets")

    @classmethod
    def identity(cls, arena: SLPArena) -> FourPortCarryAction:
        arena = _validated_arena(arena)
        return cls(
            arena,
            0,
            (
                FourPortCarryRow(
                    0, 0, arena, arena.empty_id, arena.nodes[arena.empty_id]
                ),
                FourPortCarryRow(
                    0, 1, arena, arena.empty_id, arena.nodes[arena.empty_id]
                ),
                FourPortCarryRow(
                    1, 0, arena, arena.empty_id, arena.nodes[arena.empty_id]
                ),
                FourPortCarryRow(
                    1, 1, arena, arena.empty_id, arena.nodes[arena.empty_id]
                ),
            ),
        )

    @classmethod
    def terminal(
        cls,
        arena: SLPArena,
        digit: int,
        *,
        reserve_scratch: Callable[[int, int], None] | None = None,
        on_region_visit: Callable[[int], None] | None = None,
    ) -> FourPortCarryAction:
        arena = _validated_arena(arena)
        if reserve_scratch is not None:
            reserve_scratch(5, 5)
        rows: list[FourPortCarryRow] = []
        for forward_in in (0, 1):
            for reverse_in in (0, 1):
                if on_region_visit is not None:
                    on_region_visit(1)
                cell = TwoStepCarryCell.apply(digit, forward_in, reverse_in)
                output_root = arena.terminal(cell.digit)
                rows.append(
                    FourPortCarryRow(
                        cell.forward_out,
                        cell.reverse_out,
                        arena,
                        output_root,
                        arena.nodes[output_root],
                    )
                )
        return cls(arena, 1, (rows[0], rows[1], rows[2], rows[3]))

    def row(self, forward_in: int, reverse_in: int) -> FourPortCarryRow:
        if (
            type(forward_in) is not int
            or forward_in not in (0, 1)
            or type(reverse_in) is not int
            or reverse_in not in (0, 1)
        ):
            raise ValueError("four-port action requires Boolean inlets")
        row = self.rows[2 * forward_in + reverse_in]
        row.output_in(self._arena)
        return row

    def validate_for(self, arena: SLPArena, input_width: int | None = None) -> None:
        """Validate the action's arena, all row nodes and optional source width."""
        if arena is not self._arena:
            raise ValueError("four-port action belongs to another SLP arena")
        for row in self.rows:
            row.validate_for(arena, self.input_width)
        if input_width is not None and self.input_width != input_width:
            raise ValueError("four-port action has the wrong source width")

    def then(
        self,
        later: FourPortCarryAction,
        *,
        reserve_scratch: Callable[[int, int], None] | None = None,
        on_region_visit: Callable[[int], None] | None = None,
        retained_result: bool = True,
    ) -> FourPortCarryAction:
        """Join adjacent blocks, transporting both carries in order."""
        if type(later) is not FourPortCarryAction:
            raise TypeError("expected a four-port carry action")
        if later._arena is not self._arena:
            raise ValueError("cannot compose actions from different SLP arenas")
        self.validate_for(self._arena)
        later.validate_for(self._arena)
        if self.input_width == 0:
            return later
        if later.input_width == 0:
            return self
        if retained_result and reserve_scratch is not None:
            reserve_scratch(5, 5)

        rows: list[FourPortCarryRow] = []
        for forward_in in (0, 1):
            left_forward = self.row(forward_in, 0).forward_out
            for reverse_in in (0, 1):
                if on_region_visit is not None:
                    on_region_visit(1)
                right_row = later.row(left_forward, reverse_in)
                left_row = self.row(forward_in, right_row.reverse_out)
                output_root = self._arena.concat(
                    left_row.output_in(self._arena),
                    right_row.output_in(self._arena),
                )
                rows.append(
                    FourPortCarryRow(
                        right_row.forward_out,
                        left_row.reverse_out,
                        self._arena,
                        output_root,
                        self._arena.nodes[output_root],
                    )
                )
        return FourPortCarryAction(
            self._arena,
            self.input_width + later.input_width,
            (rows[0], rows[1], rows[2], rows[3]),
        )

    def power(
        self,
        repetitions: int,
        *,
        on_region_visit: Callable[[int], None] | None = None,
    ) -> FourPortCarryAction:
        """Repeat this spatial block by chronological binary composition."""
        if type(repetitions) is not int or repetitions < 0:
            raise ValueError("spatial repeat count must be nonnegative")
        self.validate_for(self._arena)
        result = FourPortCarryAction.identity(self._arena)
        block = self
        remaining = repetitions
        while remaining:
            if remaining & 1:
                result = result.then(
                    block,
                    on_region_visit=on_region_visit,
                    retained_result=False,
                )
            remaining >>= 1
            if remaining:
                block = block.then(
                    block,
                    on_region_visit=on_region_visit,
                    retained_result=False,
                )
        return result


@dataclass(frozen=True, slots=True, init=False, eq=False)
class FourPortSLPProjection:
    """Source-bound result of folding the reachable SLP action nodes."""

    action: FourPortCarryAction
    _arena: SLPArena = field(repr=False)
    source_root: int
    _source_node: SLPNode = field(repr=False, compare=False)
    _issuer: object = field(repr=False, compare=False)
    _issued_action: FourPortCarryAction = field(repr=False, compare=False)
    _issued_width: int = field(repr=False, compare=False)
    _issued_rows: tuple[tuple[FourPortCarryRow, int, int, int, SLPNode], ...] = field(
        repr=False, compare=False
    )

    def __init__(
        self,
        action: FourPortCarryAction,
        arena: SLPArena,
        source_root: int,
        source_node: SLPNode,
        *,
        _issuer: object,
    ) -> None:
        if _issuer is not _FOUR_PORT_PROJECTION_ISSUER:
            raise TypeError("four-port projections must come from the SLP fold")
        if type(action) is not FourPortCarryAction:
            raise TypeError("projection needs its exact four-port action")
        arena = _validated_arena(arena)
        if (
            type(source_root) is not int
            or not 0 <= source_root < len(arena.nodes)
            or arena.nodes[source_root] is not source_node
            or action.input_width != source_node.length
        ):
            raise ValueError("projection is not bound to its exact source root")
        action.validate_for(arena, source_node.length)
        issued_rows_list: list[tuple[FourPortCarryRow, int, int, int, SLPNode]] = []
        for row in action.rows:
            output_root = row.output_in(arena)
            issued_rows_list.append(
                (
                    row,
                    row.forward_out,
                    row.reverse_out,
                    output_root,
                    arena.nodes[output_root],
                )
            )
        issued_rows = tuple(issued_rows_list)
        object.__setattr__(self, "action", action)
        object.__setattr__(self, "_arena", arena)
        object.__setattr__(self, "source_root", source_root)
        object.__setattr__(self, "_source_node", source_node)
        object.__setattr__(self, "_issuer", _FOUR_PORT_PROJECTION_ISSUER)
        object.__setattr__(self, "_issued_action", action)
        object.__setattr__(self, "_issued_width", action.input_width)
        object.__setattr__(self, "_issued_rows", issued_rows)

    def validate_for(self, arena: SLPArena, source_root: int) -> None:
        """Authenticate the projection against the exact current source node."""
        arena = _validated_arena(arena)
        if (
            self._issuer is not _FOUR_PORT_PROJECTION_ISSUER
            or self.action is not self._issued_action
            or self.action.input_width != self._issued_width
            or len(self.action.rows) != len(self._issued_rows)
            or arena is not self._arena
            or type(source_root) is not int
            or source_root != self.source_root
            or not 0 <= source_root < len(arena.nodes)
            or arena.nodes[source_root] is not self._source_node
        ):
            raise ValueError("four-port projection belongs to another or stale source")
        for current, issued in zip(self.action.rows, self._issued_rows, strict=True):
            row, forward_out, reverse_out, root, node = issued
            current_root = current.output_in(arena)
            if (
                current is not row
                or current.forward_out != forward_out
                or current.reverse_out != reverse_out
                or current_root != root
                or arena.nodes[current_root] is not node
            ):
                raise ValueError("four-port projection action was changed after issue")
        self.action.validate_for(arena, self._source_node.length)


def _issue_fold_projection(
    action: FourPortCarryAction,
    arena: SLPArena,
    source_root: int,
    reserve_scratch: Callable[[int, int], None] | None,
) -> FourPortSLPProjection:
    """Issue one projection and charge its retained row snapshot first."""
    if type(source_root) is not int or not 0 <= source_root < len(arena.nodes):
        raise ValueError("four-port projection source is outside its arena")
    # The immutable snapshot retains the action rows and their output-node
    # identities while the consumer checks its source binding.
    if reserve_scratch is not None:
        reserve_scratch(6, 6)
    return FourPortSLPProjection(
        action,
        arena,
        source_root,
        arena.nodes[source_root],
        _issuer=_FOUR_PORT_PROJECTION_ISSUER,
    )


def fold_two_step_slp(
    arena: SLPArena,
    root: int,
    *,
    reserve_scratch: Callable[[int, int], None] | None = None,
    on_region_visit: Callable[[int], None] | None = None,
) -> FourPortSLPProjection:
    """Fold all four ``T²`` port rows over one caller-owned SLP grammar.

    The local fold memo is bounded by the reachable source node count and is
    discarded on return.  Every emitted output node is interned in ``arena``;
    the caller reserves transient fold storage before invoking this function.
    """
    arena = _validated_arena(arena)
    if type(root) is not int or not 0 <= root < len(arena.nodes):
        raise ValueError("two-step SLP root is outside its arena")

    identity = FourPortCarryAction.identity(arena)

    def terminal(digit: int) -> FourPortCarryAction:
        return FourPortCarryAction.terminal(
            arena,
            digit,
            reserve_scratch=reserve_scratch,
            on_region_visit=on_region_visit,
        )

    def concatenate(
        earlier: FourPortCarryAction, later: FourPortCarryAction
    ) -> FourPortCarryAction:
        return earlier.then(
            later,
            reserve_scratch=reserve_scratch,
            on_region_visit=on_region_visit,
        )

    power_workspace_reserved = False

    def repeat(action: FourPortCarryAction, count: int) -> FourPortCarryAction:
        nonlocal power_workspace_reserved
        if count > 1 and reserve_scratch is not None:
            if not power_workspace_reserved:
                reserve_scratch(24, 24)
                power_workspace_reserved = True
            reserve_scratch(5, 5)
        return action.power(count, on_region_visit=on_region_visit)

    def on_reduce(_node_id: int) -> None:
        if on_region_visit is not None:
            on_region_visit(1)

    def on_schedule(count: int) -> None:
        if reserve_scratch is not None:
            reserve_scratch(count, count)

    values = fold_slp_dag(
        arena,
        root,
        empty_value=identity,
        terminal_value=terminal,
        concatenate=concatenate,
        repeat=repeat,
        on_schedule=on_schedule if reserve_scratch is not None else None,
        on_reduce=on_reduce,
    )
    action: FourPortCarryAction | None = None
    try:
        action = values[root]
        if action.input_width != arena.nodes[root].length:
            raise ArithmeticError("four-port fold changed the source word width")
        action.validate_for(arena, arena.nodes[root].length)
        return _issue_fold_projection(action, arena, root, reserve_scratch)
    finally:
        values.clear()
        action = None


__all__ = [
    "FourPortCarryAction",
    "FourPortCarryRow",
    "FourPortSLPProjection",
    "TwoStepCarryCell",
    "TwoStepCarryPorts",
    "fold_two_step_slp",
]
