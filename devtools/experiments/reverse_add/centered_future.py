"""Research constructor for source-bound reverse/add centered cylinders.

This is the constructive bridge between the centered residual algebra and the
modulo-32 interval quotient. The original source is read once to form interval
runs. Later advances recover signed resets, growth and forcing directly from
quotient boundaries; they never construct a carry SLP or midpoint digit word.

One call to :meth:`CenteredFutureGrammar.advance` is an exact chronological
successor.  This module deliberately makes no pumping claim: repeated calls
remain linear in the number of temporal clauses until a separately checked
parameter-transport rule is supplied.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.automata.residue_carry_slp import (
    ResidueCarrySLPResult,
)
from number_compiler.arithmetic.contracts.cylinder_chart import CylinderChart
from number_compiler.arithmetic.contracts.scoped_handles import (
    ArenaHandle,
    ArenaToken,
    ExactSource,
)
from number_compiler.arithmetic.fields.centered_carry import (
    advance_centered_residual,
    center_pair_field,
    reflected_innovation,
    uncenter_pair_field,
)
from number_compiler.arithmetic.fields.live_carry_projection import (
    recover_centered_carry_events,
)
from number_compiler.arithmetic.fields.live_forcing import LiveForcingProjection
from number_compiler.arithmetic.fields.radial_innovation import InnovationID
from number_compiler.arithmetic.fields.symbolic_innovation import (
    SymbolicInnovationArena,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict, LedgerList


@dataclass(frozen=True, slots=True)
class CenteredFutureStateID(ArenaHandle):
    """Scoped identity of one admitted reachable centered cylinder."""


@dataclass(frozen=True, slots=True)
class CenteredFutureState:
    """Read-only view of one published centered cylinder."""

    steps: int
    extent: int
    residual: InnovationID
    output: InnovationID


def _shift(
    arena: SymbolicInnovationArena, expression: InnovationID, amount: int
) -> InnovationID:
    if not amount:
        return expression
    return arena.chart(expression, CylinderChart(1, -amount))


def _concatenate(
    arena: SymbolicInnovationArena,
    left: tuple[InnovationID, int],
    right: tuple[InnovationID, int],
) -> tuple[InnovationID, int]:
    left_expression, left_length = left
    right_expression, right_length = right
    return (
        arena.add(left_expression, _shift(arena, right_expression, left_length)),
        left_length + right_length,
    )


def slp_polynomial(
    arena: SymbolicInnovationArena, result: ResidueCarrySLPResult, root: int
) -> InnovationID:
    """Convert a compressed integer word to its polynomial without expansion.

    CONCAT becomes polynomial addition after a monomial chart.  REPEAT uses
    binary concatenation, so its work is logarithmic in the repetition count.
    The input SLP remains the authority for its represented word.
    """
    if (
        type(arena) is not SymbolicInnovationArena
        or type(result) is not ResidueCarrySLPResult
        or result.ledger is not arena.ledger
    ):
        raise TypeError("SLP polynomial conversion requires one owned carry result")
    outgoing_root = result.outgoing_root
    grammar = result.arena
    if type(root) is not int or not 0 <= root < len(grammar.nodes):
        raise ValueError("SLP polynomial root is foreign or out of range")
    if root not in (
        outgoing_root,
        result.jump_root,
        result.closed_jump_root,
    ):
        raise ValueError("SLP polynomial root was not published by the carry result")
    ledger = arena.ledger
    prefix = f"centered-future-slp-workspace-{ledger.owner_count}"
    values_owner = ledger.register(prefix + "-values", "query_memo")
    stack_owner: int | None = None
    values: LedgerDict[int, tuple[InnovationID, int]] | None = None
    stack: LedgerList[tuple[int, bool]] | None = None
    try:
        stack_owner = ledger.register(prefix + "-stack", "query_memo")
        values = ledger.make_dict(values_owner)
        stack = ledger.make_list(stack_owner, append_only=False)

        def push(frame: tuple[int, bool]) -> None:
            assert stack_owner is not None and stack is not None
            ledger.reserve(stack_owner, entries=1, nodes=1)
            try:
                stack.append(frame)
            except BaseException:
                ledger.release(stack_owner, entries=1, nodes=1)
                raise

        push((root, False))
        while stack:
            node_id, expanded = stack.pop()
            ledger.release(stack_owner, entries=1, nodes=1)
            if node_id in values:
                continue
            node = grammar.nodes[node_id]
            fields = (
                node.id,
                node.length,
                node.symbol,
                node.left,
                node.right,
                node.child,
                node.count,
            )
            if any(type(value) is not int for value in fields) or node.id != node_id:
                raise ValueError("SLP polynomial node identity was altered")
            if node.kind == "EMPTY":
                valid = node_id == grammar.empty_id and node.length == 0
            elif node.kind == "TERM":
                valid = (
                    node.length == 1
                    and node.left == node.right == node.child == -1
                    and node.count == 0
                )
            elif node.kind == "CONCAT":
                valid = (
                    0 <= node.left < node_id
                    and 0 <= node.right < node_id
                    and node.symbol == node.child == -1
                    and node.count == 0
                )
            elif node.kind == "REPEAT":
                valid = (
                    0 <= node.child < node_id
                    and node.count >= 2
                    and node.symbol == node.left == node.right == -1
                )
            else:
                valid = False
            if not valid:
                raise ValueError("SLP polynomial node definition was altered")
            children = (
                (node.left, node.right)
                if node.kind == "CONCAT"
                else ((node.child,) if node.kind == "REPEAT" else ())
            )
            if not expanded and children:
                push((node_id, True))
                for child in reversed(children):
                    push((child, False))
                continue
            if node.kind == "EMPTY":
                value = arena.zero, 0
            elif node.kind == "TERM":
                unit = arena.interval(1)
                value = arena.linear_combination(((node.symbol, unit),)), 1
            elif node.kind == "CONCAT":
                value = _concatenate(arena, values[node.left], values[node.right])
            elif node.kind == "REPEAT":
                if node.count < 2:
                    raise ValueError("SLP repeat lost its canonical count")
                repeated = arena.zero, 0
                power = values[node.child]
                count = node.count
                while count:
                    if count & 1:
                        repeated = _concatenate(arena, repeated, power)
                    count >>= 1
                    if count:
                        power = _concatenate(arena, power, power)
                    arena.ledger.bump("reverse_centered_future_repeat_bits")
                value = repeated
            else:
                raise ValueError("SLP polynomial contains an unknown node kind")
            if value[1] != node.length:
                raise ValueError("SLP polynomial length disagrees with its grammar")
            ledger.reserve(values_owner, entries=1, nodes=1)
            values[node_id] = value
            arena.ledger.bump("reverse_centered_future_slp_nodes")
        answer = values[root][0]
    finally:
        stack_entries = 0 if stack is None else len(stack)
        value_entries = 0 if values is None else len(values)
        if stack is not None:
            stack.clear()
        if values is not None:
            values.clear()
        if stack_entries or value_entries:
            if stack_entries:
                assert stack_owner is not None
                ledger.release(stack_owner, entries=stack_entries, nodes=stack_entries)
            if value_entries:
                ledger.release(values_owner, entries=value_entries, nodes=value_entries)
        if stack_owner is not None:
            ledger.mark_disposed(stack_owner)
        ledger.mark_disposed(values_owner)
    return answer


class CenteredFutureGrammar:
    """Exact finite successor constructor for one authenticated decimal source."""

    _KIND = "reverse-centered-future-state"

    def __init__(self, ledger: ResourceLedger, source: ExactSource) -> None:
        if type(ledger) is not ResourceLedger or type(source) is not ExactSource:
            raise TypeError("centered future grammar requires a ledger and source")
        source.__post_init__()
        if source.base != 10 or source.orbit != "reverse-add":
            raise ValueError("centered future grammar requires decimal reverse/add")
        if (
            not source.digits
            or source.blank != 0
            or source.extent not in (None, len(source.digits))
            or source.alphabet_size not in (None, 10)
        ):
            raise ValueError(
                "centered future grammar requires canonical finite digit geometry"
            )
        self.ledger = ledger
        self.source = source
        self._closed = False
        self._source_owner: int | None = None
        self._source_units = 1 + len(source.digits)
        self._state_owner: int | None = None
        self._states: LedgerList[CenteredFutureState] | None = None
        source_reserved = False
        workspace_owner: int | None = None
        workspace_reserved = False
        workspace_disposed = False
        arena: SymbolicInnovationArena | None = None
        try:
            prefix = f"reverse-centered-future-{ledger.owner_count}"
            self._source_owner = ledger.register(
                prefix + "-source", "reverse_centered_future_source"
            )
            workspace_owner = ledger.register(
                prefix + "-source-workspace",
                "reverse_centered_future_source_workspace",
            )
            # Charge the retained authority and both constant-size scan cursors
            # before allocating the arena or any source-derived expression.
            ledger.reserve_many(
                (
                    (self._source_owner, 1, self._source_units),
                    (workspace_owner, 2, 2),
                )
            )
            source_reserved = True
            workspace_reserved = True
            ledger.bump("reverse_centered_future_source_workspace_peak", 2)
            self._source_digits = source.digits
            self._source_authority = (
                source,
                source.digits,
                source.base,
                source.orbit,
                source.blank,
                source.extent,
                source.alphabet_size,
            )
            self._owner = ArenaToken("reverse-centered-future")
            arena = SymbolicInnovationArena(ledger)
            self.arena = arena
            self._state_owner = ledger.register(
                f"reverse-centered-future-states-{ledger.owner_count}",
                "reverse_centered_future_state",
            )
            self._states = ledger.make_list(self._state_owner)
            ledger.register_container(
                self._state_owner,
                self._states,
                node_count=lambda: 0 if self._states is None else len(self._states),
                payloads=lambda: () if self._states is None else self._states,
            )
            try:
                digits = self._run_expression(source.digits)
                pairs = self._pair_run_expression()
            finally:
                ledger.release(workspace_owner, entries=2, nodes=2)
                workspace_reserved = False
                ledger.mark_disposed(workspace_owner)
                workspace_disposed = True
            residual = center_pair_field(self.arena, pairs, extent=len(source.digits))
            self.initial = self._publish(
                CenteredFutureState(0, len(source.digits), residual, digits)
            )
            ledger.register_execution_root(self)
        except BaseException:
            if workspace_reserved and workspace_owner is not None:
                ledger.release(workspace_owner, entries=2, nodes=2)
            if workspace_owner is not None and not workspace_disposed:
                ledger.mark_disposed(workspace_owner)
            if self._states is not None and self._state_owner is not None:
                count = len(self._states)
                self._states.rollback_unpublished(0)
                if count:
                    ledger.release(self._state_owner, entries=count, nodes=count)
            if self._state_owner is not None:
                ledger.mark_disposed(self._state_owner)
            if arena is not None:
                arena.close()
            if source_reserved and self._source_owner is not None:
                ledger.release(self._source_owner, entries=1, nodes=self._source_units)
            if self._source_owner is not None:
                ledger.mark_disposed(self._source_owner)
            self._closed = True
            raise

    def require_open(self) -> None:
        if self._closed:
            raise ValueError("disposed centered future grammar")
        authority = self._source_authority
        if (
            self.source is not authority[0]
            or self.source.digits is not authority[1]
            or self.source.base != authority[2]
            or self.source.orbit != authority[3]
            or self.source.blank != authority[4]
            or self.source.extent != authority[5]
            or self.source.alphabet_size != authority[6]
            or self._source_digits is not authority[1]
        ):
            raise ValueError("centered future source authority was altered")
        if self._states is None or self._state_owner is None:
            raise ValueError("centered future state arena is unavailable")
        self.initial.validate(self._owner, self._KIND, size=len(self._states))
        initial = self._states[self.initial.local_id]
        if initial.steps != 0:
            raise ValueError("centered future origin publication was altered")
        self.arena.resolve(initial.residual)
        self.arena.resolve(initial.output)

    def _publish(self, state: CenteredFutureState) -> CenteredFutureStateID:
        if self._states is None or self._state_owner is None:
            raise ValueError("centered future state arena is unavailable")
        self.arena.resolve(state.residual)
        self.arena.resolve(state.output)
        if state.steps != len(self._states):
            raise ValueError("centered future publication is not chronological")
        self.ledger.reserve(self._state_owner, entries=1, nodes=1)
        try:
            self._states.append(state)
        except BaseException:
            self.ledger.release(self._state_owner, entries=1, nodes=1)
            raise
        return CenteredFutureStateID(self._owner, self._KIND, state.steps)

    def state(self, state: CenteredFutureStateID) -> CenteredFutureState:
        self.require_open()
        assert self._states is not None
        if type(state) is not CenteredFutureStateID:
            raise TypeError("centered future grammar requires a scoped state ID")
        state.validate(self._owner, self._KIND, size=len(self._states))
        record = self._states[state.local_id]
        if record.steps != state.local_id:
            raise ValueError("centered future state publication was altered")
        self.arena.resolve(record.residual)
        self.arena.resolve(record.output)
        return record

    def _run_expression(self, values: tuple[int, ...]) -> InnovationID:
        self.ledger.bump("reverse_centered_future_source_coordinates", len(values))
        result = self.arena.zero
        start = 0
        while start < len(values):
            stop = start + 1
            while stop < len(values) and values[stop] == values[start]:
                stop += 1
            interval = self.arena.interval(stop - start)
            term = self.arena.linear_combination(
                ((values[start], _shift(self.arena, interval, start)),)
            )
            result = self.arena.add(result, term)
            start = stop
            self.ledger.bump("reverse_centered_future_source_runs")
        return result

    def _pair_run_expression(self) -> InnovationID:
        digits = self._source_digits
        self.ledger.bump("reverse_centered_future_source_coordinates", len(digits))
        result = self.arena.zero
        start = 0
        while start < len(digits):
            value = digits[start] + digits[-1 - start]
            stop = start + 1
            while stop < len(digits) and digits[stop] + digits[-1 - stop] == value:
                stop += 1
            interval = self.arena.interval(stop - start)
            term = self.arena.linear_combination(
                ((value, _shift(self.arena, interval, start)),)
            )
            result = self.arena.add(result, term)
            start = stop
            self.ledger.bump("reverse_centered_future_source_runs")
        return result

    @property
    def retained_states(self) -> int:
        self.require_open()
        assert self._states is not None
        return len(self._states)

    @property
    def retained_innovation_nodes(self) -> int:
        self.require_open()
        return self.arena.node_count

    @property
    def observed_residue_runs(self) -> int:
        """Total represented intervals inspected by finite carry demands."""
        self.require_open()
        return self.ledger.counters.get("carry_event_domain_actions", 0)

    def advance(self, state: CenteredFutureStateID) -> CenteredFutureStateID:
        """Construct one exact successor from the compressed centered cylinder."""
        record = self.state(state)
        assert self._states is not None
        if state.local_id + 1 < len(self._states):
            return CenteredFutureStateID(self._owner, self._KIND, state.local_id + 1)
        events = recover_centered_carry_events(
            self.arena, record.residual, extent=record.extent
        )
        growth = events.terminal_carry
        pair = uncenter_pair_field(self.arena, record.residual, extent=record.extent)
        correction = events.correction
        output = self.arena.add(pair, correction)
        innovation = reflected_innovation(
            self.arena,
            correction,
            extent=record.extent,
            growth=growth,
        )
        residual = advance_centered_residual(
            self.arena,
            record.residual,
            innovation,
            extent=record.extent,
            growth=growth,
        )
        self.ledger.bump("reverse_centered_future_advances")
        return self._publish(
            CenteredFutureState(
                record.steps + 1,
                record.extent + growth,
                residual,
                output,
            )
        )

    def construct(self, steps: int) -> CenteredFutureStateID:
        """Construct a finite prefix exactly; this is not a pumping operation."""
        if type(steps) is not int or steps < 0:
            raise ValueError("centered future steps must be nonnegative")
        self.require_open()
        assert self._states is not None
        state = CenteredFutureStateID(self._owner, self._KIND, len(self._states) - 1)
        while state.local_id < steps:
            state = self.advance(state)
        return CenteredFutureStateID(self._owner, self._KIND, steps)

    def runs(self, state: CenteredFutureStateID) -> tuple[tuple[int, int, int], ...]:
        """Return compressed exact digit runs for the current output."""
        record = self.state(state)
        with LiveForcingProjection(self.arena, record.output) as view:
            runs = view.residue_runs(0, record.extent)
        if any(not 0 <= run.residue <= 9 for run in runs):
            raise ArithmeticError("centered future output left the digit alphabet")
        return tuple((run.start, run.stop, run.residue) for run in runs)

    def digit(self, state: CenteredFutureStateID, position: int) -> int:
        record = self.state(state)
        if type(position) is not int or not 0 <= position < record.extent:
            raise IndexError(position)
        with LiveForcingProjection(self.arena, record.output) as view:
            run = view.residue_runs(position, position + 1)
        if len(run) != 1 or not 0 <= run[0].residue <= 9:
            raise ArithmeticError("centered future output is not one decimal digit")
        return run[0].residue

    def close(self) -> None:
        if self._closed:
            return
        assert self._states is not None and self._state_owner is not None
        count = len(self._states)
        self._states.rollback_unpublished(0)
        if count:
            self.ledger.release(self._state_owner, entries=count, nodes=count)
        self.ledger.mark_disposed(self._state_owner)
        assert self._source_owner is not None
        self.ledger.release(self._source_owner, entries=1, nodes=self._source_units)
        self.ledger.mark_disposed(self._source_owner)
        self._owner = ArenaToken("disposed-reverse-centered-future")
        self.arena.close()
        self._closed = True


__all__ = [
    "CenteredFutureGrammar",
    "CenteredFutureState",
    "CenteredFutureStateID",
    "slp_polynomial",
]
