"""Budgeted packed decimal stencil for exact demanded 2rev10 windows.

The packed rows evaluate finite source cones only. A complete spatial halo is
read from the admitted SLP; carry bits are taken from that same evolving row.
"""

from __future__ import annotations

from collections.abc import Callable
from contextlib import closing
from dataclasses import dataclass
from math import gcd, lcm
from typing import Protocol, cast

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp_walks import iter_symbols, symbol_at
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import double_reverse as keys
from number_compiler.sequences.double_reverse.stencil_moore import stencil_cell
from number_compiler.sequences.double_reverse.temporal_digit_affine import (
    DigitCarryAffine,
)
from number_compiler.sequences.double_reverse.temporal_hashlife import growth_ports

_MAX_PAIRED_RING_WINDOWS = 2


def initialize_packed_ring_metrics(ledger: ResourceLedger) -> None:
    """Initialize only counters instrumented by the packed-ring owner."""
    for counter in (
        keys.DOUBLE_REVERSE_POINTED_RING_AFFINE_DIGITS,
        keys.DOUBLE_REVERSE_POINTED_RING_AFFINE_PORTS,
        keys.DOUBLE_REVERSE_POINTED_RING_FAILED_WORK,
        keys.DOUBLE_REVERSE_POINTED_RING_OPERAND_BITS,
        keys.DOUBLE_REVERSE_POINTED_RING_PACKED_STEPS,
        keys.DOUBLE_REVERSE_POINTED_RING_SOURCE_CELLS,
        keys.DOUBLE_REVERSE_POINTED_RING_STENCIL_CELLS,
        keys.DOUBLE_REVERSE_POINTED_RING_WINDOW_ATTEMPTS,
        keys.DOUBLE_REVERSE_POINTED_RING_WINDOWS,
        keys.DOUBLE_REVERSE_POINTED_RING_FORCED_PORTS,
        keys.DOUBLE_REVERSE_POINTED_RING_BUDGET_FALLBACKS,
        keys.DOUBLE_REVERSE_POINTED_RING_PERIODIC_ATTEMPTS,
        keys.DOUBLE_REVERSE_POINTED_RING_PERIODIC_HITS,
        keys.DOUBLE_REVERSE_POINTED_RING_PERIODIC_GUARD_STATES,
        keys.DOUBLE_REVERSE_POINTED_RING_PERIODIC_MOTIF_STEPS,
        keys.DOUBLE_REVERSE_POINTED_RING_PERIODIC_SOURCE_PROBES,
        keys.DOUBLE_REVERSE_POINTED_RING_PERIODIC_SOURCE_NODE_VISITS,
        keys.DOUBLE_REVERSE_POINTED_RING_PERIODIC_MOTIF_CELL_EVALUATIONS,
        keys.DOUBLE_REVERSE_POINTED_RING_AFFINE_LOGICAL_PORTS,
    ):
        ledger.bump(counter, 0)


class _RingSource(Protocol):
    arena: LedgerSLPArena
    ledger: ResourceLedger
    max_steps: int
    scratch_owner: int

    def certify(self, root: int) -> int | None: ...

    def _pointed_source_window(self, root: int, origin: int, radius: int) -> int: ...


@dataclass(frozen=True, slots=True)
class RingWindowRequest:
    """One demanded output range and its affine-tracked positions."""

    start: int
    count: int
    positions: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class RingDigitAction:
    """Finite source-derived digit action and its exact endpoint check."""

    position: int
    initial_digit: int
    result_digit: int
    action: DigitCarryAffine


@dataclass(frozen=True, slots=True)
class RingWindowResult:
    digits: tuple[int, ...]
    actions: tuple[RingDigitAction, ...]


def _digits_to_masks(digits: bytearray) -> tuple[int, ...]:
    plane_bytes = (len(digits) + 7) // 8
    planes = [bytearray(plane_bytes) for _ in range(10)]
    for position, digit in enumerate(digits):
        if digit > 9:
            raise ArithmeticError("packed 2rev10 source contains a non-decimal digit")
        planes[digit][position >> 3] |= 1 << (position & 7)
    return tuple(int.from_bytes(plane, "little") for plane in planes)


def _slp_symbol_at(engine: _RingSource, root: int, position: int) -> int:
    """Read one source symbol and count each actually visited grammar node."""
    visits = 0

    def count_visit() -> None:
        nonlocal visits
        visits += 1

    try:
        result = symbol_at(engine.arena, root, position, on_visit=count_visit)
    finally:
        if visits:
            engine.ledger.bump(keys.DOUBLE_REVERSE_POINTED_RING_PERIODIC_SOURCE_PROBES)
            engine.ledger.bump(
                keys.DOUBLE_REVERSE_POINTED_RING_PERIODIC_SOURCE_NODE_VISITS, visits
            )
    return result


def _certified_periodic_motif(
    engine: _RingSource, root: int, *, max_period: int = 8, max_states: int = 256
) -> tuple[int, ...] | None:
    """Certify the complete finite causal SLP as a short spatial period.

    This checks every reachable SLP node/phase through an iterative worklist.
    A prefix sample only rejects candidates cheaply; it never certifies one.
    """
    width = engine.arena.nodes[root].length
    if width < 32:
        return None
    initial = tuple(_slp_symbol_at(engine, root, i) for i in range(2 * max_period))
    for period in range(1, min(max_period, width // 2) + 1):
        if any(initial[i] != initial[i % period] for i in range(period, len(initial))):
            continue
        motif = initial[:period]
        if any(
            _slp_symbol_at(engine, root, at) != motif[at % period]
            for at in (width // 2, width // 2 + 1, width - 2, width - 1)
        ):
            continue
        dependencies: dict[tuple[int, int], tuple[tuple[int, int], ...]] = {}
        terminal_values: dict[tuple[int, int], bool] = {}
        tasks: list[tuple[int, int]] = [(root, 0)]
        queued: set[tuple[int, int]] = {(root, 0)}
        discovered: set[tuple[int, int]] = set()
        charged = 0
        certified = False
        try:
            while tasks:
                node_id, phase = tasks.pop()
                state = (node_id, phase % period)
                queued.discard(state)
                if state in discovered:
                    continue
                if charged >= max_states:
                    break
                engine.ledger.reserve(engine.scratch_owner, entries=1, nodes=1)
                charged += 1
                discovered.add(state)
                node = engine.arena.nodes[node_id]
                if node.kind == "EMPTY":
                    terminal_values[state] = True
                    continue
                if node.kind == "TERM":
                    terminal_values[state] = node.symbol == motif[state[1]]
                    continue
                children: tuple[tuple[int, int], ...]
                if node.kind == "CONCAT":
                    children = (
                        (node.left, state[1]),
                        (
                            node.right,
                            (state[1] + engine.arena.nodes[node.left].length) % period,
                        ),
                    )
                elif node.kind == "REPEAT":
                    advance = engine.arena.nodes[node.child].length % period
                    phase_cycle = period // gcd(period, advance) if advance else 1
                    children = tuple(
                        (node.child, (state[1] + offset * advance) % period)
                        for offset in range(min(node.count, phase_cycle))
                    )
                else:
                    raise ValueError("unknown source SLP node kind")
                dependencies[state] = children
                for child_id, child_phase in children:
                    child_state = (child_id, child_phase % period)
                    if child_state not in discovered and child_state not in queued:
                        tasks.append(child_state)
                        queued.add(child_state)

            if len(discovered) <= max_states and not tasks:
                dependents: dict[tuple[int, int], set[tuple[int, int]]] = {}
                remaining: dict[tuple[int, int], set[tuple[int, int]]] = {}
                ready: list[tuple[int, int]] = []
                for state in discovered:
                    child_states = set(dependencies.get(state, ()))
                    remaining[state] = child_states
                    if not child_states:
                        ready.append(state)
                    for child in child_states:
                        dependents.setdefault(child, set()).add(state)
                resolved = dict(terminal_values)
                while ready:
                    state = ready.pop()
                    if state not in resolved:
                        resolved[state] = all(
                            resolved[child] for child in dependencies[state]
                        )
                    for parent in dependents.get(state, ()):
                        waiting = remaining[parent]
                        waiting.discard(state)
                        if not waiting:
                            ready.append(parent)
                certified = resolved.get((root, 0)) is True
            if certified:
                return motif
        except BlockContextBudgetExceeded:
            return None
        finally:
            if charged:
                engine.ledger.release(
                    engine.scratch_owner, entries=charged, nodes=charged
                )
            engine.ledger.bump(
                keys.DOUBLE_REVERSE_POINTED_RING_PERIODIC_GUARD_STATES, charged
            )
    return None


def _periodic_evolve(
    engine: _RingSource,
    motif: tuple[int, ...],
    steps: int,
    positions: tuple[int, ...],
) -> tuple[tuple[int, ...], dict[int, RingDigitAction]] | None:
    """Evolve a certified spatial ring and power exact selected carry words."""
    seen: dict[tuple[int, ...], int] = {}
    states: list[tuple[int, ...]] = []
    current = motif
    charged = 0

    def record_carry_ports(count: int) -> None:
        engine.ledger.bump(keys.DOUBLE_REVERSE_POINTED_RING_AFFINE_PORTS, count)

    def record_motif_cell() -> None:
        # Counts discovery and per-position lineage-validation stencil calls.
        engine.ledger.bump(
            keys.DOUBLE_REVERSE_POINTED_RING_PERIODIC_MOTIF_CELL_EVALUATIONS
        )

    def actions_for(
        final_state: tuple[int, ...], cycle_start: int, cycle_length: int
    ) -> dict[int, RingDigitAction]:
        actions: dict[int, RingDigitAction] = {}
        for position in positions:
            action = _periodic_lineage_action(
                states,
                cycle_start,
                cycle_length,
                steps,
                position,
                on_carry_ports=record_carry_ports,
                on_motif_cell=record_motif_cell,
            )
            initial_digit = motif[(position + steps) % len(motif)]
            result_digit = final_state[position % len(motif)]
            if action.apply(initial_digit % 5) != result_digit % 5:
                raise ArithmeticError(
                    "periodic F5 action disagrees with its exact digit endpoint"
                )
            actions[position] = RingDigitAction(
                position, initial_digit, result_digit, action
            )
        return actions

    try:
        for _ in range(steps):
            previous = seen.get(current)
            if previous is not None:
                cycle_start = previous
                cycle_length = len(states) - cycle_start
                final_index = cycle_start + (steps - cycle_start) % cycle_length
                final_state = states[final_index]
                actions = actions_for(final_state, cycle_start, cycle_length)
                return final_state, actions
            engine.ledger.reserve(engine.scratch_owner, entries=1, nodes=1)
            charged += 1
            seen[current] = len(states)
            states.append(current)
            next_state: list[int] = []
            for index in range(len(current)):
                engine.ledger.bump(
                    keys.DOUBLE_REVERSE_POINTED_RING_PERIODIC_MOTIF_CELL_EVALUATIONS
                )
                next_state.append(
                    stencil_cell(
                        current[index],
                        current[(index + 1) % len(current)],
                        current[(index + 2) % len(current)],
                    )
                )
            engine.ledger.bump(keys.DOUBLE_REVERSE_POINTED_RING_PERIODIC_MOTIF_STEPS)
            current = tuple(next_state)
        states.append(current)
        # No cycle was needed before the requested finite endpoint.
        final_state = current
        actions = actions_for(final_state, steps, 0)
        return final_state, actions
    except BlockContextBudgetExceeded:
        return None
    finally:
        if charged:
            engine.ledger.release(engine.scratch_owner, entries=charged, nodes=charged)


def _periodic_lineage_action(
    states: list[tuple[int, ...]],
    cycle_start: int,
    cycle_length: int,
    steps: int,
    position: int,
    *,
    on_carry_ports: Callable[[int], None],
    on_motif_cell: Callable[[], None],
) -> DigitCarryAffine:
    """Compose carries over a detected joint temporal/spatial orbit."""
    period = len(states[0])

    def state_at(tick: int) -> tuple[int, ...]:
        if tick < len(states):
            return states[tick]
        if cycle_length <= 0:
            raise AssertionError("missing periodic state cycle")
        return states[cycle_start + (tick - cycle_start) % cycle_length]

    def one_step(tick: int) -> DigitCarryAffine:
        row = state_at(tick)
        center = (position + steps - tick) % period
        left = row[(center - 1) % period]
        middle = row[center]
        right = row[(center + 1) % period]
        c0 = int(left >= 5)
        right_five = right % 5
        c1 = int(right_five >= 3 or (right_five == 2 and middle >= 5))
        on_carry_ports(2)
        on_motif_cell()
        result = stencil_cell(left, middle, right)
        following = state_at(tick + 1)
        if result != following[(center - 1) % period]:
            raise ArithmeticError("periodic ring carry disagrees with stencil output")
        return DigitCarryAffine.two_step(c0, c1)

    if steps <= cycle_start:
        action = DigitCarryAffine.identity()
        for tick in range(steps):
            action = action.then(one_step(tick))
        return action
    action = DigitCarryAffine.identity()
    for tick in range(cycle_start):
        action = action.then(one_step(tick))
    joint_period = lcm(cycle_length, period)
    remaining = steps - cycle_start
    if remaining < joint_period:
        for offset in range(remaining):
            action = action.then(one_step(cycle_start + offset))
        return action
    copies, tail = divmod(remaining, joint_period)
    cycle_action = DigitCarryAffine.identity()
    for offset in range(joint_period):
        cycle_action = cycle_action.then(one_step(cycle_start + offset))
    action = action.then(cycle_action.power(copies))
    for offset in range(tail):
        action = action.then(one_step(cycle_start + offset))
    return action


def _mask_digit(masks: tuple[int, ...], position: int) -> int:
    found: int | None = None
    for digit, plane in enumerate(masks):
        if (plane >> position) & 1:
            if found is not None:
                raise ArithmeticError("packed decimal planes overlap at a source cell")
            found = digit
    if found is not None:
        return found
    raise ArithmeticError("packed decimal planes do not contain exactly one digit")


def _two_step_row(
    masks: tuple[int, ...], length: int
) -> tuple[tuple[int, ...], int, int]:
    """Apply the exact radius-one T² digit law to ten bitplanes."""
    if length < 3:
        raise ValueError("packed two-step stencil requires three input cells")
    high = masks[5] | masks[6] | masks[7] | masks[8] | masks[9]
    rho = masks[3] | masks[4] | masks[8] | masks[9]
    residue_two = masks[2] | masks[7]
    gate = (rho >> 2) | ((high >> 1) & (residue_two >> 2))
    output = [0] * 10
    not_high = ~high
    not_gate = ~gate
    for residue in range(5):
        centers = (masks[residue] | masks[residue + 5]) >> 1
        for carry, left_domain in ((0, not_high), (1, high)):
            cells = centers & left_domain
            if cells:
                base = (4 * residue + 2 * carry) % 10
                output[base] |= cells & not_gate
                output[(base + 1) % 10] |= cells & gate
    cap = (1 << (length - 2)) - 1
    return tuple(plane & cap for plane in output), high, gate


def _window_geometry(
    steps: int, phase: int, request: RingWindowRequest
) -> tuple[int, int]:
    left_births, _ = growth_ports(phase, steps)
    center = request.start - left_births + (request.count - 1) // 2
    radius = steps + request.count // 2
    begin = center - radius
    end = center + radius + 1
    return begin, end


def _validate_request(
    engine: _RingSource,
    root: int,
    steps: int,
    phase: int,
    request: RingWindowRequest,
) -> None:
    if (
        type(root) is not int
        or not 0 <= root < len(engine.arena.nodes)
        or type(steps) is not int
        or steps < 0
        or type(phase) is not int
        or phase not in (0, 1, 2, 3)
        or type(request) is not RingWindowRequest
        or type(request.start) is not int
        or type(request.count) is not int
        or not 1 <= request.count <= 18
        or type(request.positions) is not tuple
        or any(
            type(position) is not int or not 0 <= position < request.count
            for position in request.positions
        )
        or len(set(request.positions)) != len(request.positions)
    ):
        raise ValueError("packed ring requires a valid source and window")
    width = engine.arena.nodes[root].length + sum(growth_ports(phase, steps))
    if request.start < 0 or request.start + request.count > width:
        raise IndexError("packed ring request is outside the authenticated output")


def _evaluate_causal_window(
    engine: _RingSource,
    causal_root: int,
    steps: int,
    selected: tuple[tuple[int, int], ...],
) -> tuple[tuple[int, ...], dict[int, RingDigitAction]]:
    source_cells = engine.arena.nodes[causal_root].length
    if source_cells <= 2 * steps:
        raise ValueError("packed causal source window has no endpoint row")
    required_cells = source_cells - 2 * steps
    # Reserve the byte row, ten packed planes, simultaneous input/output masks,
    # and bounded temporary arithmetic before reading or materializing source.
    # Iteration tasks reserve their own live stack slots as well.
    reservation = max(8 * source_cells, 128)
    traversed = 0
    with engine.ledger.reservation(
        engine.scratch_owner, entries=reservation, nodes=reservation
    ):

        def reserve_task() -> None:
            engine.ledger.reserve(engine.scratch_owner, entries=1, nodes=1)

        def release_tasks(count: int) -> None:
            engine.ledger.release(engine.scratch_owner, entries=count, nodes=count)

        digits = bytearray()
        try:
            with closing(
                iter_symbols(
                    engine.arena,
                    causal_root,
                    reserve_task=reserve_task,
                    release_tasks=release_tasks,
                )
            ) as symbols:
                for symbol in symbols:
                    digits.append(symbol)
                    traversed += 1
        finally:
            if traversed:
                engine.ledger.bump(
                    keys.DOUBLE_REVERSE_POINTED_RING_SOURCE_CELLS,
                    traversed,
                )
        if len(digits) != source_cells:
            raise ArithmeticError("packed source traversal returned a short window")
        masks = _digits_to_masks(digits)
        action_positions = tuple(sorted({position for position, _ in selected}))
        actions = {
            position: DigitCarryAffine.identity() for position in action_positions
        }
        starts = {
            position: _mask_digit(masks, position + steps)
            for position in action_positions
        }
        length = source_cells
        for elapsed in range(steps):
            next_masks, high, gate = _two_step_row(masks, length)
            engine.ledger.bump(keys.DOUBLE_REVERSE_POINTED_RING_PACKED_STEPS)
            engine.ledger.bump(
                keys.DOUBLE_REVERSE_POINTED_RING_STENCIL_CELLS, length - 2
            )
            engine.ledger.bump(
                keys.DOUBLE_REVERSE_POINTED_RING_OPERAND_BITS,
                sum(plane.bit_length() for plane in masks)
                + sum(plane.bit_length() for plane in next_masks),
            )
            for result_position in action_positions:
                cell = result_position + steps - elapsed
                output_position = cell - 1
                left = _mask_digit(masks, output_position)
                center = _mask_digit(masks, cell)
                right = _mask_digit(masks, cell + 1)
                expected = stencil_cell(left, center, right)
                actual = _mask_digit(next_masks, output_position)
                if actual != expected:
                    raise ArithmeticError(
                        "packed row disagrees with exact digit stencil"
                    )
                carry_zero = (high >> output_position) & 1
                carry_one = (gate >> output_position) & 1
                engine.ledger.bump(keys.DOUBLE_REVERSE_POINTED_RING_AFFINE_PORTS, 2)
                actions[result_position] = actions[result_position].then(
                    DigitCarryAffine.two_step(carry_zero, carry_one)
                )
            masks = next_masks
            length -= 2
        if length != required_cells:
            raise ArithmeticError("packed evolution lost its finite endpoint width")
        values = tuple(_mask_digit(masks, index) for index in range(required_cells))
        result: dict[int, RingDigitAction] = {}
        for result_position, action_position in selected:
            action = actions[result_position]
            value = values[result_position]
            initial = starts[result_position]
            if action.apply(initial % 5) != value % 5:
                raise ArithmeticError("F5 carry action disagrees with packed digit")
            if action.physical_ticks % 4 == 0:
                c0, c1, c2, c3 = action.phase_counts
                expected_offset = (3 * c0 + 4 * c1 + 2 * c2 + c3) % 5
                if action.offset != expected_offset or action.multiplier != 1:
                    raise ArithmeticError(
                        "four-phase carry totals disagree with F5 action"
                    )
            result[action_position] = RingDigitAction(
                action_position, initial, value, action
            )
        engine.ledger.bump(keys.DOUBLE_REVERSE_POINTED_RING_AFFINE_DIGITS, len(result))
        engine.ledger.bump(
            keys.DOUBLE_REVERSE_POINTED_RING_AFFINE_LOGICAL_PORTS,
            2 * steps * len(result),
        )
        return values, result


def pointed_ring_windows(
    engine: _RingSource,
    root: int,
    steps: int,
    phase: int,
    requests: tuple[RingWindowRequest, ...],
) -> tuple[RingWindowResult, ...]:
    """Read overlapping demands from one SLP cone and one packed evolution."""
    if type(requests) is not tuple or not requests:
        raise ValueError("packed ring needs at least one output window")
    if len(requests) > _MAX_PAIRED_RING_WINDOWS:
        raise ValueError("packed ring accepts at most two paired output windows")
    if (
        type(root) is not int
        or not 0 <= root < len(engine.arena.nodes)
        or type(steps) is not int
        or steps < 0
        or type(phase) is not int
        or phase not in (0, 1, 2, 3)
    ):
        raise ValueError("packed ring requires a valid source, step count, and phase")
    if steps > engine.max_steps // 2:
        raise ValueError("packed ring exceeds its temporal owner budget")
    for request in requests:
        _validate_request(engine, root, steps, phase, request)
    if engine.certify(root) != phase:
        raise ValueError("packed ring source does not have the requested border phase")
    geometries = tuple(_window_geometry(steps, phase, request) for request in requests)
    order = sorted(range(len(requests)), key=lambda index: geometries[index][0])
    groups: list[list[int]] = []
    group_end = -1
    for index in order:
        begin, end = geometries[index]
        if groups and begin <= group_end:
            groups[-1].append(index)
            group_end = max(group_end, end)
        else:
            groups.append([index])
            group_end = end
    results: list[RingWindowResult | None] = [None] * len(requests)
    left_births, _ = growth_ports(phase, steps)
    for group in groups:
        begin = min(geometries[index][0] for index in group)
        end = max(geometries[index][1] for index in group)
        span = end - begin
        radius = span // 2
        center = begin + radius
        engine.ledger.bump(keys.DOUBLE_REVERSE_POINTED_RING_WINDOW_ATTEMPTS)
        try:
            causal = engine._pointed_source_window(root, center, radius)
            if engine.arena.nodes[causal].length not in (span, span + 1):
                raise AssertionError("merged causal cone has an unexpected right halo")
            selected: list[tuple[int, int, int]] = []
            for index in group:
                request = requests[index]
                for position in request.positions:
                    row_position = (
                        request.start - left_births - begin - steps + position
                    )
                    if (
                        not 0
                        <= row_position
                        < engine.arena.nodes[causal].length - 2 * steps
                    ):
                        raise AssertionError(
                            "selected output escaped its merged causal cone"
                        )
                    selected.append((row_position, index, position))
            row_to_action: dict[int, int] = {}
            action_ids: dict[tuple[int, int], int] = {}
            for row_position, index, position in selected:
                action_id = row_to_action.setdefault(row_position, len(row_to_action))
                action_ids[(index, position)] = action_id
            selected_actions = tuple(
                (row_position, action_id)
                for row_position, action_id in row_to_action.items()
            )
            periodic: tuple[tuple[int, ...], dict[int, RingDigitAction]] | None = None
            if steps >= 16 and selected_actions:
                engine.ledger.bump(keys.DOUBLE_REVERSE_POINTED_RING_PERIODIC_ATTEMPTS)
                motif = _certified_periodic_motif(engine, causal)
                if motif is not None:
                    periodic = _periodic_evolve(
                        engine,
                        motif,
                        steps,
                        tuple(row_position for row_position, _ in selected_actions),
                    )
            if periodic is None:
                selected_for_action = tuple(
                    (row_position, action_id)
                    for row_position, action_id in selected_actions
                )
                values, actions = _evaluate_causal_window(
                    engine, causal, steps, selected_for_action
                )
            else:
                final_motif, periodic_actions = periodic
                actions = {
                    action_id: periodic_actions[row_position]
                    for row_position, action_id in selected_actions
                }
                required_cells = engine.arena.nodes[causal].length - 2 * steps
                values = tuple(
                    final_motif[index % len(final_motif)]
                    for index in range(required_cells)
                )
                engine.ledger.bump(keys.DOUBLE_REVERSE_POINTED_RING_PERIODIC_HITS)
                engine.ledger.bump(
                    keys.DOUBLE_REVERSE_POINTED_RING_AFFINE_DIGITS,
                    len(actions),
                )
                engine.ledger.bump(
                    keys.DOUBLE_REVERSE_POINTED_RING_AFFINE_LOGICAL_PORTS,
                    2 * steps * len(actions),
                )
                engine.ledger.bump(
                    keys.DOUBLE_REVERSE_POINTED_RING_STENCIL_CELLS,
                    steps * (engine.arena.nodes[causal].length - 2)
                    - steps * (steps - 1),
                )
            for index in group:
                request = requests[index]
                output_start = request.start - left_births - begin - steps
                window_digits = tuple(
                    values[output_start + offset] for offset in range(request.count)
                )
                requested_actions = []
                for position in request.positions:
                    action = actions[action_ids[(index, position)]]
                    requested_actions.append(
                        RingDigitAction(
                            position,
                            action.initial_digit,
                            action.result_digit,
                            action.action,
                        )
                    )
                results[index] = RingWindowResult(
                    window_digits, tuple(requested_actions)
                )
            engine.ledger.bump(keys.DOUBLE_REVERSE_POINTED_RING_WINDOWS)
        except BaseException:
            engine.ledger.bump(keys.DOUBLE_REVERSE_POINTED_RING_FAILED_WORK)
            raise
    engine.ledger.bump(
        keys.DOUBLE_REVERSE_POINTED_STENCIL_PUBLICATIONS,
        sum(request.count for request in requests),
    )
    if any(result is None for result in results):
        raise AssertionError("packed ring did not publish every requested window")
    return cast(tuple[RingWindowResult, ...], tuple(results))


__all__ = [
    "RingDigitAction",
    "RingWindowRequest",
    "RingWindowResult",
    "initialize_packed_ring_metrics",
    "pointed_ring_windows",
]
