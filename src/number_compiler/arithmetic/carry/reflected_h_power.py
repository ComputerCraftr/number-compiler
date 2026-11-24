"""Source-bounded reflected multiplication using padded H cones."""

from __future__ import annotations

from collections.abc import Callable
from contextlib import closing
from dataclasses import dataclass
from itertools import count

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp_interval import (
    fold_slp_dag,
    fold_slp_interval,
)
from number_compiler.arithmetic.automata.slp_walks import iter_symbols, symbol_at
from number_compiler.arithmetic.automata.temporal_cone import (
    CarrySpacetimePower,
    TemporalSquareScratchReservation,
)
from number_compiler.arithmetic.carry.decimal_slp_action import multiply_decimal_slp
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.radix import (
    digits_lsd,
    reverse_decimal_and_width,
)
from number_compiler.resources.ledger import LedgerReservation, ResourceLedger
from number_compiler.resources.metric_keys import arithmetic_carry as carry_keys

_CELL_ARENA_SERIAL = count()


def padded_h_workload(seed: int, steps: int, max_state_bits: int) -> bool:
    """Select the measured wide-source domain within a conservative width bound."""
    bits = seed.bit_length()
    if bits < 425 or not 256 <= steps <= 4096:
        return False
    width_bound = (bits * 30103 + 99999) // 100000
    return (3322 * (width_bound + steps + 1) + 999) // 1000 <= max_state_bits


def padded_h_cell(previous: int, current: int, multiplier: int) -> int:
    low_previous, high_previous = previous % 10, previous // 10
    low, high = current % 10, current // 10
    divisor = 10 // multiplier
    before = multiplier * (high_previous % divisor) + low_previous // divisor
    first = multiplier * (low % divisor) + high_previous // divisor
    second = multiplier * (high % divisor) + low // divisor
    return (
        first // divisor
        + multiplier * (before % divisor)
        + 10 * (second // divisor + multiplier * (first % divisor))
    )


def padded_h_kernel(multiplier: int) -> Callable[[int, int], int]:
    """Compile the finite cell law from its two independent predecessor ports."""
    if type(multiplier) is not int or multiplier not in (2, 5):
        raise ValueError("reflected multiplier must be 2 or 5")
    divisor = 10 // multiplier
    incoming = bytes(previous // 10 // divisor for previous in range(100))
    offset = bytes(
        multiplier
        * (
            (multiplier * (previous // 10 % divisor) + previous % 10 // divisor)
            % divisor
        )
        for previous in range(100)
    )
    cells = bytearray()
    for current in range(100):
        low, high = current % 10, current // 10
        start = multiplier * (low % divisor)
        end = 10 * ((multiplier * (high % divisor) + low // divisor) // divisor)
        for carry in range(multiplier):
            first = start + carry
            cells.append(first // divisor + 10 * multiplier * (first % divisor) + end)
    contributions = bytes(cells)

    def transition(previous: int, current: int) -> int:
        return (
            offset[previous] + contributions[multiplier * current + incoming[previous]]
        )

    return transition


def _normalize(source: tuple[int, ...]) -> tuple[int, ...]:
    end = len(source)
    while end and source[end - 1] == 0:
        end -= 1
    if not end:
        return (0,)
    start = 0
    while source[start] == 0:
        start += 1
    if source[start] % 10:
        return source[start:end]
    # Dropping one low digit brings the next cell's low digit into this cell.
    # A last one-digit cell moves wholly into the preceding result.
    stop = end - int(source[end - 1] < 10)
    return tuple(
        source[i] // 10 + (10 * (source[i + 1] % 10) if i + 1 < end else 0)
        for i in range(start, stop)
    )


@dataclass(frozen=True, slots=True)
class _AdjacentCellSummary:
    """First/last inlet and all internal adjacent-cell outputs as an SLP."""

    first: int | None
    last: int | None
    internal: int


def _cell_interval(arena: LedgerSLPArena, root: int, start: int, end: int) -> int:
    """Select a cell interval without enumerating CONCAT/REPEAT occurrences."""
    return fold_slp_interval(
        arena,
        root,
        start,
        end,
        identity=arena.empty_id,
        length=lambda node: arena.nodes[node].length,
        full_value=lambda node, _reverse: node,
        compose=arena.concat,
        repeat=arena.repeat,
    )


def _adjacent_cell_summary(
    source: LedgerSLPArena,
    root: int,
    emit_pair: Callable[[int, int], int],
    output: LedgerSLPArena,
    ledger: ResourceLedger,
    owner: int,
    *,
    reverse_output: bool = False,
) -> _AdjacentCellSummary:
    """Apply a one-sided cell transducer to a shared SLP in graph order.

    CONCAT emits one boundary response and REPEAT creates one repeated bridge
    action. Neither operation visits the repeated physical occurrences.
    """
    empty = _AdjacentCellSummary(None, None, output.empty_id)

    def join(
        left: _AdjacentCellSummary, right: _AdjacentCellSummary
    ) -> _AdjacentCellSummary:
        if left.first is None:
            return right
        if right.first is None:
            return left
        assert left.last is not None and right.last is not None
        bridge = emit_pair(left.last, right.first)
        first, second = (
            (right.internal, left.internal)
            if reverse_output
            else (left.internal, right.internal)
        )
        return _AdjacentCellSummary(
            left.first,
            right.last,
            output.concat_many((first, bridge, second)),
        )

    def repeat(node: _AdjacentCellSummary, count: int) -> _AdjacentCellSummary:
        if node.first is None or count == 0:
            return empty
        if count == 1:
            return node
        assert node.last is not None
        bridge = emit_pair(node.last, node.first)
        unit = output.concat(bridge, node.internal)
        return _AdjacentCellSummary(
            node.first,
            node.last,
            output.concat(node.internal, output.repeat(unit, count - 1)),
        )

    # Charge each in-flight fold task and each retained node summary before
    # constructing the corresponding dictionaries. The output SLP nodes are
    # independently charged by the arena's canonical stores.
    with LedgerReservation(ledger, owner) as reserve:

        def reserve_slot(_node: int) -> None:
            reserve.reserve(entries=1, nodes=1)

        def release_slot(_node: int) -> None:
            reserve.release(entries=1, nodes=1)

        values = fold_slp_dag(
            source,
            root,
            empty_value=empty,
            terminal_value=lambda cell: _AdjacentCellSummary(
                cell, cell, output.empty_id
            ),
            concatenate=join,
            repeat=repeat,
            on_schedule=reserve_slot,
            on_unschedule=release_slot,
            on_evaluate=reserve_slot,
        )
        try:
            return values[root]
        finally:
            values.clear()


def _slp_zero_edges(
    arena: LedgerSLPArena,
    root: int,
    ledger: ResourceLedger,
    owner: int,
) -> tuple[int, int]:
    """Count zero edges without visiting grammar interior after a nonzero cell."""

    def edge(reverse: bool) -> int:
        count = 0
        # A repeat marker is reached only if its first child copy was all
        # zero. A completion marker authenticates a zero-only subtree, so a
        # shared DAG of zero cells never expands like a tree.
        visit, repeat_remainder, complete = range(3)
        tasks: list[tuple[int, int]] = []
        zero_nodes: set[int] = set()
        with LedgerReservation(ledger, owner) as reserve:

            def push(kind: int, value: int) -> None:
                reserve.reserve(entries=1, nodes=1)
                tasks.append((kind, value))

            try:
                push(visit, root)
                while tasks:
                    kind, value = tasks.pop()
                    reserve.release(entries=1, nodes=1)
                    if kind == repeat_remainder:
                        count += value
                        continue
                    if kind == complete:
                        if value not in zero_nodes:
                            reserve.reserve(entries=1, nodes=1)
                            zero_nodes.add(value)
                        continue
                    node_id = value
                    node = arena.nodes[node_id]
                    if node_id in zero_nodes:
                        count += node.length
                        continue
                    if node.kind == "EMPTY":
                        continue
                    if node.kind == "TERM":
                        if node.symbol != 0:
                            break
                        count += 1
                    elif node.kind == "CONCAT":
                        first, second = (
                            (node.right, node.left)
                            if reverse
                            else (node.left, node.right)
                        )
                        push(complete, node_id)
                        push(visit, second)
                        push(visit, first)
                    elif node.kind == "REPEAT":
                        push(complete, node_id)
                        push(
                            repeat_remainder,
                            (node.count - 1) * arena.nodes[node.child].length,
                        )
                        push(visit, node.child)
                    else:
                        raise ValueError("invalid SLP node kind")
            finally:
                tasks.clear()
                zero_nodes.clear()
        return count

    start = edge(False)
    return start, start if start == arena.nodes[root].length else edge(True)


def normalize_reflected_cell_slp(
    arena: LedgerSLPArena, root: int, ledger: ResourceLedger, owner: int
) -> int:
    """Exact physical base-100 normalization on SLP roots, including 10 shifts."""
    width = arena.nodes[root].length
    start, suffix = _slp_zero_edges(arena, root, ledger, owner)
    if start == width:
        return arena.terminal(0)
    end = width - suffix
    if start or end != width:
        root = _cell_interval(arena, root, start, end)
    if symbol_at(arena, root, 0) % 10:
        return root
    # A one-decimal-digit shift is a radius-one action on base-100 cells.
    # Pair actions commute with SLP concatenation modulo the seam digit.
    summary = _adjacent_cell_summary(
        arena,
        root,
        lambda left, right: arena.terminal(left // 10 + 10 * (right % 10)),
        arena,
        ledger,
        owner,
    )
    assert summary.last is not None
    if summary.last < 10:
        return summary.internal
    return arena.concat(summary.internal, arena.terminal(summary.last // 10))


def _decimal_slp_from_cells(
    cells: LedgerSLPArena,
    root: int,
    multiplier: int,
    output: LedgerSLPArena,
    owner: int,
    *,
    even: bool,
) -> int:
    """Publish decimal digits and carry seams in one source-DAG fold."""
    if type(multiplier) is not int or multiplier not in (2, 5):
        raise ValueError("reflected multiplier must be 2 or 5")
    divisor = 100 // multiplier

    def two_digits(cell: int) -> int:
        return output.word((cell // 10, cell % 10))

    summary = _adjacent_cell_summary(
        cells,
        root,
        lambda left, right: two_digits(multiplier * right % 100 + left // divisor),
        output,
        output.ledger,
        owner,
        reverse_output=True,
    )
    if summary.first is None or summary.last is None:
        return output.terminal(0)
    decimal = output.concat(
        summary.internal, two_digits(multiplier * summary.first % 100)
    )
    carry = summary.last // divisor
    if carry:
        decimal = output.concat(output.terminal(carry), decimal)
    if not even:
        if symbol_at(output, decimal, 0) == 0:
            decimal = _cell_interval(output, decimal, 1, output.nodes[decimal].length)
        return decimal
    # The physical even endpoint is 2*reverse10(N(2*odd_track)). The
    # normalization is applied before this final multiplication, preserving
    # real trailing zeros such as 50 -> 10 on the physical odd track.
    decimal_width = output.nodes[decimal].length
    leading_zeros, trailing_zeros = _slp_zero_edges(
        output, decimal, output.ledger, owner
    )
    if leading_zeros == decimal_width:
        return output.terminal(0)
    end = decimal_width - trailing_zeros
    if leading_zeros or end != decimal_width:
        decimal = _cell_interval(output, decimal, leading_zeros, end)
    action = multiply_decimal_slp(output, decimal, multiplier, output.ledger, owner)
    multiplied, final_carry = action.resolve(output, 0)
    if final_carry:
        multiplied = output.concat(multiplied, output.terminal(final_carry))
    with LedgerReservation(output.ledger, owner) as reserve:

        def reserve_slot(_node: int) -> None:
            reserve.reserve(entries=1, nodes=1)

        def release_slot(_node: int) -> None:
            reserve.release(entries=1, nodes=1)

        rows = fold_slp_dag(
            output,
            multiplied,
            empty_value=output.empty_id,
            terminal_value=output.terminal,
            concatenate=lambda left, right: output.concat(right, left),
            repeat=output.repeat,
            on_schedule=reserve_slot,
            on_unschedule=release_slot,
            on_evaluate=reserve_slot,
        )
        try:
            return rows[multiplied]
        finally:
            rows.clear()


def _exact_periodic_cell_source(arena: LedgerSLPArena, cells: tuple[int, ...]) -> int:
    """Compile an *authenticated finite* periodic cell source before H work.

    The source has already been decoded at the inlet. Check actual equality
    against candidate periods (including at most two exceptional cells at
    either physical end) before issuing any REPEAT node. This is not temporal
    cycle discovery: it never extends the given finite word or replays H.
    Small/dense inputs use the original word constructor unchanged.
    """
    size = len(cells)
    if size < 128:
        return arena.word(cells)
    comparisons_left = 4 * size
    for period in range(1, min(16, size // 4) + 1):
        for total_fringe in range(5):
            for left in range(min(2, total_fringe) + 1):
                right = total_fringe - left
                if right > 2:
                    continue
                length = size - left - right
                if length < 4 * period or length % period:
                    continue
                for index in range(left + period, size - right):
                    if comparisons_left == 0:
                        return arena.word(cells)
                    comparisons_left -= 1
                    if cells[index] != cells[left + (index - left) % period]:
                        break
                else:
                    center = arena.repeat(
                        arena.word(cells[left : left + period]),
                        length // period,
                    )
                    return arena.concat_many(
                        (
                            arena.word(cells[:left]),
                            center,
                            arena.word(cells[size - right :])
                            if right
                            else arena.empty_id,
                        )
                    )
    return arena.word(cells)


def _padded_h_inlet(
    digits: tuple[int, ...], generation: int, multiplier: int
) -> tuple[tuple[int, ...], int]:
    """One physical odd/even inlet authority for both exact H executors."""
    if multiplier == 5 and generation % 2 == 0:
        previous = 0
        inlet: list[int] = []
        for digit in digits:
            inlet.append(digit // 2 + 5 * (previous % 2))
            previous = digit
        inlet.append(5 * (previous % 2))
        source = tuple(
            inlet[i] + (10 * inlet[i + 1] if i + 1 < len(inlet) else 0)
            for i in range(0, len(inlet), 2)
        )
        return source, generation // 2 - 1
    # The 2rev10 even projection reads the same odd track backwards.
    source = tuple(
        digits[-1 - i] + (10 * digits[-2 - i] if i + 1 < len(digits) else 0)
        for i in range(0, len(digits), 2)
    )
    return source, ((generation - 1) // 2 if generation % 2 else generation // 2 - 1)


def _admit_padded_h_inlet(
    seed: int, generation: int, multiplier: int, max_state_bits: int
) -> tuple[tuple[int, ...], int]:
    digits = digits_lsd(seed, 10)
    bound_bits = (3322 * (len(digits) + generation + 1) + 999) // 1000
    if bound_bits > max_state_bits:
        raise BlockContextBudgetExceeded("padded cone exceeds proved width envelope")
    return _padded_h_inlet(digits, generation, multiplier)


def _retire_padded_h_power(
    bank: CarrySpacetimePower, ledger: ResourceLedger, transitions: int
) -> None:
    try:
        stats = bank.stats
        ledger.bump(carry_keys.REFLECTED_H_PRIMITIVE_TRANSITIONS, transitions)
        ledger.bump(carry_keys.REFLECTED_H_COMPUTED_CONES, stats.temporal_cones)
        ledger.bump(carry_keys.REFLECTED_H_REUSED_CONES, stats.reused_cones)
    finally:
        bank.release_temporary_storage()


def _padded_h_execute_slp(
    seed: int,
    generation: int,
    multiplier: int,
    *,
    ledger: ResourceLedger,
    scratch_owner: int,
    max_state_bits: int,
    emit: Callable[[LedgerSLPArena, int, bool], int],
) -> int:
    """Execute selected dyadic H powers through a *single* cell-SLP arena."""
    if (
        type(seed) is not int
        or seed < 0
        or type(generation) is not int
        or generation < 0
        or type(multiplier) is not int
        or multiplier not in (2, 5)
        or type(max_state_bits) is not int
        or max_state_bits < 1
    ):
        raise ValueError("invalid reflected source, generation or budget")
    if seed.bit_length() > max_state_bits:
        raise BlockContextBudgetExceeded("reflected source exceeds state-bit budget")
    width_bound = (seed.bit_length() * 30103 + 99999) // 100000 + 1
    if seed == 0 or generation == 0:
        return _padded_h_execute(
            seed,
            generation,
            multiplier,
            ledger=ledger,
            scratch_owner=scratch_owner,
            max_state_bits=max_state_bits,
            emit=lambda items, even: _single_cell_slp_emit(
                items, even, ledger, scratch_owner, emit
            ),
        )
    with ledger.reservation(
        scratch_owner,
        entries=4 * (width_bound + 4),
        nodes=4 * (width_bound + 4),
    ):
        source, steps = _admit_padded_h_inlet(
            seed, generation, multiplier, max_state_bits
        )
        cell_arena = LedgerSLPArena(
            ledger, f"reflected-h-cell-{next(_CELL_ARENA_SERIAL)}", "reflected_h"
        )
        reservation = LedgerReservation(ledger, scratch_owner)
        transitions = 0
        kernel = padded_h_kernel(multiplier)

        def transition(a: int, b: int) -> int:
            nonlocal transitions
            transitions += 1
            return kernel(a, b)

        try:
            cell_root = normalize_reflected_cell_slp(
                cell_arena,
                _exact_periodic_cell_source(cell_arena, source),
                ledger,
                scratch_owner,
            )
            with TemporalSquareScratchReservation(reservation) as scratch:
                bank = CarrySpacetimePower(scratch, None, None, cell_action=transition)
                try:
                    for bit in range(steps.bit_length() - 1, -1, -1):
                        if steps & (1 << bit):
                            cell_root = normalize_reflected_cell_slp(
                                cell_arena,
                                bank.advance_blocks_slp(
                                    cell_arena, cell_root, 1 << bit
                                ),
                                ledger,
                                scratch_owner,
                            )
                    return emit(
                        cell_arena,
                        cell_root,
                        multiplier == 2 and generation % 2 == 0,
                    )
                finally:
                    _retire_padded_h_power(bank, ledger, transitions)
        finally:
            cell_arena.dispose()


def _single_cell_slp_emit(
    items: list[int],
    even: bool,
    ledger: ResourceLedger,
    owner: int,
    emit: Callable[[LedgerSLPArena, int, bool], int],
) -> int:
    arena = LedgerSLPArena(
        ledger, f"reflected-h-single-{next(_CELL_ARENA_SERIAL)}", "reflected_h"
    )
    try:
        return emit(arena, arena.word(items), even)
    finally:
        arena.dispose()


def _padded_h_execute(
    seed: int,
    generation: int,
    multiplier: int,
    *,
    ledger: ResourceLedger,
    scratch_owner: int,
    max_state_bits: int,
    emit: Callable[[list[int], bool], int],
) -> int:
    """Compute a bounded physical endpoint via the same ledgered cone arena."""
    if (
        type(seed) is not int
        or seed < 0
        or type(generation) is not int
        or generation < 0
    ):
        raise ValueError("invalid reflected source or generation")
    if multiplier not in (2, 5) or type(multiplier) is not int:
        raise ValueError("reflected multiplier must be 2 or 5")
    if type(max_state_bits) is not int or max_state_bits < 1:
        raise ValueError("state-bit budget must be a positive integer")
    if seed.bit_length() > max_state_bits:
        raise BlockContextBudgetExceeded("reflected source exceeds state-bit budget")
    width_bound = (seed.bit_length() * 30103 + 99999) // 100000 + 1
    if seed == 0 or generation == 0:
        with ledger.reservation(scratch_owner, nodes=2 * width_bound):
            cells = []
            value = seed
            while value:
                value, digit = divmod(value, 100)
                cells.append(digit)
            return emit(cells or [0], False)
    with ledger.reservation(
        scratch_owner,
        entries=4 * (width_bound + generation + 1),
        nodes=4 * (width_bound + generation + 1),
    ):
        source, steps = _admit_padded_h_inlet(
            seed, generation, multiplier, max_state_bits
        )
        source = _normalize(source)
        reservation = LedgerReservation(ledger, scratch_owner)
        transitions = 0
        kernel: Callable[[int, int], int] | None = None

        def transition(left: int, right: int) -> int:
            nonlocal transitions
            transitions += 1
            return (
                padded_h_cell(left, right, multiplier)
                if kernel is None
                else kernel(left, right)
            )

        with TemporalSquareScratchReservation(reservation) as scratch:
            # Two 100-byte predecessor ports and two copies of at most
            # 500 bytes while freezing the contribution table.
            try:
                scratch.acquire(entries=4, nodes=320)
            except BlockContextBudgetExceeded:
                pass
            else:
                kernel = padded_h_kernel(multiplier)
            bank = CarrySpacetimePower(scratch, None, None, cell_action=transition)
            try:
                for bit in range(steps.bit_length() - 1, -1, -1):
                    if steps & (1 << bit):
                        source = _normalize(bank.advance_blocks(source, 1 << bit))
                carry = 0
                output: list[int] = []
                for cell in source:
                    carry, digit = divmod(multiplier * cell + carry, 100)
                    output.append(digit)
                if carry:
                    output.append(carry)
                return emit(output, multiplier == 2 and generation % 2 == 0)
            finally:
                _retire_padded_h_power(bank, ledger, transitions)


def padded_h_endpoint(
    seed: int,
    generation: int,
    multiplier: int,
    *,
    ledger: ResourceLedger,
    scratch_owner: int,
    max_state_bits: int,
    use_slp_power: bool = False,
) -> int:
    """Compute a bounded physical endpoint via the ledgered cone arena."""

    # The H track is SLP-persistent across dyadic powers. Only the requested
    # final integer must be constructed; the intermediate rows are never
    # materialized into whole-base-100 tuples.
    if type(use_slp_power) is not bool:
        raise TypeError("SLP powering selector must be Boolean")
    if use_slp_power and generation >= 128:

        def emit_slp(cells: LedgerSLPArena, root: int, even: bool) -> int:
            number = 0
            with closing(
                iter_symbols(
                    cells,
                    root,
                    reverse=True,
                    ledger=ledger,
                    owner=scratch_owner,
                )
            ) as symbols:
                for digit in symbols:
                    number = number * 100 + digit
            number *= multiplier
            if even:
                reflected, _width = reverse_decimal_and_width(number)
                return multiplier * reflected
            return number

        return _padded_h_execute_slp(
            seed,
            generation,
            multiplier,
            ledger=ledger,
            scratch_owner=scratch_owner,
            max_state_bits=max_state_bits,
            emit=emit_slp,
        )

    def emit(cells: list[int], even: bool) -> int:
        result = cells[-1]
        for i in range(len(cells) - 2, -1, -1):
            cell = cells[i]
            result = result * 100 + cell
        if even:
            reverse = 0
            while result:
                result, digit = divmod(result, 10)
                reverse = 10 * reverse + digit
            result = multiplier * reverse
        return result

    return _padded_h_execute(
        seed,
        generation,
        multiplier,
        ledger=ledger,
        scratch_owner=scratch_owner,
        max_state_bits=max_state_bits,
        emit=emit,
    )


def padded_h_publish(
    seed: int,
    generation: int,
    multiplier: int,
    *,
    arena: LedgerSLPArena,
    scratch_owner: int,
    max_state_bits: int,
    use_slp_power: bool = False,
) -> int:
    """Publish an exact MSD-first endpoint in the receiving SLP arena."""
    arena.empty()
    checkpoint = len(arena.nodes)
    if type(use_slp_power) is not bool:
        raise TypeError("SLP powering selector must be Boolean")
    # Keep the lower-cost tuple kernel for ordinary short/medium endpoints.
    # Explicit source-SLP consumers select the compressed intermediate path;
    # its cost is not universally lower for small physical words.
    if use_slp_power and generation >= 128:
        try:
            return _padded_h_execute_slp(
                seed,
                generation,
                multiplier,
                ledger=arena.ledger,
                scratch_owner=scratch_owner,
                max_state_bits=max_state_bits,
                emit=lambda cells, root, even: _decimal_slp_from_cells(
                    cells, root, multiplier, arena, scratch_owner, even=even
                ),
            )
        except BaseException as error:
            try:
                arena.rollback_unpublished_suffix(checkpoint)
            except BaseException as cleanup_error:
                raise error from cleanup_error
            raise

    def emit(cells: list[int], even: bool) -> int:
        top = cells[-1]
        digits = [top // 10, top % 10] if top >= 10 else [top]
        for i in range(len(cells) - 2, -1, -1):
            cell = cells[i]
            digits.extend((cell // 10, cell % 10))
        if not even:
            return arena.word(digits)
        while len(digits) > 1 and digits[-1] == 0:
            digits.pop()
        source = arena.word(digits)
        action = multiply_decimal_slp(
            arena, source, multiplier, arena.ledger, scratch_owner
        )
        output, carry = action.resolve(arena, 0)
        if carry:
            output = arena.concat(output, arena.terminal(carry))
        with arena.ledger.reservation(scratch_owner, nodes=4 * (len(arena.nodes) + 1)):
            rows = fold_slp_dag(
                arena,
                output,
                empty_value=arena.empty_id,
                terminal_value=arena.terminal,
                concatenate=lambda left, right: arena.concat(right, left),
                repeat=arena.repeat,
            )
            try:
                return rows[output]
            finally:
                rows.clear()

    try:
        return _padded_h_execute(
            seed,
            generation,
            multiplier,
            ledger=arena.ledger,
            scratch_owner=scratch_owner,
            max_state_bits=max_state_bits,
            emit=emit,
        )
    except BaseException as error:
        try:
            arena.rollback_unpublished_suffix(checkpoint)
        except BaseException as cleanup_error:
            raise error from cleanup_error
        raise
