"""Source-bounded reflected multiplication using padded H cones."""

from __future__ import annotations

from collections.abc import Callable

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp_interval import fold_slp_dag
from number_compiler.arithmetic.automata.temporal_cone import (
    CarrySpacetimePower,
    TemporalSquareScratchReservation,
)
from number_compiler.arithmetic.carry.decimal_slp_action import multiply_decimal_slp
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import LedgerReservation, ResourceLedger
from number_compiler.resources.metric_keys import arithmetic_carry as carry_keys


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
        digits = digits_lsd(seed, 10)
        if (3322 * (len(digits) + generation + 1) + 999) // 1000 > max_state_bits:
            raise BlockContextBudgetExceeded(
                "padded cone exceeds proved width envelope"
            )
        if multiplier == 5 and generation % 2 == 0:
            # E_5(seed) is the established even inlet, in LSD-first order.
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
            steps = generation // 2 - 1
        else:
            # The 2rev10 even projection reads the same odd track backwards.
            source = tuple(
                digits[-1 - i] + (10 * digits[-2 - i] if i + 1 < len(digits) else 0)
                for i in range(0, len(digits), 2)
            )
            steps = (generation - 1) // 2 if generation % 2 else generation // 2 - 1
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
                try:
                    stats = bank.stats
                    ledger.bump(
                        carry_keys.REFLECTED_H_PRIMITIVE_TRANSITIONS, transitions
                    )
                    ledger.bump(
                        carry_keys.REFLECTED_H_COMPUTED_CONES, stats.temporal_cones
                    )
                    ledger.bump(carry_keys.REFLECTED_H_REUSED_CONES, stats.reused_cones)
                finally:
                    bank.release_temporary_storage()


def padded_h_endpoint(
    seed: int,
    generation: int,
    multiplier: int,
    *,
    ledger: ResourceLedger,
    scratch_owner: int,
    max_state_bits: int,
) -> int:
    """Compute a bounded physical endpoint via the ledgered cone arena."""

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
) -> int:
    """Publish an exact MSD-first endpoint in the receiving SLP arena."""
    arena.empty()
    checkpoint = len(arena.nodes)

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
