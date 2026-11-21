"""Ledger-owned exact evidence for demanded physical palindrome prefixes."""

from contextlib import closing
from dataclasses import dataclass

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp_walks import iter_symbols
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.radix import reverse_decimal_and_width
from number_compiler.resources.ledger import ResourceLedger

from .boundary_cycles import CANDIDATE_COMPONENTS
from .temporal_mixed_adic_consumer import certified_edge_action


@dataclass(frozen=True, slots=True)
class PalindromeCursor:
    """A checked prefix of one source, independent of endpoint-only cursors."""

    seed: int
    generation: int
    arena_generation: int
    value: int | None
    first_hit: int | None = None
    c0_closed: bool = False


def cursor_nodes(_key: int, cursor: PalindromeCursor) -> int:
    """Account for the retained physical value and evidence."""
    return 8 + (0 if cursor.value is None else (cursor.value.bit_length() + 29) // 30)


def cursor_from_issued_prefix(
    seed: int,
    generation: int,
    root: int,
    first_hit: int | None,
    arena: LedgerSLPArena,
    ledger: ResourceLedger,
    scratch_owner: int,
    max_state_bits: int,
) -> PalindromeCursor:
    """Resume an authenticated finite prefix from its exact SLP endpoint."""
    width = arena.nodes[root].length
    with ledger.reservation(scratch_owner, entries=2 * width, nodes=2 * width):
        value = 0
        with closing(
            iter_symbols(arena, root, ledger=ledger, owner=scratch_owner)
        ) as digits:
            for digit in digits:
                value = value * 10 + digit
                if value.bit_length() > max_state_bits:
                    raise BlockContextBudgetExceeded(
                        "palindrome bridge exceeds the source bit budget"
                    )
    return PalindromeCursor(
        seed, generation, arena.node_id_generation, value, first_hit
    )


def advance_palindrome_cursor(
    cursor: PalindromeCursor,
    horizon: int,
    ledger: ResourceLedger,
    scratch_owner: int,
    max_state_bits: int,
) -> PalindromeCursor:
    """Extend only the not-yet-checked physical suffix of an event query."""
    certified_edge_action()
    edges = CANDIDATE_COMPONENTS[0]
    if any(edge[0] == edge[3] for edge in edges):
        raise AssertionError("C0 boundary permits a palindrome")
    step, value = cursor.generation, cursor.value
    if cursor.first_hit is not None or cursor.c0_closed:
        return cursor
    if type(value) is not int or value < 0:
        raise ValueError("resumable palindrome cursor lost its physical value")
    if step >= horizon:
        return cursor
    while True:
        width_bound = (value.bit_length() * 30103 + 99999) // 100000 + 1
        with ledger.reservation(
            scratch_owner, entries=2 * width_bound, nodes=2 * width_bound
        ):
            reflected, width = reverse_decimal_and_width(value)
            if step and value == reflected:
                return PalindromeCursor(
                    cursor.seed, step, cursor.arena_generation, None, step
                )
            if (
                width >= 5
                and (
                    reflected % 10,
                    reflected // 10 % 10,
                    value // 10 % 10,
                    value % 10,
                )
                in edges
            ):
                return PalindromeCursor(
                    cursor.seed, step, cursor.arena_generation, None, c0_closed=True
                )
            if step == horizon:
                return PalindromeCursor(
                    cursor.seed, step, cursor.arena_generation, value
                )
            value = 2 * reflected
            if value.bit_length() > max_state_bits:
                raise BlockContextBudgetExceeded(
                    "palindrome prefix exceeds the double-reverse state-bit budget"
                )
            step += 1
