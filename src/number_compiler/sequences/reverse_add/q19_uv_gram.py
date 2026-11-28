"""Source-guarded ordered carry Gram action for a bounded tile grammar."""

from __future__ import annotations

from collections.abc import Generator
from contextlib import contextmanager
from typing import TYPE_CHECKING

from number_compiler.arithmetic.automata.slp_interval import fold_slp_dag
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.metric_keys import reverse_add as keys
from number_compiler.resources.owned_memo import LedgerReservation

from .q19_gram_observation import GramFoldCharges
from .q19_ordered_gram import Q19OrderedGramAction

if TYPE_CHECKING:
    from .q19_occurrence import ReversePairOutputOccurrence
    from .q19_output import ReversePairQ19OutputOwner

_A = (1, 9, 5, 9, 1, 3, 7, 3)
_B = (1, 9, 5, 9, 5, 9, 1, 3, 7, 3)
_TILES = (_A + _A + _B + _A, _A + _B + _A + _A)
# The exact reachable deterministic states are bounded independently of source.
_STATE_BOUND = 128


def _transition(state: tuple[int, int, int], symbol: int) -> tuple[int, int, int]:
    stage, position, mask = state
    if stage == 0:
        return (1, 0, 0) if symbol == 19 else (5, 0, 0)
    if stage == 1:
        return (2, 0, 3) if symbol == 17 else (5, 0, 0)
    if stage == 3:
        return (4, 0, 0) if symbol == 21 else (5, 0, 0)
    if stage != 2:
        return (5, 0, 0)
    # Bit 4 records a complete tile.  The center is accepted only at a seam.
    if position == 0 and mask & 4 and symbol == 11:
        return (3, 0, 0)
    possible = mask & 3
    for index, tile in enumerate(_TILES):
        if symbol != tile[position]:
            possible &= ~(1 << index)
    if not possible:
        return (5, 0, 0)
    if position == 33:
        return (2, 0, 7)
    return (2, position + 1, possible | (mask & 4))


def _alphabet() -> tuple[tuple[int, ...], tuple[tuple[int, ...], ...], int]:
    start = (0, 0, 0)
    states: list[tuple[int, int, int]] = [start]
    indexes: dict[tuple[int, int, int], int] = {start: 0}
    columns: list[list[int]] = [[] for _ in range(22)]
    for state in states:
        for symbol, column in enumerate(columns):
            nxt = _transition(state, symbol)
            if nxt not in indexes:
                if len(states) >= _STATE_BOUND:
                    raise AssertionError(
                        "Q19 U/V recognition escaped its fixed state bound"
                    )
                indexes[nxt] = len(states)
                states.append(nxt)
            column.append(indexes[nxt])
    identity = tuple(range(len(states)))
    atoms = tuple(tuple(column) for column in columns)
    return identity, atoms, indexes[(4, 0, 0)]


def _then(first: tuple[int, ...], later: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(later[state] for state in first)


@contextmanager
def source_uv_gram(
    owner: ReversePairQ19OutputOwner,
    source: ReversePairOutputOccurrence,
    generation: int = 3,
) -> Generator[Q19OrderedGramAction | None, None, None]:
    """Probe exact source tiles and issue their ordered projection at the certified clock."""
    owner.validate_issued_occurrence(source)
    if owner.base != 10 or source is not owner.initial or source.temporal_steps != 1:
        raise ValueError("Q19 U/V action requires its initial decimal source")
    if generation not in (3, 9):
        raise ValueError("unsupported Q19 U/V projection clock")
    width = source.pair_width
    if width < 72 or width % 68 != 4:
        yield None
        return
    root = source.root
    if owner.arena.node_storage_poisoned:
        raise ValueError("Q19 U/V source grammar storage is stale")
    node = owner.arena.nodes[root]
    arena_generation = owner.arena.node_id_generation

    def check_source() -> None:
        if (
            owner.arena.node_storage_poisoned
            or owner.arena.node_id_generation != arena_generation
            or not 0 <= root < len(owner.arena.nodes)
            or owner.arena.nodes[root] is not node
        ):
            raise ValueError("Q19 U/V source grammar changed during admission")
        owner.validate_issued_occurrence(source)

    # The quotient and power-loop temporaries can have the source width's
    # bit length, so reserve their limbs before performing integer division.
    width_limbs = max(1, (width.bit_length() + 63) // 64)
    with LedgerReservation(owner.ledger, owner.scratch_owner) as width_reservation:
        try:
            width_reservation.reserve(nodes=64 * width_limbs)
        except BlockContextBudgetExceeded:
            check_source()
            yield None
            return
        n = width // 2 - 2

        def read(index: int) -> int:
            owner.ledger.bump(keys.REVERSE_Q19_UV_GUARD_READS)
            return owner.symbol_at(root, index)

        admitted_edges = not (
            node.length != n + 4
            or read(0) != 19
            or read(1) != 17
            or read(2) != 1
            or read(3) != 9
            or read(node.length - 3) != 3
            or read(node.length - 2) != 11
            or read(node.length - 1) != 21
        )
        check_source()
        if not admitted_edges:
            yield None
            return
        with LedgerReservation(owner.ledger, owner.scratch_owner) as reservation:
            try:
                # DFA discovery columns, frozen alphabet, pending composition
                # and all four output rows coexist during construction.
                reservation.reserve(nodes=46 * _STATE_BOUND + 2048)
            except BlockContextBudgetExceeded:
                check_source()
                yield None
                return
            identity, atoms, accepted = _alphabet()
            states = len(identity)
            owner.ledger.bump(keys.REVERSE_Q19_UV_GUARD_TRANSITIONS, 22 * states)

            def dfa_join(
                first: tuple[int, ...], later: tuple[int, ...]
            ) -> tuple[int, ...]:
                owner.ledger.bump(keys.REVERSE_Q19_UV_GUARD_TRANSITIONS, states)
                return _then(first, later)

            def repeat(action: tuple[int, ...], count: int) -> tuple[int, ...]:
                result = identity
                while count:
                    if count & 1:
                        result = dfa_join(result, action)
                    count //= 2
                    if count:
                        action = dfa_join(action, action)
                return result

            charges = GramFoldCharges(reservation)

            def evaluate(_node: int) -> None:
                reservation.reserve(entries=1, nodes=states + 2)
                owner.ledger.bump(keys.REVERSE_Q19_UV_GUARD_NODES)
                owner.ledger.bump(keys.REVERSE_Q19_GRAM_NODE_VISITS)

            def release_value(_node: int) -> None:
                reservation.release(entries=1, nodes=states + 2)

            def terminal(symbol: int) -> tuple[int, ...]:
                if type(symbol) is not int or not 0 <= symbol < len(atoms):
                    raise ValueError("invalid Q19 source symbol")
                return atoms[symbol]

            values = fold_slp_dag(
                owner.arena,
                root,
                empty_value=identity,
                terminal_value=terminal,
                concatenate=dfa_join,
                repeat=repeat,
                on_schedule=charges.schedule,
                on_unschedule=charges.unschedule,
                reclaim_values=True,
                on_reference_entry=charges.reference_entry,
                on_reference_release=charges.reference_release,
                on_evaluate=evaluate,
                on_value_release=release_value,
            )
            try:
                check_source()
                if values[root][0] != accepted:
                    yield None
                    return
                # The checked physical field is head, uniform twos, tail, center
                # and the reflected half in reverse order. Carry atoms distinguish
                # all three decimal domains even when a fringe is one digit wide.
                head: tuple[int, ...]
                tail: tuple[int, ...]
                center: tuple[int, ...]
                if generation == 3:
                    head, tail, center = (8, 7, 11), (3, 10), ()
                    copies = n - 2
                else:
                    head, tail, center = (4, 9, 6, 9, 9, 6, 6), (4, 5, 4, 8), (12,)
                    copies = n - 7
                atoms_by_domain: dict[int, Q19OrderedGramAction] = {}

                def atom(digit: int) -> Q19OrderedGramAction:
                    domain = min(10, max(8, digit))
                    if domain not in atoms_by_domain:
                        atoms_by_domain[domain] = Q19OrderedGramAction.atom(
                            domain, 1, 1_000_000_007, 3
                        )
                        owner.ledger.bump(keys.REVERSE_Q19_GRAM_ATOM_BUILDS)
                    return atoms_by_domain[domain]

                def compose() -> None:
                    owner.ledger.bump(keys.REVERSE_Q19_GRAM_COMPOSITIONS)

                core = atom(2).repeat(copies, on_compose=compose)
                result = atom(head[0])
                for digit in head[1:]:
                    result = result.then(atom(digit), on_compose=compose)
                result = result.then(core, on_compose=compose)
                for digit in (*tail, *center, *reversed(tail)):
                    result = result.then(atom(digit), on_compose=compose)
                result = result.then(core, on_compose=compose)
                for digit in reversed(head):
                    result = result.then(atom(digit), on_compose=compose)
                physical_width = source.pair_width + (2 if generation == 3 else 5)
                if result.length != physical_width:
                    raise AssertionError("Q19 U/V projection changed physical width")
                owner.ledger.bump(keys.REVERSE_Q19_UV_GRAM_HITS)
                owner.ledger.bump(keys.REVERSE_Q19_UV_GRAM_SKIPPED_TICKS, generation)
                yield result
            finally:
                values.clear()
