"""Demanded ordered carry correlations over an issued Q19 source grammar."""

from __future__ import annotations

from collections.abc import Generator
from contextlib import contextmanager
from typing import TYPE_CHECKING

from number_compiler.arithmetic.automata.slp_interval import fold_slp_dag
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys
from number_compiler.resources.owned_memo import LedgerReservation

from .q19_ordered_gram import Q19OrderedGramAction
from .q19_word_summary import FoldedPairAction

if TYPE_CHECKING:
    from .q19_occurrence import ReversePairOutputOccurrence
    from .q19_output import ReversePairQ19OutputOwner


@contextmanager
def source_carry_gram(
    owner: ReversePairQ19OutputOwner,
    source: ReversePairOutputOccurrence,
) -> Generator[Q19OrderedGramAction, None, None]:
    """Fold an issued field under a reservation through its projection."""
    owner.validate_issued_occurrence(source)
    if owner.base != 10:
        raise ValueError("Q19 decimal carry projection requires base 10")
    z, modulus, degree = 1, 1_000_000_007, 3

    def terminal(symbol: int) -> FoldedPairAction[Q19OrderedGramAction]:
        if type(symbol) is not int or not 0 <= symbol <= 21:
            raise ValueError("invalid Q19 source symbol")
        if symbol in (19, 20, 21):
            return identity
        slot = 0 if symbol < 9 else 1 if symbol == 9 else 2
        atom = atoms[slot]
        if atom is None:
            atom = Q19OrderedGramAction.atom((0, 9, 10)[slot], z, modulus, degree)
            atoms[slot] = atom
            owner.ledger.bump(_reverse_add_keys.REVERSE_Q19_GRAM_ATOM_BUILDS)
        return FoldedPairAction(atom, atom, zero)

    def compose() -> None:
        owner.ledger.bump(_reverse_add_keys.REVERSE_Q19_GRAM_COMPOSITIONS)

    def concatenate(
        left: FoldedPairAction[Q19OrderedGramAction],
        right: FoldedPairAction[Q19OrderedGramAction],
    ) -> FoldedPairAction[Q19OrderedGramAction]:
        prefix_reverse = (
            right.prefix_reverse.then(left.reverse, on_compose=compose)
            if right.forward.length
            else left.prefix_reverse
        )
        return FoldedPairAction(
            left.forward.then(right.forward, on_compose=compose),
            right.reverse.then(left.reverse, on_compose=compose),
            prefix_reverse,
        )

    def repeat(
        value: FoldedPairAction[Q19OrderedGramAction], count: int
    ) -> FoldedPairAction[Q19OrderedGramAction]:
        if count == 0 or value.forward.length == 0:
            return identity
        forward = value.forward.repeat(count, on_compose=compose)
        reverse = (
            forward
            if value.forward is value.reverse
            else value.reverse.repeat(count, on_compose=compose)
        )
        prefix = (
            value.prefix_reverse
            if count == 1
            else value.prefix_reverse.then(
                value.reverse.repeat(count - 1, on_compose=compose), on_compose=compose
            )
        )
        return FoldedPairAction(forward, reverse, prefix)

    # Degree 3 and the 30-bit modulus bound each action to four rows of five
    # three-coefficient jets, four boundary signs and two outgoing carries.
    # A half summary has three actions, with temporary joins and packet
    # projection covered by the separate fixed working-set reservation.
    root_bits = owner.arena.nodes[source.root].length.bit_length()
    length_limbs = max(1, (root_bits + 63) // 64)
    nodes_per_action = 4 * (5 * degree + 6) + 2 * degree + 8 + 3 * length_limbs
    nodes_per_half = 3 * nodes_per_action
    with LedgerReservation(owner.ledger, owner.scratch_owner) as reservation:
        reservation.reserve(nodes=12 * nodes_per_action)
        zero = Q19OrderedGramAction.identity(z, modulus, degree)
        identity = FoldedPairAction(zero, zero, zero)
        atoms: list[Q19OrderedGramAction | None] = [None, None, None]

        def schedule(count: int) -> None:
            reservation.reserve(entries=count, nodes=2 * count)

        def unschedule(count: int) -> None:
            reservation.release(entries=count, nodes=2 * count)

        def reference_entry(_node: int) -> None:
            reservation.reserve(entries=1, nodes=2)

        def reference_release(_node: int) -> None:
            reservation.release(entries=1, nodes=2)

        def evaluate(_node: int) -> None:
            reservation.reserve(entries=1, nodes=nodes_per_half)
            owner.ledger.bump(_reverse_add_keys.REVERSE_Q19_GRAM_NODE_VISITS)

        def release_value(_node: int) -> None:
            reservation.release(entries=1, nodes=nodes_per_half)

        summaries = fold_slp_dag(
            owner.arena,
            source.root,
            empty_value=identity,
            terminal_value=terminal,
            concatenate=concatenate,
            repeat=repeat,
            on_schedule=schedule,
            on_evaluate=evaluate,
            on_unschedule=unschedule,
            reclaim_values=True,
            on_reference_entry=reference_entry,
            on_reference_release=reference_release,
            on_value_release=release_value,
        )
        try:
            result = summaries[source.root].physical(
                owner.root_width_parity(source.root), compose
            )
            if result.length != source.pair_width:
                raise AssertionError("ordered carry Gram lost the physical pair field")
            owner.validate_issued_occurrence(source)
            yield result
        finally:
            summaries.clear()
