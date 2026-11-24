"""Compile finite repeated H-cell blocks with their exact boundary seams."""

from __future__ import annotations

from collections.abc import Callable
from math import gcd
from typing import Protocol

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp_interval import fold_slp_interval


class ScratchReservation(Protocol):
    def acquire(self, entries: int = 1, nodes: int = 1) -> None: ...

    def try_acquire(self, entries: int, nodes: int) -> bool: ...

    def release(self, entries: int = 1, nodes: int = 1) -> None: ...


def advance_periodic_blocks_slp(
    arena: LedgerSLPArena,
    root: int,
    span: int,
    *,
    scratch: ScratchReservation,
    pair: Callable[[int, int], int],
    tile_from_slp: Callable[[LedgerSLPArena, int], int],
    publish: Callable[[LedgerSLPArena, int], int],
    middle: Callable[[int], int],
) -> int | None:
    """Power an exact repeated middle with phase-rotated inlet actions.

    Source grammar authority comes from an existing REPEAT node, never
    from inspecting a physical orbit or detecting a guessed period. Let
    the repeated motif have k cells. Dyadic block starts rotate by span
    modulo k, so their minimal *guaranteed* period is k/gcd(k,span).
    The one-sided cell action only reads neighboring blocks. This yields
    a finite cyclic ring of inlet effects plus bounded nonperiodic seams.
    The ring is composed with SLP REPEAT, not with occurrence iteration.

    This also handles the fringe/period/fringe grammar produced by an
    earlier jump. Uncertified or overly costly source shapes use the
    general exact overlapping-block compiler unchanged.
    """
    cells = arena.nodes[root].length
    blocks = (cells + span - 1) // span
    # A short word is cheaper through the original exact tile kernel.
    # Do not pay for source quotient discovery when it cannot amortize.
    if blocks <= 32:
        return None
    # Find a complete REPEAT subtree and its exact offset without ever
    # descending into the subtree's physical occurrences. Bound this
    # search by DAG structure, not by the requested temporal horizon.
    pending: list[tuple[int, int]] = []
    if not scratch.try_acquire(1, 1):
        return None
    pending.append((root, 0))
    pending_charge = 1
    examined = 0
    selected: tuple[int, int, int] | None = None
    try:
        while pending:
            node_id, offset = pending.pop()
            pending_charge -= 1
            scratch.release()
            examined += 1
            if examined > 128:
                return None
            node = arena.nodes[node_id]
            if node.kind == "REPEAT":
                if selected is None or node.length > selected[2]:
                    selected = (offset, node.child, node.length)
            elif node.kind == "CONCAT":
                if not scratch.try_acquire(2, 2):
                    return None
                pending_charge += 2
                pending.append((node.right, offset + arena.nodes[node.left].length))
                pending.append((node.left, offset))
            elif node.kind not in ("EMPTY", "TERM"):
                raise ValueError("invalid SLP node kind")
    finally:
        pending.clear()
        if pending_charge:
            scratch.release(pending_charge, pending_charge)
    if selected is None:
        return None
    offset, motif, run_length = selected
    motif_length = arena.nodes[motif].length
    if not motif_length:
        return None
    # Blocks [first,last) lie entirely inside the certified repeated
    # interval. Partial blocks at its ends belong to the finite fringes.
    first = (offset + span - 1) // span
    last = (offset + run_length) // span
    period = motif_length // gcd(motif_length, span)
    run_blocks = last - first
    prefix_blocks = first
    suffix_blocks = blocks - last
    if period > 32 or run_blocks < 2 * period or prefix_blocks > 8 or suffix_blocks > 8:
        return None

    charge = 4 * (period + prefix_blocks + suffix_blocks) + 16
    if not scratch.try_acquire(charge, charge):
        return None
    try:
        zero = 0
        for _ in range(span.bit_length() - 1):
            zero = pair(zero, zero)

        def interval(node: int, begin: int, end: int) -> int:
            # A CONCAT contributes at most two tasks and a REPEAT at most
            # three. Each descent advances through an acyclic source node.
            frames = 3 * len(arena.nodes)
            scratch.acquire(frames, frames)
            try:
                return fold_slp_interval(
                    arena,
                    node,
                    begin,
                    end,
                    identity=arena.empty_id,
                    length=lambda item: arena.nodes[item].length,
                    full_value=lambda item, _reverse: item,
                    compose=arena.concat,
                    repeat=arena.repeat,
                )
            finally:
                scratch.release(frames, frames)

        def block(index: int) -> int:
            begin = index * span
            section = interval(root, begin, min(cells, begin + span))
            short = span - arena.nodes[section].length
            if short:
                section = arena.concat(section, arena.repeat(arena.terminal(0), short))
            return tile_from_slp(arena, section)

        def edge(previous: int, current: int) -> int:
            return publish(arena, middle(pair(previous, current)))

        outputs: list[int] = []
        previous = zero
        for index in range(first):
            current = block(index)
            outputs.append(edge(previous, current))
            previous = current

        # One canonical representative of every rotated block phase.
        # Exact REPEAT semantics guarantee these representatives recur
        # at all internal positions in [first,last), not merely at samples.
        phases = [block(first + i) for i in range(period)]
        outputs.append(edge(previous, phases[0]))
        ring = [edge(phases[i], phases[(i + 1) % period]) for i in range(period)]
        internal = run_blocks - 1
        turns, tail = divmod(internal, period)
        if turns:
            outputs.append(arena.repeat(arena.concat_many(ring), turns))
        if tail:
            outputs.append(arena.concat_many(ring[:tail]))

        previous = phases[(run_blocks - 1) % period]
        for index in range(last, blocks):
            current = block(index)
            outputs.append(edge(previous, current))
            previous = current
        outputs.append(edge(previous, zero))
        result = arena.concat_many(outputs)
        # The final physical block may have been padded. The true H row
        # contains exactly one extra span, regardless of that padding.
        if cells % span:
            result = interval(result, 0, cells + span)
        return result
    finally:
        scratch.release(charge, charge)
