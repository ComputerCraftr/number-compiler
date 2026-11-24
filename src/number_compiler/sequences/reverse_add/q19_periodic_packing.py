"""Exact base-64 algebra for repeating Q19 pair-field SLPs.

A repeated spatial pair field is represented as a semantic SLP REPEAT.  Both
publication and recovery use geometric-series algebra; neither enumerates
copies.  This is *spatial* factoring, not a claim that physical Q19 time is
periodic or that remaining successor steps have been powered.
"""

from __future__ import annotations

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp_interval import fold_slp_dag
from number_compiler.arithmetic.automata.slp_walks import symbol_at
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.owned_memo import LedgerReservation

from .q19_broadword_publisher import PackedQ19


def packed_repeated_motif(pairs: int, count: int) -> tuple[int, int] | None:
    """Find a short ordered period by an exact base-64 integer identity.

    A whole-lane shift-and-mask equality certifies every period position
    at once; no occurrence is sampled or visited.  Short/dense words
    return None to preserve the faster original word publisher.
    """
    if count < 128:
        return None
    for period in range(1, 9):
        turns = count // period
        if turns < 16:
            continue
        width_bits = 6 * period
        rest_bits = 6 * (count - period)
        if pairs >> width_bits == pairs & ((1 << rest_bits) - 1):
            return pairs & ((1 << width_bits) - 1), period
    return None


def publish_packed_word(arena: LedgerSLPArena, frame: PackedQ19) -> int | None:
    """Publish a certified repeated pair-field skeleton or decline cheaply."""
    motif = packed_repeated_motif(frame.pairs, frame.count)
    if motif is None:
        return None
    value, period = motif
    count = frame.count
    body = arena.word(tuple((value >> (6 * i)) & 63 for i in range(period)))
    turns, tail = divmod(count, period)
    chunks = [arena.terminal(19 + int(frame.center is not None))]
    if turns:
        chunks.append(arena.repeat(body, turns))
    if tail:
        chunks.append(arena.word(tuple((value >> (6 * i)) & 63 for i in range(tail))))
    if frame.center is not None:
        chunks.append(arena.terminal(2 * frame.center))
    chunks.append(arena.terminal(21))
    return arena.concat_many(chunks)


def has_nearby_repeat(arena: LedgerSLPArena, root: int) -> bool:
    """Recognize a compiled repeated field without a source-symbol walk."""
    pending = [root]
    for _ in range(16):
        if not pending:
            break
        node = arena.nodes[pending.pop()]
        if node.kind == "REPEAT":
            return True
        if node.kind == "CONCAT":
            pending.append(node.right)
            pending.append(node.left)
    return False


def recover_repeated_word(
    arena: LedgerSLPArena,
    root: int,
    pair_width: int,
    ledger: ResourceLedger,
    scratch_owner: int,
) -> PackedQ19:
    """Recover a packed frame using an exact SLP base-64 concatenation action.

    CONCAT(a,b) = a + 64**len(a)*b; REPEAT is its geometric power.
    The marker symbols are distinguished from pair coefficients and
    are checked at the exact published word boundaries.
    """
    count = pair_width // 2
    odd = pair_width & 1
    if (
        symbol_at(arena, root, 0) != 19 + odd
        or symbol_at(arena, root, arena.nodes[root].length - 1) != 21
        or arena.nodes[root].length != count + 2 + odd
    ):
        raise ValueError("issued Q19 frontier has an invalid marker or extent")
    neutral = (0, 0, 1)

    def terminal(symbol: int) -> tuple[int, int, int]:
        if 0 <= symbol <= 18:
            return symbol, 1, 64
        if symbol in (19, 20, 21):
            return neutral
        raise ValueError("invalid Q19 grammar terminal")

    def concat(
        a: tuple[int, int, int], b: tuple[int, int, int]
    ) -> tuple[int, int, int]:
        return a[0] + a[2] * b[0], a[1] + b[1], a[2] * b[2]

    def repeat(a: tuple[int, int, int], copies: int) -> tuple[int, int, int]:
        if not a[1] or not copies:
            return neutral
        power = pow(a[2], copies)
        return a[0] * ((power - 1) // (a[2] - 1)), a[1] * copies, power

    with LedgerReservation(ledger, scratch_owner) as scratch:
        values = fold_slp_dag(
            arena,
            root,
            empty_value=neutral,
            terminal_value=terminal,
            concatenate=concat,
            repeat=repeat,
            on_schedule=lambda count: scratch.reserve(entries=count, nodes=count),
            on_unschedule=lambda count: scratch.release(entries=count, nodes=count),
            on_evaluate=lambda node_id: scratch.reserve(
                entries=1,
                nodes=1 + 3 * ((6 * arena.nodes[node_id].length + 63) // 64),
            ),
        )
        packed, actual_count, _power = values[root]
        values.clear()
    if actual_count != count + odd:
        raise ValueError("issued Q19 frontier has a non-coefficient terminal")
    if odd:
        middle = packed >> (6 * count)
        if middle & 1 or middle > 18:
            raise ValueError("issued Q19 frontier has an invalid center")
        center: int | None = middle // 2
    else:
        center = None
    mask = (1 << (6 * count)) - 1
    return PackedQ19.from_record((packed & mask, count, center))
