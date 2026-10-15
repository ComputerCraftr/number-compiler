"""Read-only validation of canonical bounded reverse-output summaries."""

from __future__ import annotations

from dataclasses import fields

from number_compiler.arithmetic.carry.reverse_port_functions import (
    ReverseLeftTransfer,
    ReverseRightTransfer,
)
from number_compiler.hashlife.behavior.reverse_bound_output import ReverseBoundOutput
from number_compiler.hashlife.tiles.tile_result_records import ReverseBoundOutputKey
from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
from number_compiler.resources.tile_alphabet_contract import (
    CANONICAL_TILE_ALPHABET_VERSION,
)


def reverse_bound_output_scalar_slots(result: ReverseBoundOutput) -> int:
    """Derive the retained scalar slots from the two closed record layouts."""
    if type(result) is not ReverseBoundOutput:
        raise TypeError("reverse output slot audit requires its exact record")
    if (
        type(result.left) is not ReverseLeftTransfer
        or type(result.right) is not ReverseRightTransfer
    ):
        return -1
    return len(fields(ReverseLeftTransfer)) + len(fields(ReverseRightTransfer))


def valid_reverse_bound_output(
    arena: CompletedResultArena,
    key: ReverseBoundOutputKey,
    result: object,
) -> bool:
    """Recompute bounded child composition without mutating runtime counters."""
    if type(result) is not ReverseBoundOutput:
        return False
    try:
        key.__post_init__()
        node = arena.tiles.resolve(key.input)
        alphabet = arena.tiles.alphabet(node.alphabet)
        result.__post_init__()
        valid = (
            alphabet.blank == 2 * alphabet.radix - 1
            and alphabet.symbol_count == 2 * alphabet.radix
            and alphabet.interpretation == "unsigned-radix-cell-with-explicit-blank"
            and alphabet.version == CANONICAL_TILE_ALPHABET_VERSION
            and result.left.base == alphabet.radix
            and reverse_bound_output_scalar_slots(result) == 9
        )
        if not node.level:
            return (
                valid
                and node.symbol is not None
                and result == ReverseBoundOutput.leaf(alphabet.radix, node.symbol)
            )
        if node.left is None or node.right is None:
            return False
        left = arena._memo.get(ReverseBoundOutputKey(node.left))
        right = arena._memo.get(ReverseBoundOutputKey(node.right))
        if (
            type(left) is not ReverseBoundOutput
            or type(right) is not ReverseBoundOutput
        ):
            return False
        return valid and (
            result.left == left.left.then(right.left)
            and result.right == right.right.then(left.right)
        )
    except (TypeError, ValueError, KeyError, AttributeError, IndexError):
        return False


__all__ = ["reverse_bound_output_scalar_slots", "valid_reverse_bound_output"]
