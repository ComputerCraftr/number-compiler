"""Build exact Q19 word summaries over a ledger-owned SLP arena."""

from __future__ import annotations

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys
from number_compiler.sequences.reverse_add.q19_word_summary import (
    Q19Summary,
    WordSummary,
)


def build_word_summary(
    arena: LedgerSLPArena,
    summaries: OwnedMemo[int, WordSummary],
    ledger: ResourceLedger,
    root: int,
) -> WordSummary:
    """Summarize an SLP root with one iterative postorder traversal."""
    found = summaries.get(root)
    if found is not None:
        ledger.bump(_reverse_add_keys.REVERSE_PAIR_Q19_SUMMARY_CACHE_HITS)
        return found
    ledger.bump(_reverse_add_keys.REVERSE_PAIR_Q19_SUMMARY_CACHE_MISSES)
    stack: list[tuple[int, bool]] = [(root, False)]
    identity = Q19Summary.identity()
    while stack:
        node_id, expanded = stack.pop()
        if summaries.get(node_id) is not None:
            continue
        node = arena.nodes[node_id]
        if node.kind == "EMPTY":
            value = WordSummary(
                0, identity, identity, identity, identity, None, None, 0
            )
        elif node.kind == "TERM":
            if 0 <= node.symbol <= 18:
                atom = Q19Summary.atom(node.symbol)
                value = WordSummary(
                    1, atom, atom, identity, identity, node.symbol, node.symbol, 1
                )
            else:
                value = WordSummary(
                    0, identity, identity, identity, identity, None, None, 0
                )
        elif node.kind == "CONCAT":
            if not expanded:
                stack.append((node_id, True))
                stack.append((node.right, False))
                stack.append((node.left, False))
                continue
            left = summaries[node.left]
            right = summaries[node.right]
            if right.symbols:
                prefix_forward = left.forward.then(right.prefix_forward)
                prefix_reverse = right.prefix_reverse.then(left.reverse)
            else:
                prefix_forward, prefix_reverse = (
                    left.prefix_forward,
                    left.prefix_reverse,
                )
            value = WordSummary(
                left.symbols + right.symbols,
                left.forward.then(right.forward),
                right.reverse.then(left.reverse),
                prefix_forward,
                prefix_reverse,
                left.first_symbol if left.symbols else right.first_symbol,
                right.last_symbol if right.symbols else left.last_symbol,
                left.runs
                + right.runs
                - int(
                    left.last_symbol is not None
                    and left.last_symbol == right.first_symbol
                ),
            )
        elif node.kind == "REPEAT":
            if not expanded:
                stack.append((node_id, True))
                stack.append((node.child, False))
                continue
            child = summaries[node.child]
            if not child.symbols:
                value = WordSummary(
                    0, identity, identity, identity, identity, None, None, 0
                )
            else:
                whole_forward = child.forward.repeat(node.count)
                whole_reverse = child.reverse.repeat(node.count)
                if node.count == 1:
                    prefix_forward = child.prefix_forward
                    prefix_reverse = child.prefix_reverse
                else:
                    prefix_forward = child.forward.repeat(node.count - 1).then(
                        child.prefix_forward
                    )
                    prefix_reverse = child.prefix_reverse.then(
                        child.reverse.repeat(node.count - 1)
                    )
                value = WordSummary(
                    child.symbols * node.count,
                    whole_forward,
                    whole_reverse,
                    prefix_forward,
                    prefix_reverse,
                    child.first_symbol,
                    child.last_symbol,
                    child.runs * node.count
                    - (
                        node.count - 1 if child.first_symbol == child.last_symbol else 0
                    ),
                )
        else:  # pragma: no cover - guarded by SLPArena
            raise AssertionError(node.kind)
        summaries[node_id] = value
    result = summaries.get(root)
    if result is None:
        raise AssertionError("Q19 summary construction lost its root")
    return result


__all__ = ["build_word_summary"]
