"""Independent checks for cached and occurrence-level Q19 summaries."""

from __future__ import annotations

from typing import TypeVar

from number_compiler.resources.owned_memo import OwnedMemoAuditSnapshot

_Key = TypeVar("_Key")
_Value = TypeVar("_Value")


def _memo_value(snapshot: OwnedMemoAuditSnapshot[_Key, _Value], key: _Key) -> object:
    if key not in snapshot.container:
        raise KeyError(key)
    try:
        return snapshot.payload_view[key]
    except TypeError:
        return snapshot.container[key]


def summary_matches(root: object, index: int) -> bool:
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairQ19OutputOwner,
    )
    from number_compiler.sequences.reverse_add.q19_word_summary import (
        Q19Summary,
        WordSummary,
    )

    if type(root) is not ReversePairQ19OutputOwner:
        return False
    state = root.audit_snapshot()
    if not 0 <= index < len(state.arena.nodes):
        return False
    node = state.arena.nodes[index]
    value = _memo_value(state.summaries, index)
    if type(value) is not WordSummary:
        return False
    identity = Q19Summary.identity()
    if node.kind == "EMPTY" or node.kind == "TERM" and node.symbol > 18:
        expected = WordSummary(0, identity, identity, identity, identity, None, None, 0)
    elif node.kind == "TERM":
        atom = Q19Summary.atom(node.symbol)
        expected = WordSummary(
            1, atom, atom, identity, identity, node.symbol, node.symbol, 1
        )
    elif node.kind == "CONCAT":
        left = _memo_value(state.summaries, node.left)
        right = _memo_value(state.summaries, node.right)
        if type(left) is not WordSummary or type(right) is not WordSummary:
            return False
        prefix = (left.prefix_forward, left.prefix_reverse)
        if right.symbols:
            prefix = (
                left.forward.then(right.prefix_forward),
                right.prefix_reverse.then(left.reverse),
            )
        expected = WordSummary(
            left.symbols + right.symbols,
            left.forward.then(right.forward),
            right.reverse.then(left.reverse),
            *prefix,
            left.first_symbol if left.symbols else right.first_symbol,
            right.last_symbol if right.symbols else left.last_symbol,
            left.runs
            + right.runs
            - int(
                left.last_symbol is not None and left.last_symbol == right.first_symbol
            ),
        )
    elif node.kind == "REPEAT":
        child = _memo_value(state.summaries, node.child)
        if type(child) is not WordSummary:
            return False
        if child.symbols == 0:
            expected = WordSummary(
                0, identity, identity, identity, identity, None, None, 0
            )
        else:
            expected = WordSummary(
                child.symbols * node.count,
                child.forward.repeat(node.count),
                child.reverse.repeat(node.count),
                child.forward.repeat(node.count - 1).then(child.prefix_forward),
                child.prefix_reverse.then(child.reverse.repeat(node.count - 1)),
                child.first_symbol,
                child.last_symbol,
                child.runs * node.count
                - (node.count - 1 if child.first_symbol == child.last_symbol else 0),
            )
    else:
        return False
    return value == expected


def occurrence_summary(root: object, grammar_root: int) -> tuple[int, int, int]:
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairQ19OutputOwner,
    )
    from number_compiler.sequences.reverse_add.q19_word_summary import WordSummary

    if type(root) is not ReversePairQ19OutputOwner:
        raise TypeError("expected the exact reverse pair output owner")
    state = root.audit_snapshot()
    summary_value = _memo_value(state.summaries, grammar_root)
    if type(summary_value) is not WordSummary:
        raise ValueError("issued pair grammar has no typed summary")
    summary = summary_value
    node = state.arena.nodes[grammar_root]
    while node.kind in ("CONCAT", "REPEAT"):
        node = state.arena.nodes[node.left if node.kind == "CONCAT" else node.child]
    parity = node.symbol - 19
    if node.kind != "TERM" or parity not in (0, 1):
        raise ValueError("issued pair grammar lacks its parity header")
    tail = summary.prefix_reverse if parity else summary.reverse
    full = summary.forward.then(tail)
    if full.length != 2 * summary.symbols - parity:
        raise ValueError("issued pair grammar has inconsistent symmetry")
    return full.length, full.domain, full.f9


__all__ = ["occurrence_summary", "summary_matches"]
