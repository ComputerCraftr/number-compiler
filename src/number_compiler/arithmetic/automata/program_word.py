"""Canonical RLE rope used by powered continuation programs.

Words are canonical modulo concatenation associativity and adjacent equal-run
fusion.  This is compiler/runtime metadata: a represented run never allocates
one node per symbol.
"""

from __future__ import annotations

import weakref
from collections.abc import Callable, Generator, Iterable, Iterator, MutableSequence
from dataclasses import dataclass
from itertools import count
from typing import Any, TypeVar

from number_compiler.arithmetic.fields.radix import bit_width

_CacheKey = TypeVar("_CacheKey")


_IDS = count(1)


@dataclass(frozen=True, slots=True, weakref_slot=True)
class CanonicalWord:
    node_id: int
    length: int
    run_count: int
    symbol: int | None = None
    run_length: int = 0
    left: CanonicalWord | None = None
    right: CanonicalWord | None = None

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (
                self.node_id,
                self.length,
                self.run_count,
                self.run_length,
            )
        ):
            raise TypeError(
                "canonical word identities and extents require exact integers"
            )
        if self.node_id <= 0 or min(self.length, self.run_count, self.run_length) < 0:
            raise ValueError("invalid canonical word identity or extent")
        if self.run_count == 0:
            valid = (
                self.length == self.run_length == 0
                and self.symbol is None
                and self.left is None
                and self.right is None
            )
        elif self.run_count == 1:
            valid = (
                type(self.symbol) is int
                and self.length == self.run_length > 0
                and self.left is None
                and self.right is None
            )
        else:
            valid = (
                self.symbol is None
                and self.run_length == 0
                and type(self.left) is CanonicalWord
                and type(self.right) is CanonicalWord
                and self.length == self.left.length + self.right.length
                and self.run_count == self.left.run_count + self.right.run_count
            )
        if not valid:
            raise ValueError("malformed canonical word node")


@dataclass(slots=True)
class RunTraversalMetrics:
    """Ephemeral work retained by one run-order traversal."""

    visited_nodes: int = 0
    peak_frontier: int = 0
    visited_block_bits: int = 0
    peak_frontier_bits: int = 0


EMPTY = CanonicalWord(next(_IDS), 0, 0)
_WORDS: weakref.WeakValueDictionary[int, CanonicalWord] = weakref.WeakValueDictionary()
_WORD_DEFINITIONS: dict[
    int, tuple[int, int, int, int | None, int, int | None, int | None]
] = {}
_WORD_WATCHES: dict[int, weakref.ReferenceType[CanonicalWord]] = {}


def _definition(
    word: CanonicalWord,
) -> tuple[int, int, int, int | None, int, int | None, int | None]:
    return (
        word.node_id,
        word.length,
        word.run_count,
        word.symbol,
        word.run_length,
        None if word.left is None else word.left.node_id,
        None if word.right is None else word.right.node_id,
    )


def _publish_word(word: CanonicalWord) -> None:
    local_id = word.node_id
    _WORDS[local_id] = word
    _WORD_DEFINITIONS[local_id] = _definition(word)

    def expired(_reference: weakref.ReferenceType[CanonicalWord]) -> None:
        _WORD_DEFINITIONS.pop(local_id, None)
        _WORD_WATCHES.pop(local_id, None)

    _WORD_WATCHES[local_id] = weakref.ref(word, expired)


_publish_word(EMPTY)
_RUNS: weakref.WeakValueDictionary[tuple[int, int], CanonicalWord] = (
    weakref.WeakValueDictionary()
)
_LEAVES: weakref.WeakValueDictionary[int, CanonicalWord] = weakref.WeakValueDictionary()
_CONCATS: weakref.WeakValueDictionary[tuple[int, int], CanonicalWord] = (
    weakref.WeakValueDictionary()
)
_SLICE: weakref.WeakValueDictionary[tuple[int, int, int], CanonicalWord] = (
    weakref.WeakValueDictionary()
)
_JOIN: weakref.WeakValueDictionary[tuple[int, int], CanonicalWord] = (
    weakref.WeakValueDictionary()
)


def _get(
    cache: weakref.WeakValueDictionary[_CacheKey, CanonicalWord], key: _CacheKey
) -> CanonicalWord | None:
    return cache.get(key)


def _put(
    cache: weakref.WeakValueDictionary[_CacheKey, CanonicalWord],
    key: _CacheKey,
    value: CanonicalWord,
) -> None:
    cache[key] = value


def _split(n: int) -> int:
    if n <= 1:
        raise ValueError(n)
    return 1 << ((n - 1).bit_length() - 1)


def _validate_word(word: CanonicalWord) -> None:
    if type(word) is not CanonicalWord:
        raise TypeError("expected an exact canonical word")
    word.__post_init__()
    if _WORDS.get(word.node_id) is not word or _WORD_DEFINITIONS.get(
        word.node_id
    ) != _definition(word):
        raise ValueError("canonical word identity is foreign or stale")


def run(symbol: int, count_value: int) -> CanonicalWord:
    if type(symbol) is not int or type(count_value) is not int:
        raise TypeError("word symbols and run lengths require exact integers")
    if count_value == 0:
        return EMPTY
    if count_value < 0:
        raise ValueError(count_value)
    key = (symbol, count_value)
    v = _RUNS.get(key)
    if v is not None:
        return v
    v = CanonicalWord(next(_IDS), count_value, 1, symbol=symbol, run_length=count_value)
    _publish_word(v)
    _RUNS[key] = v
    if count_value == 1:
        _LEAVES[symbol] = v
    return v


def leaf(symbol: int) -> CanonicalWord:
    if type(symbol) is not int:
        raise TypeError("word symbols require exact integers")
    return _LEAVES.get(symbol) or run(symbol, 1)


def first_run(w: CanonicalWord) -> CanonicalWord:
    if not w.run_count:
        raise ValueError("empty")
    while w.left is not None:
        w = w.left
    return w


def last_run(w: CanonicalWord) -> CanonicalWord:
    if not w.run_count:
        raise ValueError("empty")
    while w.right is not None:
        w = w.right
    return w


def _raw_node(left: CanonicalWord, right: CanonicalWord) -> CanonicalWord:
    """Intern one already-balanced, non-mergeable internal node."""
    _validate_word(left)
    _validate_word(right)
    if not left.run_count:
        return right
    if not right.run_count:
        return left
    if last_run(left).symbol == first_run(right).symbol:
        raise AssertionError("mergeable")
    total = left.run_count + right.run_count
    if left.run_count != _split(total):
        raise AssertionError((left.run_count, right.run_count, total))
    key = (left.node_id, right.node_id)
    v = _CONCATS.get(key)
    if v is not None:
        return v
    v = CanonicalWord(
        next(_IDS), left.length + right.length, total, left=left, right=right
    )
    _publish_word(v)
    _CONCATS[key] = v
    return v


def _word_tasks(initial: tuple[Any, ...]) -> CanonicalWord:
    """Execute slice/rebalance operations with one explicit continuation stack."""
    results: list[CanonicalWord] = []
    tasks: list[tuple[Any, ...]] = [initial]
    while tasks:
        frame = tasks.pop()
        tag = frame[0]
        if tag == "SLICE":
            node, offset, count_value = frame[1], int(frame[2]), int(frame[3])
            if offset < 0 or count_value < 0 or offset + count_value > node.run_count:
                raise ValueError((node.run_count, offset, count_value))
            key = (node.node_id, offset, count_value)
            cached = _get(_SLICE, key)
            if cached is not None:
                results.append(cached)
                continue
            if count_value == 0:
                out = EMPTY
            elif offset == 0 and count_value == node.run_count:
                out = node
            else:
                if node.left is None or node.right is None:
                    raise AssertionError((node, offset, count_value))
                lr = node.left.run_count
                if offset + count_value <= lr:
                    tasks.append(("STORE_SLICE", key))
                    tasks.append(("SLICE", node.left, offset, count_value))
                    continue
                if offset >= lr:
                    tasks.append(("STORE_SLICE", key))
                    tasks.append(("SLICE", node.right, offset - lr, count_value))
                    continue
                left_count = lr - offset
                right_count = count_value - left_count
                tasks.append(("SLICE_CROSS", key))
                tasks.append(("SLICE", node.right, 0, right_count))
                tasks.append(("SLICE", node.left, offset, left_count))
                continue
            _put(_SLICE, key, out)
            results.append(out)
            continue
        if tag == "STORE_SLICE":
            key = frame[1]
            out = results.pop()
            _put(_SLICE, key, out)
            results.append(out)
            continue
        if tag == "SLICE_CROSS":
            key = frame[1]
            right = results.pop()
            left = results.pop()
            tasks.append(("STORE_SLICE", key))
            tasks.append(("JOIN", left, right))
            continue
        if tag == "JOIN":
            left, right = frame[1], frame[2]
            if not left.run_count:
                results.append(right)
                continue
            if not right.run_count:
                results.append(left)
                continue
            if last_run(left).symbol == first_run(right).symbol:
                raise AssertionError("mergeable")
            total = left.run_count + right.run_count
            sp = _split(total)
            if left.run_count == sp:
                results.append(_raw_node(left, right))
                continue
            if left.run_count > sp:
                tasks.append(("JOIN_LEFT_SPLIT", right))
                tasks.append(("SLICE", left, sp, left.run_count - sp))
                tasks.append(("SLICE", left, 0, sp))
                continue
            need = sp - left.run_count
            tasks.append(("JOIN_RIGHT_SPLIT", left))
            tasks.append(("SLICE", right, need, right.run_count - need))
            tasks.append(("SLICE", right, 0, need))
            continue
        if tag == "JOIN_LEFT_SPLIT":
            right = frame[1]
            rem = results.pop()
            prefix = results.pop()
            tasks.append(("RAW_PREFIX", prefix))
            tasks.append(("JOIN", rem, right))
            continue
        if tag == "JOIN_RIGHT_SPLIT":
            left = frame[1]
            rem = results.pop()
            prefix = results.pop()
            tasks.append(("RAW_SUFFIX", rem))
            tasks.append(("JOIN", left, prefix))
            continue
        if tag == "RAW_PREFIX":
            prefix = frame[1]
            tail = results.pop()
            results.append(_raw_node(prefix, tail))
            continue
        if tag == "RAW_SUFFIX":
            suffix = frame[1]
            head = results.pop()
            results.append(_raw_node(head, suffix))
            continue
        raise AssertionError(tag)
    if len(results) != 1:
        raise AssertionError(len(results))
    return results[0]


def slice_runs(w: CanonicalWord, start: int, length: int) -> CanonicalWord:
    _validate_word(w)
    if type(start) is not int or type(length) is not int:
        raise TypeError("word slices require exact integer coordinates")
    return _word_tasks(("SLICE", w, start, length))


def concat_disjoint(left: CanonicalWord, right: CanonicalWord) -> CanonicalWord:
    _validate_word(left)
    _validate_word(right)
    return _word_tasks(("JOIN", left, right))


def concat(left: CanonicalWord, right: CanonicalWord) -> CanonicalWord:
    _validate_word(left)
    _validate_word(right)
    if not left.run_count:
        return right
    if not right.run_count:
        return left
    key = (left.node_id, right.node_id)
    got = _get(_JOIN, key)
    if got is not None:
        return got
    a = last_run(left)
    b = first_run(right)
    if a.symbol == b.symbol:
        lp = slice_runs(left, 0, left.run_count - 1)
        rs = slice_runs(right, 1, right.run_count - 1)
        if a.symbol is None:
            raise AssertionError(a)
        merged = run(int(a.symbol), a.run_length + b.run_length)
        out = concat_disjoint(concat_disjoint(lp, merged), rs)
    else:
        out = concat_disjoint(left, right)
    _put(_JOIN, key, out)
    return out


def from_values(values: Iterable[int]) -> CanonicalWord:
    out = EMPTY
    for v in values:
        out = concat(out, leaf(v))
    return out


def from_runs(runs: Iterable[tuple[int, int]]) -> CanonicalWord:
    """Build a canonical word from ``(symbol, count)`` pairs without expansion."""
    out = EMPTY
    for symbol, count_value in runs:
        if type(symbol) is not int or type(count_value) is not int:
            raise TypeError("word runs require exact integer symbols and lengths")
        if count_value < 0:
            raise ValueError(count_value)
        if count_value:
            out = concat(out, run(symbol, count_value))
    return out


def iter_runs(root: CanonicalWord) -> Iterator[tuple[int, int]]:
    """Yield canonical runs left-to-right without expanding their lengths."""
    _validate_word(root)
    stack: list[CanonicalWord] = []
    node = root
    while stack or node.run_count:
        while node.run_count and node.left is not None:
            if node.right is None:
                raise AssertionError(node)
            stack.append(node.right)
            node = node.left
        if node.run_count:
            if node.symbol is None:
                raise AssertionError(node)
            yield int(node.symbol), int(node.run_length)
        if not stack:
            break
        node = stack.pop()


def iter_run_blocks_reverse(
    root: CanonicalWord,
    value: int,
    *,
    symbol_bits: int,
    metrics: RunTraversalMetrics | None = None,
    frontier_delta: Callable[[int, int], None] | None = None,
    frontier: MutableSequence[tuple[CanonicalWord, int, int]] | None = None,
) -> Generator[tuple[int, int, int], None, None]:
    """Yield right-to-left runs paired with their integer source blocks.

    The input integer is split at the existing balanced word boundaries. No
    digit vector or integer representing the canonical word is constructed.
    """
    _validate_word(root)
    if type(value) is not int or value < 0:
        raise ValueError("word block traversal requires a nonnegative integer")
    if type(symbol_bits) is not int or symbol_bits < 1:
        raise ValueError("word block traversal requires a positive symbol width")
    if value.bit_length() > root.length * symbol_bits:
        raise ValueError("integer does not fit the canonical word extent")
    stack: MutableSequence[tuple[CanonicalWord, int, int]]
    if frontier is None:
        stack = []
    else:
        if frontier:
            raise ValueError("word block traversal requires an empty frontier")
        stack = frontier
    frontier_bits = 0
    node, block = root, value
    try:
        while stack or node.run_count:
            if metrics is not None:
                metrics.visited_nodes += 1
                metrics.visited_block_bits += node.length * symbol_bits
            while node.run_count and node.right is not None:
                if node.left is None:
                    raise AssertionError(node)
                left_bits = node.left.length * symbol_bits
                right_block = block >> left_bits
                left_block = block - (right_block << left_bits)
                if frontier_delta is not None:
                    frontier_delta(1, left_bits)
                try:
                    stack.append((node.left, left_block, left_bits))
                except BaseException:
                    if frontier_delta is not None:
                        frontier_delta(-1, -left_bits)
                    raise
                frontier_bits += left_bits
                if metrics is not None:
                    metrics.peak_frontier = max(metrics.peak_frontier, len(stack))
                    metrics.peak_frontier_bits = max(
                        metrics.peak_frontier_bits, frontier_bits
                    )
                    metrics.visited_nodes += 1
                    metrics.visited_block_bits += node.right.length * symbol_bits
                node, block = node.right, right_block
            if node.run_count:
                if node.symbol is None:
                    raise AssertionError(node)
                yield int(node.symbol), int(node.run_length), block
            if not stack:
                break
            node, block, block_bits = stack.pop()
            frontier_bits -= block_bits
            if frontier_delta is not None:
                frontier_delta(-1, -block_bits)
    finally:
        while stack:
            _, _, block_bits = stack.pop()
            if frontier_delta is not None:
                frontier_delta(-1, -block_bits)


def word_metrics(root: CanonicalWord) -> dict[str, int]:
    """Charge the retained RLE/SLP word, including references and run parameters."""
    _validate_word(root)
    seen = {}
    stack = [root]
    while stack:
        node = stack.pop()
        if node.node_id in seen:
            continue
        seen[node.node_id] = node
        if node.left is not None:
            stack.append(node.left)
        if node.right is not None:
            stack.append(node.right)
    refs = sum(
        int(node.left is not None) + int(node.right is not None)
        for node in seen.values()
    )
    param_bits = 0
    for node in seen.values():
        if node.run_count == 1:
            param_bits += bit_width(int(node.symbol or 0)) + bit_width(node.run_length)
        else:
            param_bits += bit_width(node.length) + bit_width(node.run_count)
    id_bits = bit_width(len(seen))
    return {
        "length": root.length,
        "runs": root.run_count,
        "nodes": len(seen),
        "references": refs,
        "parameter_bits": param_bits,
        "description_bits": param_bits + len(seen) + refs * id_bits,
    }


_REVERSE: weakref.WeakValueDictionary[int, CanonicalWord] = (
    weakref.WeakValueDictionary()
)


def reverse(word: CanonicalWord) -> CanonicalWord:
    _validate_word(word)
    got = _REVERSE.get(word.node_id)
    if got is not None:
        return got
    built: dict[int, CanonicalWord] = {}
    stack: list[tuple[CanonicalWord, bool]] = [(word, False)]
    while stack:
        node, ready = stack.pop()
        cached = _REVERSE.get(node.node_id)
        if cached is not None:
            built[node.node_id] = cached
            continue
        if not node.run_count:
            out = EMPTY
        elif node.run_count == 1:
            out = node
        else:
            if node.left is None or node.right is None:
                raise AssertionError(node)
            if not ready:
                stack.append((node, True))
                if node.left.node_id not in built:
                    stack.append((node.left, False))
                if node.right.node_id not in built:
                    stack.append((node.right, False))
                continue
            out = concat(built[node.right.node_id], built[node.left.node_id])
        _REVERSE[node.node_id] = out
        built[node.node_id] = out
    return built[word.node_id]


_NORMALIZE_RUN_CAP: weakref.WeakValueDictionary[tuple[int, int, int], CanonicalWord] = (
    weakref.WeakValueDictionary()
)


def cap_symbol_runs(word: CanonicalWord, symbol: int, cap: int) -> CanonicalWord:
    """Canonical quotient under a proved synchronizing ``symbol**cap`` law."""
    _validate_word(word)
    if type(symbol) is not int or type(cap) is not int:
        raise TypeError("run normalization requires exact integer parameters")
    if cap <= 0 or not word.run_count:
        return word
    root_key = (word.node_id, symbol, cap)
    got = _get(_NORMALIZE_RUN_CAP, root_key)
    if got is not None:
        return got
    built: dict[int, CanonicalWord] = {}
    stack: list[tuple[CanonicalWord, bool]] = [(word, False)]
    while stack:
        node, ready = stack.pop()
        key = (node.node_id, symbol, cap)
        cached = _get(_NORMALIZE_RUN_CAP, key)
        if cached is not None:
            built[node.node_id] = cached
            continue
        if node.run_count == 1:
            out = (
                run(symbol, cap)
                if node.symbol == symbol and node.run_length > cap
                else node
            )
        else:
            if node.left is None or node.right is None:
                raise AssertionError(node)
            if not ready:
                stack.append((node, True))
                if node.right.node_id not in built:
                    stack.append((node.right, False))
                if node.left.node_id not in built:
                    stack.append((node.left, False))
                continue
            out = concat(built[node.left.node_id], built[node.right.node_id])
        _put(_NORMALIZE_RUN_CAP, key, out)
        built[node.node_id] = out
    return built[word.node_id]


def clear_transient_program_word_caches() -> None:
    """Drop weak memo tables without changing live canonical semantics.

    Every module-level interner is weak and therefore owns no semantic object.
    The explicit clear remains available for compatibility and deterministic
    research epochs.
    """
    global _NEXT_PRUNE_SIZE
    _NEXT_PRUNE_SIZE = 256
    _SLICE.clear()
    _JOIN.clear()
    _NORMALIZE_RUN_CAP.clear()


_NEXT_PRUNE_SIZE = 256


def prune_stale_program_word_memos(*, amortized: bool = False) -> int:
    """Retire operation keys whose operands have expired, preserving live hits.

    A weak result can remain live after an operand dies (for example a slice
    returning a shared literal). Weak values alone do not retire such keys.
    Automatic callers sweep only after the table population doubles. Rechecking
    the same live tables at every grammar advance was quadratic bookkeeping.
    Explicit callers retain immediate cleanup. Return the number of keys visited
    so cleanup work is visible independently of semantic construction.
    """
    global _NEXT_PRUNE_SIZE
    if type(amortized) is not bool:
        raise TypeError("memo cleanup policy must be a boolean")
    population = len(_SLICE) + len(_JOIN) + len(_NORMALIZE_RUN_CAP) + len(_REVERSE)
    if amortized and population < _NEXT_PRUNE_SIZE:
        return 0
    visited = 0
    for slice_key in tuple(_SLICE):
        visited += 1
        if slice_key[0] not in _WORDS:
            _SLICE.pop(slice_key, None)
    for join_key in tuple(_JOIN):
        visited += 1
        if join_key[0] not in _WORDS or join_key[1] not in _WORDS:
            _JOIN.pop(join_key, None)
    for cap_key in tuple(_NORMALIZE_RUN_CAP):
        visited += 1
        if cap_key[0] not in _WORDS:
            _NORMALIZE_RUN_CAP.pop(cap_key, None)
    for reverse_key in tuple(_REVERSE):
        visited += 1
        if reverse_key not in _WORDS:
            _REVERSE.pop(reverse_key, None)
    survivors = len(_SLICE) + len(_JOIN) + len(_NORMALIZE_RUN_CAP) + len(_REVERSE)
    _NEXT_PRUNE_SIZE = max(256, 2 * survivors)
    return visited


__all__ = [
    "EMPTY",
    "CanonicalWord",
    "RunTraversalMetrics",
    "cap_symbol_runs",
    "clear_transient_program_word_caches",
    "concat",
    "concat_disjoint",
    "first_run",
    "from_runs",
    "from_values",
    "iter_run_blocks_reverse",
    "iter_runs",
    "last_run",
    "leaf",
    "prune_stale_program_word_memos",
    "reverse",
    "run",
    "slice_runs",
    "word_metrics",
]
