"""Canonical two-phase ``-1/3`` source-prefix summaries in the result memo."""

from __future__ import annotations

from number_compiler.hashlife.tiles.result_reverse_indexes import publish_indexed_result
from number_compiler.hashlife.tiles.tile_result_records import (
    RootMatchResult,
    SourceRootMatchKey,
)
from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
from number_compiler.hashlife.tiles.tiles import TileID
from number_compiler.resources.metric_keys import (
    hashlife_tiles as _tiles_keys,
)
from number_compiler.resources.result_cache_kinds import (
    ResultCacheKind,
    record_unattributed_post_eviction_miss,
)
from number_compiler.resources.tile_alphabet_contract import (
    CANONICAL_TILE_ALPHABET_VERSION,
)


def _snapshot(key: SourceRootMatchKey, value: RootMatchResult) -> tuple[object, ...]:
    tile = key.input
    return (
        tile.owner,
        tile.kind,
        tile.local_id,
        value.level,
        value.phase0_first_mismatch,
        value.phase1_first_mismatch,
    )


def _validate_key(arena: CompletedResultArena, key: SourceRootMatchKey) -> None:
    if type(arena) is not CompletedResultArena:
        raise TypeError("source root matching requires the shared result arena")
    key.__post_init__()
    record = arena.tiles.resolve(key.input)
    alphabet = arena.tiles.alphabet(record.alphabet)
    if (
        alphabet.symbol_count,
        alphabet.blank,
        alphabet.radix,
        alphabet.cell_bits,
        alphabet.interpretation,
        alphabet.version,
    ) != (
        3,
        2,
        2,
        2,
        "unsigned-radix-cell-with-explicit-blank",
        CANONICAL_TILE_ALPHABET_VERSION,
    ):
        raise ValueError("source root matching requires a canonical binary tile")


def _validate_value(
    arena: CompletedResultArena,
    key: SourceRootMatchKey,
    value: RootMatchResult,
    *,
    published: bool,
) -> None:
    if type(value) is not RootMatchResult:
        raise TypeError("source root memo contains another result sort")
    value.__post_init__()
    if value.level != arena.tiles.resolve(key.input).level:
        raise ValueError("source root summary has another spatial level")
    if published and (
        value._publication_owner is not arena._interface_publication_seal
        or value._publication_snapshot != _snapshot(key, value)
    ):
        raise ValueError("source root summary publication metadata was modified")


def _sealed(
    arena: CompletedResultArena,
    key: SourceRootMatchKey,
    value: RootMatchResult,
) -> RootMatchResult:
    value.__post_init__()
    return RootMatchResult(
        value.level,
        value.phase0_first_mismatch,
        value.phase1_first_mismatch,
        arena._interface_publication_seal,
        _snapshot(key, value),
    )


def lookup_source_root_match(
    arena: CompletedResultArena, key: SourceRootMatchKey
) -> RootMatchResult | None:
    """Return one validated summary before any child inspection."""
    _validate_key(arena, key)
    arena.ledger.bump(_tiles_keys.COLLATZ_SOURCE_ROOT_MATCH_REQUESTS)
    found = arena._memo.get(key)
    if found is None:
        record_unattributed_post_eviction_miss(arena.ledger, ResultCacheKind.INTERFACE)
        return None
    if type(found) is not RootMatchResult:
        raise TypeError("source root memo contains another result sort")
    _validate_value(arena, key, found, published=True)
    arena.ledger.bump(_tiles_keys.COLLATZ_SOURCE_ROOT_MATCH_EARLY_HITS)
    return found


def _publish(
    arena: CompletedResultArena,
    key: SourceRootMatchKey,
    plain: RootMatchResult,
) -> RootMatchResult:
    _validate_key(arena, key)
    value = _sealed(arena, key, plain)
    _validate_value(arena, key, value, published=True)
    found = arena._memo.get(key)
    if found is not None:
        if type(found) is not RootMatchResult:
            raise TypeError("source root memo contains another result sort")
        _validate_value(arena, key, found, published=True)
        if found != value:
            raise ValueError("source tile already has another root summary")
        arena.ledger.bump(_tiles_keys.COLLATZ_SOURCE_ROOT_MATCH_LATE_DUPLICATES)
        return found
    publish_indexed_result(arena, key, value, referenced=(key.input,))
    arena.ledger.bump(_tiles_keys.COLLATZ_SOURCE_ROOT_MATCH_PUBLICATIONS)
    return value


def _parent(left: RootMatchResult, right: RootMatchResult) -> RootMatchResult:
    if left.level != right.level:
        raise ValueError("source root children have different levels")
    width = 1 << left.level

    def mismatch(phase: int) -> int | None:
        first = left.phase0_first_mismatch if phase == 0 else left.phase1_first_mismatch
        if first is not None:
            return first
        following_phase = phase ^ (width & 1)
        following = (
            right.phase0_first_mismatch
            if following_phase == 0
            else right.phase1_first_mismatch
        )
        return None if following is None else width + following

    return RootMatchResult(left.level + 1, mismatch(0), mismatch(1))


def source_root_match(arena: CompletedResultArena, tile: TileID) -> RootMatchResult:
    """Compose the first mismatch from canonical children without source scans."""
    root_key = SourceRootMatchKey(tile)
    found = lookup_source_root_match(arena, root_key)
    if found is not None:
        return found
    tasks = arena._causal_tasks
    if tasks is None:
        raise ValueError("source root matching requires the scheduler workspace")
    from number_compiler.hashlife.execution.tile_causal_tasks import CausalFrame

    frames = tasks.frames
    base = len(frames)
    frames.append(CausalFrame("source_root_match", (tile,)))
    try:
        while len(frames) > base:
            frame = frames.pop()
            current = frame.args[0]
            if type(current) is not TileID:
                raise TypeError("source root task lost its scoped tile")
            key = SourceRootMatchKey(current)
            cached = lookup_source_root_match(arena, key)
            if cached is not None:
                continue
            node = arena.tiles.resolve(current)
            if node.level and frame.stage == 0:
                if node.left is None or node.right is None:
                    raise ValueError("source root parent has missing children")
                frame.stage = 1
                frames.extend(
                    (
                        frame,
                        CausalFrame("source_root_match", (node.left,)),
                    )
                )
                continue
            if node.level and frame.stage == 1:
                if node.left is None or node.right is None:
                    raise ValueError("source root parent has missing children")
                left = lookup_source_root_match(arena, SourceRootMatchKey(node.left))
                if left is None:
                    raise AssertionError("source root left child was not published")
                if (
                    left.phase0_first_mismatch is not None
                    and left.phase1_first_mismatch is not None
                ):
                    arena.ledger.bump(_tiles_keys.COLLATZ_SOURCE_ROOT_MATCH_EVALUATIONS)
                    _publish(
                        arena,
                        key,
                        RootMatchResult(
                            node.level,
                            left.phase0_first_mismatch,
                            left.phase1_first_mismatch,
                        ),
                    )
                    continue
                frame.stage = 2
                frames.extend((frame, CausalFrame("source_root_match", (node.right,))))
                continue
            arena.ledger.bump(_tiles_keys.COLLATZ_SOURCE_ROOT_MATCH_EVALUATIONS)
            if node.level:
                if node.left is None or node.right is None:
                    raise ValueError("source root parent has missing children")
                left = lookup_source_root_match(arena, SourceRootMatchKey(node.left))
                right = lookup_source_root_match(arena, SourceRootMatchKey(node.right))
                if left is None or right is None:
                    raise AssertionError("source root children were not published")
                result = _parent(left, right)
            else:
                if node.symbol is None:
                    raise ValueError("source root leaf has no symbol")
                bit = 0 if node.symbol == 2 else node.symbol
                if bit not in (0, 1):
                    raise ValueError("source root leaf is not binary")
                result = RootMatchResult(
                    0,
                    None if bit == 1 else 0,
                    None if bit == 0 else 0,
                )
            _publish(arena, key, result)
    finally:
        while len(frames) > base:
            frames.pop()
    completed = lookup_source_root_match(arena, root_key)
    if completed is None:
        raise AssertionError("source root parent was not published")
    return completed


__all__ = [
    "RootMatchResult",
    "SourceRootMatchKey",
    "lookup_source_root_match",
    "source_root_match",
]
