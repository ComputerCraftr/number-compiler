"""Canonical source/future content with explicit, reclaimable root leases.

Future leaves are permitted alphabet symbols, not packed words.  Tile identity
contains content alone; ports, actions and execution weights belong to results.
"""

from __future__ import annotations

from dataclasses import dataclass
from gc import get_stats
from time import perf_counter_ns
from typing import TYPE_CHECKING, Self

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.resources.cache_gc_metrics import CacheEventMetrics
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    hashlife_tiles as _tiles_keys,
)
from number_compiler.resources.stores import LedgerDict

if TYPE_CHECKING:
    from number_compiler.hashlife.tiles.tile_results import CompletedResultArena


@dataclass(frozen=True, slots=True)
class TileAlphabetID(ArenaHandle):
    """One frozen interpretation of a tile's symbols."""


@dataclass(frozen=True, slots=True)
class TileID(ArenaHandle):
    """Canonical content identity, valid only while the tile is live."""


@dataclass(frozen=True, slots=True)
class TileAlphabet:
    symbol_count: int
    blank: int
    radix: int
    cell_bits: int
    interpretation: str
    version: str

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (
                self.symbol_count,
                self.blank,
                self.radix,
                self.cell_bits,
            )
        ):
            raise TypeError("tile alphabet quantities require exact integers")
        if (
            self.symbol_count < 2
            or not 0 <= self.blank < self.symbol_count
            or self.radix < 2
            or self.cell_bits < 1
            or (self.symbol_count - 1).bit_length() > self.cell_bits
        ):
            raise ValueError("inconsistent tile alphabet")
        if any(
            type(value) is not str or not value
            for value in (
                self.interpretation,
                self.version,
            )
        ):
            raise TypeError("tile interpretation and version must be explicit")


@dataclass(frozen=True, slots=True)
class TileRecord:
    alphabet: TileAlphabetID
    level: int
    symbol: int | None
    left: TileID | None
    right: TileID | None
    first_active: int | None
    last_active: int | None

    @property
    def width(self) -> int:
        return 1 << self.level

    @property
    def extent(self) -> int:
        return 0 if self.last_active is None else self.last_active + 1


_LEASE_SEAL = object()
_TileKey = tuple[int, int, int, int, int]
_MIRROR_SENTINEL = -2


class TileLease:
    """An explicit root reference; close it when the owner releases its result."""

    __slots__ = ("_arena", "_closed", "_id")

    def __init__(self, arena: TileArena, lease_id: int, seal: object) -> None:
        if seal is not _LEASE_SEAL:
            raise TypeError("tile leases must be issued by their arena")
        self._arena, self._id, self._closed = arena, lease_id, False

    @property
    def tile(self) -> TileID:
        if type(self._arena) is not TileArena or type(self._closed) is not bool:
            raise TypeError("malformed tile lease")
        if self._closed:
            raise ValueError("closed tile lease")
        tile = self._arena._leased(self._id)
        self._arena.resolve(tile)
        return tile

    def close(self) -> None:
        if type(self._arena) is not TileArena or type(self._closed) is not bool:
            raise TypeError("malformed tile lease")
        if not self._closed:
            self._arena._release_lease(self._id)
            self._closed = True

    def __enter__(self) -> Self:
        _ = self.tile
        return self

    def __exit__(self, *_exception: object) -> None:
        self.close()


class TileArena:
    """One index-owned tile interner; no historical result is retained implicitly."""

    def __init__(self, ledger: ResourceLedger) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("tiles require an index ledger")
        self.ledger = ledger
        self.owner = ArenaToken("canonical-tiles")
        self._next_tile = self._next_alphabet = self._next_lease = 0
        self._retirement_occurred = False
        self._results: CompletedResultArena | None = None
        prefix = f"canonical-tiles-{len(ledger.inventory())}"
        self._cache_metrics = CacheEventMetrics(ledger, prefix)
        self._alphabet_owner = ledger.register(prefix + "-alphabets", "tile_alphabet")
        self._alphabet_key_owner = ledger.register(
            prefix + "-alphabet-keys", "tile_alphabet_interner"
        )
        self._node_owner = ledger.register(prefix + "-nodes", "canonical_tile")
        self._key_owner = ledger.register(prefix + "-keys", "canonical_tile_interner")
        self._ref_owner = ledger.register(
            prefix + "-references", "tile_reference_count"
        )
        self._edge_owner = ledger.register(
            prefix + "-edges", "tile_child_reverse_index"
        )
        self._lease_owner = ledger.register(prefix + "-leases", "tile_root_lease")
        self._alphabets: LedgerDict[int, TileAlphabet] = ledger.make_dict(
            self._alphabet_owner, nodes_per_entry=1
        )
        self._alphabet_keys: LedgerDict[TileAlphabet, int] = ledger.make_dict(
            self._alphabet_key_owner
        )
        self._nodes: LedgerDict[int, TileRecord] = ledger.make_dict(
            self._node_owner, nodes_per_entry=1
        )
        self._keys: LedgerDict[_TileKey, int] = ledger.make_dict(self._key_owner)
        self._refs: LedgerDict[int, int] = ledger.make_dict(self._ref_owner)
        self._edges: LedgerDict[tuple[int, int, int], None] = ledger.make_dict(
            self._edge_owner
        )
        self._leases: LedgerDict[int, TileID] = ledger.make_dict(self._lease_owner)
        ledger.register_execution_root(self)
        ledger.register_container(
            self._lease_owner,
            self._leases,
            payloads=self._leases.items,
            roots=lambda: self._leases.values(),
            node_count=lambda: 0,
        )

    def bind_results(self, results: CompletedResultArena) -> None:
        from number_compiler.hashlife.tiles.tile_results import CompletedResultArena

        if type(results) is not CompletedResultArena:
            raise TypeError("tile retirement requires the canonical result memo owner")
        if results.tiles is not self or results.ledger is not self.ledger:
            raise ValueError("tile result memo belongs to another arena")
        if not any(root is results for root in self.ledger.iter_execution_roots()):
            raise ValueError("tile result memo is not a registered execution owner")
        if self._results is not None and self._results is not results:
            raise ValueError("a tile arena has only one result memo owner")
        self._results = results

    def intern_alphabet(self, value: TileAlphabet) -> TileAlphabetID:
        if type(value) is not TileAlphabet:
            raise TypeError("expected a frozen tile alphabet")
        value.__post_init__()
        found = self._alphabet_keys.get(value)
        if found is not None:
            reference = TileAlphabetID(self.owner, "tile-alphabet", found)
            if self.alphabet(reference) != value:
                raise ValueError("alphabet interner points to another interpretation")
            return reference
        reservations = ((self._alphabet_owner, 1, 1), (self._alphabet_key_owner, 1, 0))
        self.ledger.reserve_many(reservations)
        local_id = self._next_alphabet
        self._next_alphabet += 1
        try:
            self._alphabets[local_id] = value
            self._alphabet_keys[value] = local_id
        except BaseException:
            self._alphabets.pop(local_id, None)
            self._alphabet_keys.pop(value, None)
            for owner, entries, nodes in reservations:
                self.ledger.release(owner, entries, nodes)
            raise
        return TileAlphabetID(self.owner, "tile-alphabet", local_id)

    def alphabet(self, reference: TileAlphabetID) -> TileAlphabet:
        if type(reference) is not TileAlphabetID:
            raise TypeError("expected a tile alphabet ID")
        reference.validate(self.owner, "tile-alphabet", size=self._next_alphabet)
        try:
            return self._alphabets[reference.local_id]
        except KeyError as error:
            raise ValueError("unpublished tile alphabet") from error

    def resolve(self, reference: TileID) -> TileRecord:
        if type(reference) is not TileID:
            raise TypeError("expected a canonical tile ID")
        reference.validate(self.owner, "canonical-tile", size=self._next_tile)
        try:
            return self._nodes[reference.local_id]
        except KeyError as error:
            raise ValueError("stale or unpublished tile") from error

    @staticmethod
    def _key(record: TileRecord) -> _TileKey:
        return (
            record.alphabet.local_id,
            record.level,
            -1 if record.symbol is None else record.symbol,
            -1 if record.left is None else record.left.local_id,
            -1 if record.right is None else record.right.local_id,
        )

    def _acquire(self, tile: TileID) -> TileLease:
        self.resolve(tile)
        self.ledger.reserve(self._lease_owner, entries=1)
        try:
            return self._acquire_reserved(tile)
        except BaseException:
            self.ledger.release(self._lease_owner, entries=1)
            raise

    def _acquire_reserved(self, tile: TileID) -> TileLease:
        """Publish a lease within an already reserved multi-store transaction.

        The caller owns the reservation and releases it if publication fails.
        This private seam lets complete-result publication reserve its memo,
        reverse index and output lease together before any retained mutation.
        """
        self.resolve(tile)
        lease_id = self._next_lease
        lease = TileLease(self, lease_id, _LEASE_SEAL)
        self._next_lease += 1
        old = self._refs[tile.local_id]
        acquisition_before = self.ledger.counters.get(
            _tiles_keys.TILE_LEASE_ACQUISITIONS
        )
        peak_before = self.ledger.counters.get(_tiles_keys.TILE_ROOT_LEASE_PEAK)
        peak_after = max(peak_before or 0, len(self._leases) + 1)
        try:
            self._leases[lease_id] = tile
            self._observe_peak(_tiles_keys.TILE_ROOT_LEASE_PEAK, len(self._leases))
            self._refs[tile.local_id] = old + 1
            self.ledger.bump(_tiles_keys.TILE_LEASE_ACQUISITIONS)
        except BaseException:
            self._leases.pop(lease_id, None)
            self._refs[tile.local_id] = old
            if (
                peak_after != peak_before
                and self.ledger.counters.get(_tiles_keys.TILE_ROOT_LEASE_PEAK)
                == peak_after
            ):
                if peak_before is None:
                    self.ledger.counters.pop(_tiles_keys.TILE_ROOT_LEASE_PEAK, None)
                else:
                    self.ledger.counters[_tiles_keys.TILE_ROOT_LEASE_PEAK] = peak_before
            acquisition_after = self.ledger.counters.get(
                _tiles_keys.TILE_LEASE_ACQUISITIONS
            )
            expected_acquisition = (acquisition_before or 0) + 1
            if acquisition_after == expected_acquisition:
                if acquisition_before is None:
                    self.ledger.counters.pop(_tiles_keys.TILE_LEASE_ACQUISITIONS, None)
                else:
                    self.ledger.counters[_tiles_keys.TILE_LEASE_ACQUISITIONS] = (
                        acquisition_before
                    )
            raise
        return lease

    def _observe_peak(self, name: str, value: int) -> None:
        self.ledger.counters[name] = max(self.ledger.counters.get(name, 0), value)

    def retain(self, tile: TileID) -> TileLease:
        self.resolve(tile)
        return self._acquire(tile)

    def leaf(self, alphabet: TileAlphabetID, symbol: int) -> TileLease:
        interpretation = self.alphabet(alphabet)
        if type(symbol) is not int:
            raise TypeError("tile leaf requires an exact alphabet symbol")
        if not 0 <= symbol < interpretation.symbol_count:
            raise ValueError("tile symbol is outside its alphabet")
        active = None if symbol == interpretation.blank else 0
        return self._intern(TileRecord(alphabet, 0, symbol, None, None, active, active))

    def join(self, left: TileID, right: TileID) -> TileLease:
        before, after = self.resolve(left), self.resolve(right)
        if before.alphabet != after.alphabet or before.level != after.level:
            raise ValueError("tile children require the same alphabet and level")
        offset = before.width
        first = before.first_active
        if first is None and after.first_active is not None:
            first = offset + after.first_active
        last = before.last_active
        if after.last_active is not None:
            last = offset + after.last_active
        return self._intern(
            TileRecord(
                before.alphabet,
                before.level + 1,
                None,
                left,
                right,
                first,
                last,
            )
        )

    @staticmethod
    def _mirror_key(local_id: int) -> _TileKey:
        return _MIRROR_SENTINEL, local_id, -1, -1, -1

    def _mirror_target(self, tile: TileID) -> TileID | None:
        target = self._keys.get(self._mirror_key(tile.local_id))
        if target is None:
            return None
        if type(target) is not int:
            raise TypeError("tile mirror index contains an integer alias")
        mirrored = TileID(self.owner, "canonical-tile", target)
        self.resolve(mirrored)
        if self._keys.get(self._mirror_key(target)) != tile.local_id:
            raise ValueError("tile mirror index is not involutive")
        return mirrored

    def _write_mirror(self, key: _TileKey, local_id: int) -> None:
        """Fault-injection seam for atomic mirror-index publication."""
        self._keys[key] = local_id

    def _publish_mirror(self, source: TileID, mirrored: TileID) -> None:
        before, after = self.resolve(source), self.resolve(mirrored)
        if before.alphabet != after.alphabet or before.level != after.level:
            raise ValueError("mirrored tiles require one alphabet and level")
        if before.level == 0:
            if before.symbol != after.symbol:
                raise ValueError("mirrored leaves require the same exact symbol")
        elif (
            before.left is None
            or before.right is None
            or after.left is None
            or after.right is None
            or self._mirror_target(before.left) != after.right
            or self._mirror_target(before.right) != after.left
        ):
            raise ValueError("tile mirror relation disagrees with canonical children")
        pairs: tuple[tuple[int, int], ...] = ((source.local_id, mirrored.local_id),)
        if source != mirrored:
            pairs += ((mirrored.local_id, source.local_id),)
        for local_id, target in pairs:
            found = self._keys.get(self._mirror_key(local_id))
            if found is not None and found != target:
                raise ValueError("tile already has another canonical mirror")
        missing = tuple(
            (self._mirror_key(local_id), target)
            for local_id, target in pairs
            if self._mirror_key(local_id) not in self._keys
        )
        self.ledger.reserve(self._key_owner, entries=len(missing))
        written: list[_TileKey] = []
        try:
            for key, target in missing:
                self._write_mirror(key, target)
                written.append(key)
        except BaseException:
            for key in written:
                self._keys.pop(key, None)
            self.ledger.release(self._key_owner, entries=len(missing))
            raise
        self.ledger.bump(_tiles_keys.TILE_MIRROR_PUBLICATIONS, len(missing))

    def mirror(self, tile: TileID) -> TileLease:
        """Return the exact reflected content through an iterative cached DAG walk."""
        self.resolve(tile)
        self.ledger.bump(_tiles_keys.TILE_MIRROR_REQUESTS)
        found = self._mirror_target(tile)
        if found is not None:
            self.ledger.bump(_tiles_keys.TILE_MIRROR_EARLY_HITS)
            return self._acquire(found)
        frames: list[tuple[TileID, bool]] = [(tile, False)]
        values: list[TileLease] = []
        try:
            while frames:
                current, ready = frames.pop()
                cached = self._mirror_target(current)
                if cached is not None:
                    values.append(self._acquire(cached))
                    continue
                record = self.resolve(current)
                if record.level == 0:
                    leaf = self._acquire(current)
                    try:
                        self._publish_mirror(current, current)
                    except BaseException:
                        leaf.close()
                        raise
                    values.append(leaf)
                    continue
                if not ready:
                    if record.left is None or record.right is None:
                        raise ValueError("malformed canonical parent")
                    frames.extend(
                        ((current, True), (record.left, False), (record.right, False))
                    )
                    continue
                if len(values) < 2:
                    raise AssertionError("tile mirror lost a child")
                left_mirror, right_mirror = values.pop(), values.pop()
                try:
                    parent = self.join(right_mirror.tile, left_mirror.tile)
                finally:
                    left_mirror.close()
                    right_mirror.close()
                try:
                    self._publish_mirror(current, parent.tile)
                except BaseException:
                    parent.close()
                    raise
                values.append(parent)
            if len(values) != 1:
                raise AssertionError("tile mirror produced another result arity")
            self.ledger.bump(_tiles_keys.TILE_MIRROR_EVALUATIONS)
            return values.pop()
        except BaseException:
            for value in reversed(values):
                value.close()
            raise

    def _intern(self, record: TileRecord) -> TileLease:
        self._validate_record(record)
        key = self._key(record)
        self.ledger.bump(_tiles_keys.TILE_INTERN_REQUESTS)
        found = self._keys.get(key)
        if found is not None:
            tile = TileID(self.owner, "canonical-tile", found)
            self.resolve(tile)
            result = self._acquire(tile)
            self.ledger.bump(_tiles_keys.TILE_INTERN_EARLY_HITS)
            self._cache_metrics.record(
                "tile",
                "early_hit",
                spatial_level=record.level,
                temporal_span=None,
                allow_new=False,
            )
            return result
        if self._retirement_occurred:
            self.ledger.bump(_tiles_keys.TILE_RECREATION_ATTRIBUTION_UNKNOWN)
        children = tuple(
            child for child in (record.left, record.right) if child is not None
        )
        reservations = (
            (self._node_owner, 1, 1),
            (self._key_owner, 1, 0),
            (self._ref_owner, 1, 0),
            (self._lease_owner, 1, 0),
            (self._edge_owner, len(children), 0),
        )
        self.ledger.reserve_many(reservations)
        local_id, lease_id = self._next_tile, self._next_lease
        self._next_tile += 1
        self._next_lease += 1
        tile = TileID(self.owner, "canonical-tile", local_id)
        old_refs = {child.local_id: self._refs[child.local_id] for child in children}
        try:
            self._nodes[local_id] = record
            self._observe_peak("canonical_tile_peak", len(self._nodes))
            self._keys[key] = local_id
            self._refs[local_id] = 1
            self._leases[lease_id] = tile
            self._observe_peak(_tiles_keys.TILE_ROOT_LEASE_PEAK, len(self._leases))
            for side, child in enumerate(children):
                self._edges[child.local_id, local_id, side] = None
                self._refs[child.local_id] += 1
        except BaseException:
            for child_id, old in old_refs.items():
                self._refs[child_id] = old
            for side, child in enumerate(children):
                self._edges.pop((child.local_id, local_id, side), None)
            self._leases.pop(lease_id, None)
            self._refs.pop(local_id, None)
            self._keys.pop(key, None)
            self._nodes.pop(local_id, None)
            for owner, entries, nodes in reservations:
                self.ledger.release(owner, entries, nodes)
            raise
        self.ledger.bump(_tiles_keys.TILE_PUBLICATIONS)
        self._cache_metrics.prepare(
            "tile",
            "early_hit",
            spatial_level=record.level,
            temporal_span=None,
        )
        self._cache_metrics.record(
            "tile",
            "publication",
            spatial_level=record.level,
            temporal_span=None,
        )
        self.ledger.bump(_tiles_keys.TILE_LEASE_ACQUISITIONS)
        return TileLease(self, lease_id, _LEASE_SEAL)

    def _leased(self, lease_id: int) -> TileID:
        if type(lease_id) is not int:
            raise TypeError("tile lease identity requires an exact integer")
        if not 0 <= lease_id < self._next_lease or lease_id not in self._leases:
            raise ValueError("stale or unpublished tile lease")
        return self._leases[lease_id]

    def _validate_record(self, record: TileRecord) -> None:
        if type(record) is not TileRecord or type(record.level) is not int:
            raise TypeError("tile publication requires a canonical record")
        alphabet = self.alphabet(record.alphabet)
        if record.level < 0:
            raise ValueError("negative tile level")
        if record.level == 0:
            if (
                type(record.symbol) is not int
                or not 0 <= record.symbol < alphabet.symbol_count
                or record.left is not None
                or record.right is not None
            ):
                raise ValueError("invalid canonical leaf")
            first = last = None if record.symbol == alphabet.blank else 0
        else:
            if record.symbol is not None or record.left is None or record.right is None:
                raise ValueError("canonical parent requires exactly two children")
            left, right = self.resolve(record.left), self.resolve(record.right)
            if (
                left.alphabet != record.alphabet
                or right.alphabet != record.alphabet
                or left.level != record.level - 1
                or right.level != record.level - 1
            ):
                raise ValueError("tile parent has another alphabet or child level")
            first = left.first_active
            if first is None and right.first_active is not None:
                first = left.width + right.first_active
            last = left.last_active
            if right.last_active is not None:
                last = left.width + right.last_active
        for actual, expected in (
            (record.first_active, first),
            (record.last_active, last),
        ):
            if (actual is not None and type(actual) is not int) or actual != expected:
                raise ValueError("tile summary differs from canonical content")

    def _release_lease(self, lease_id: int) -> None:
        tile = self._leased(lease_id)
        self.resolve(tile)
        del self._leases[lease_id]
        self.ledger.release(self._lease_owner, entries=1)
        self._refs[tile.local_id] -= 1
        pending = [tile.local_id] if self._refs[tile.local_id] == 0 else []
        started = perf_counter_ns() if pending else 0
        gc_before = (
            tuple(
                sum(generation[name] for generation in get_stats())
                for name in ("collections", "collected", "uncollectable")
            )
            if pending
            else (0, 0, 0)
        )
        while pending:
            current = pending.pop()
            record = self._nodes[current]
            reference = TileID(self.owner, "canonical-tile", current)
            if self._results is not None:
                self._results.retire_tile(reference)
            mirror_key = self._mirror_key(current)
            mirror = self._keys.pop(mirror_key, None)
            removed_mirrors = int(mirror is not None)
            if type(mirror) is int and mirror != current:
                reverse_key = self._mirror_key(mirror)
                if self._keys.get(reverse_key) != current:
                    raise ValueError("tile mirror reverse index is corrupt")
                del self._keys[reverse_key]
                removed_mirrors += 1
            self.ledger.release(self._key_owner, entries=removed_mirrors)
            del self._keys[self._key(record)]
            del self._nodes[current]
            del self._refs[current]
            self.ledger.release(self._key_owner, entries=1)
            self.ledger.release(self._node_owner, entries=1, nodes=1)
            self.ledger.release(self._ref_owner, entries=1)
            for side, child in enumerate((record.left, record.right)):
                if child is None:
                    continue
                del self._edges[child.local_id, current, side]
                self.ledger.release(self._edge_owner, entries=1)
                self._refs[child.local_id] -= 1
                if self._refs[child.local_id] == 0:
                    pending.append(child.local_id)
            self.ledger.bump(_tiles_keys.TILE_RETIREMENTS)
        if started:
            gc_after = tuple(
                sum(generation[name] for generation in get_stats())
                for name in ("collections", "collected", "uncollectable")
            )
            self.ledger.bump(
                _tiles_keys.TILE_RETIREMENT_WORK_NS,
                perf_counter_ns() - started,
            )
            for name, before, after in zip(
                (
                    "python_gc_collections_during_tile_retirement",
                    "python_gc_collected_during_tile_retirement",
                    "python_gc_uncollectable_during_tile_retirement",
                ),
                gc_before,
                gc_after,
                strict=True,
            ):
                self.ledger.bump(name, after - before)
            self._retirement_occurred = True
        self.ledger.bump(_tiles_keys.TILE_LEASE_RELEASES)

    def point(self, tile: TileID, coordinate: int) -> int:
        record = self.resolve(tile)
        if type(coordinate) is not int:
            raise TypeError("tile coordinate requires an exact integer")
        if not 0 <= coordinate < record.width:
            raise IndexError(coordinate)
        while record.level:
            half = 1 << (record.level - 1)
            child = record.left if coordinate < half else record.right
            if child is None:
                raise ValueError("malformed canonical parent")
            if coordinate >= half:
                coordinate -= half
            record = self.resolve(child)
            self.ledger.bump(_tiles_keys.TILE_OBSERVATION_DESCENTS)
        if record.symbol is None:
            raise ValueError("malformed canonical leaf")
        return record.symbol

    def active_width(self, tile: TileID, stop: int | None = None) -> int:
        """Rightmost active coordinate in a prefix, using derived summaries.

        A clipped observation must search that prefix; taking the minimum of
        the full extent and the clip would invent activity in an empty gap.
        """
        root = self.resolve(tile)
        if stop is None:
            stop = root.width
        if type(stop) is not int:
            raise TypeError("tile extent limit requires an exact integer")
        if not 0 <= stop <= root.width:
            raise ValueError("tile extent limit is outside the tile")
        pending = [(root, 0)]
        while pending:
            node, start = pending.pop()
            self.ledger.bump(_tiles_keys.TILE_WIDTH_DESCENTS)
            if start >= stop or node.last_active is None:
                continue
            last = start + node.last_active
            if last < stop:
                return last + 1
            if node.level == 0 or node.left is None or node.right is None:
                raise ValueError("malformed canonical activity summary")
            pending.append((self.resolve(node.left), start))
            pending.append((self.resolve(node.right), start + (1 << (node.level - 1))))
        return 0


__all__ = [
    "TileAlphabet",
    "TileAlphabetID",
    "TileArena",
    "TileID",
    "TileLease",
    "TileRecord",
]
