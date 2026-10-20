"""Demanded finite mirror sheets over shared canonical output tiles."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.polynomials.twisted_observer import (
    TwistedCylinderProjection,
)
from number_compiler.hashlife.execution.tile_application import TileApplication
from number_compiler.hashlife.tiles.tiles import TileArena, TileID
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.metric_keys import (
    hashlife_observation as _observation_keys,
)
from number_compiler.resources.stores import LedgerDict


@dataclass(frozen=True, slots=True)
class _Word:
    span: int
    forward: TwistedCylinderProjection
    reverse: TwistedCylinderProjection


class TileCylinderWorkspace:
    """Two reusable accounts; no per-sheet owner records accumulate in an index."""

    def __init__(self, ledger: ResourceLedger) -> None:
        self.ledger = ledger
        suffix = len(ledger.inventory())
        self.owner = ledger.register(
            f"tile-cylinder-values-{suffix}", "explicit_lowering"
        )
        self.values: LedgerDict[tuple[int, int], _Word] = ledger.make_dict(self.owner)
        self._disposed = False
        ledger.register_container(
            self.owner, self.values, node_count=self._nodes, payloads=self.values.items
        )
        self.frames: OwnedMemo[int, tuple[TileID, int, bool]] = OwnedMemo(
            ledger,
            ledger.register(f"tile-cylinder-frames-{suffix}", "explicit_lowering"),
            nodes_per_entry=1,
        )

    def _nodes(self) -> int:
        return sum(2 * word.forward.width + 3 for word in self.values.values())

    def put(self, key: tuple[int, int], value: _Word) -> None:
        if self._disposed:
            raise RuntimeError("cylinder workspace has been disposed")
        if key in self.values:
            raise AssertionError("cylinder subtree was already evaluated")
        nodes = 2 * value.forward.width + 3
        self.ledger.reserve(self.owner, entries=1, nodes=nodes)
        try:
            self.values[key] = value
        except BaseException:
            self.ledger.release(self.owner, entries=1, nodes=nodes)
            raise

    def clear(self) -> None:
        count, nodes = len(self.values), self._nodes()
        self.values.clear()
        self.ledger.release(self.owner, entries=count, nodes=nodes)
        self.frames.clear()

    def dispose(self) -> None:
        if self._disposed:
            return
        self.clear()
        self.frames.dispose()
        self.ledger.mark_disposed(self.owner)
        self._disposed = True


def _sheet(
    tiles: TileArena,
    root: TileID,
    extent: int,
    width: int,
    sign: int,
    workspace: TileCylinderWorkspace | None = None,
) -> TwistedCylinderProjection:
    """Fold a clipped prefix; identical subtrees with equal clips share work."""
    if (
        type(width) is not int
        or width < 1
        or type(sign) is not int
        or sign not in (-1, 1)
    ):
        raise ValueError("invalid cylinder sheet")
    ledger = tiles.ledger
    temporary = workspace is None
    workspace = TileCylinderWorkspace(ledger) if workspace is None else workspace
    if workspace.ledger is not ledger or workspace.values or workspace.frames:
        raise ValueError("cylinder workspace is foreign or already in use")
    values, frames = workspace.values, workspace.frames
    try:
        frames[0] = (root, extent, False)
        while frames:
            tile, take, ready = frames.pop(len(frames) - 1)
            record = tiles.resolve(tile)
            if not 0 < take <= record.width:
                raise ValueError("cylinder clip lies outside its tile")
            key = tile.local_id, take
            if key in values:
                ledger.bump(_observation_keys.TILE_CYLINDER_CACHE_HITS)
                continue
            if record.level == 0:
                alphabet = tiles.alphabet(record.alphabet)
                symbol = record.symbol
                if symbol is None:
                    raise ValueError("leaf tile omitted its symbol")
                if symbol == alphabet.blank:
                    raise ValueError("cylinder observation found interior padding")
                digit = symbol
                if not 0 <= digit < alphabet.radix:
                    raise ValueError("cylinder observation requires normalized digits")
                projection = TwistedCylinderProjection.observe(
                    (digit,), width=width, sign=sign
                )
                workspace.put(key, _Word(1, projection, projection))
                ledger.bump(_observation_keys.TILE_CYLINDER_LEAF_READS)
            else:
                left, right = record.left, record.right
                if left is None or right is None:
                    raise ValueError("branch tile omitted a child")
                half = record.width // 2
                left_take, right_take = min(take, half), max(0, take - half)
                if not ready:
                    frames[len(frames)] = (tile, take, True)
                    if right_take:
                        frames[len(frames)] = (right, right_take, False)
                    frames[len(frames)] = (left, left_take, False)
                    continue
                first = values[left.local_id, left_take]
                if not right_take:
                    workspace.put(key, first)
                else:
                    after = values[right.local_id, right_take]
                    workspace.put(
                        key,
                        _Word(
                            first.span + after.span,
                            first.forward.append(after.forward, span=first.span),
                            after.reverse.append(first.reverse, span=after.span),
                        ),
                    )
                    ledger.bump(_observation_keys.TILE_CYLINDER_COMPOSITIONS)
                    ledger.bump(
                        _observation_keys.TILE_CYLINDER_COEFFICIENT_ADDITIONS,
                        2 * width,
                    )
            ledger.bump(_observation_keys.TILE_CYLINDER_NODE_EVALUATIONS)
        word = values[root.local_id, extent]
        ledger.bump(_observation_keys.TILE_CYLINDER_COEFFICIENT_ADDITIONS, width)
        return TwistedCylinderProjection(
            width,
            sign,
            tuple(
                a - b
                for a, b in zip(
                    word.forward.coefficients, word.reverse.coefficients, strict=True
                )
            ),
        )
    finally:
        if temporary:
            workspace.dispose()
        else:
            workspace.clear()


def tile_mirror_obstruction(
    application: TileApplication,
    logical_extent: int,
    workspace: TileCylinderWorkspace,
    *,
    first_width: int = 1,
) -> TwistedCylinderProjection | None:
    """Consume the powered output DAG; all temporary coefficient storage is charged."""
    if type(first_width) is not int or first_width < 1:
        raise ValueError("positive first sheet width required")
    application.validate_execution()
    tiles = application.scheduler.tiles
    if (
        type(logical_extent) is not int
        or not 0 < logical_extent <= tiles.resolve(application.source).width
    ):
        raise ValueError("invalid cylinder observation extent")
    completed = application.complete()
    extent = tiles.active_width(completed.output, logical_extent)
    if extent < 1:
        raise ValueError("mirror observation requires a nonempty normalized word")
    width, sign = first_width, 1
    while True:
        projection = _sheet(tiles, completed.output, extent, width, sign, workspace)
        if projection.nonzero:
            return projection
        if width >= extent:
            return None
        if sign == 1:
            sign = -1
        else:
            width *= 2
