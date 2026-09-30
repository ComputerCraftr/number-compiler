"""Independent proof oracle for finite boundary actions on dyadic tiles.

Each finite bimachine side is a directed finite-state scan.  A dyadic tile is
summarized by the exact word action in *both* scan orientations.  Those two
mappings are canonicalized under reflection before the action receives an ID,
so a tile and its mirror share one semantic cache object plus one orientation
bit. Carry direction is never reversed physically; the stored transform tells
the caller which directed mapping to apply. Production execution uses scoped
TileIDs and the shared tile scheduler instead of this proof-only cache.
"""

from __future__ import annotations

import weakref
from dataclasses import dataclass

from number_compiler.arithmetic.automata.symmetry_powering import (
    FiniteKernel,
    OrientedActionRef,
    OrientedFiniteActionArena,
)
from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.block_kernel import FiniteBlockEffect
from number_compiler.arithmetic.fields.dyadic_tile import DyadicTile


@dataclass(frozen=True, slots=True)
class FiniteTileActionMetrics:
    requests: int
    tile_cache_hits: int
    compose_cache_hits: int
    semantic_alias_hits: int
    unique_actions: int
    mirror_alias_hits: int = 0
    conjugate_alias_hits: int = 0


class _SideArena:
    __slots__ = (
        "_arena",
        "_tile_actions",
        "alphabet_size",
        "effect",
        "requests",
        "side",
        "state_count",
        "tile_hits",
    )

    def __init__(
        self,
        effect: FiniteBlockEffect,
        side: BoundarySide,
        *,
        pair_cache_limit: int = 2048,
    ) -> None:
        self.effect = effect
        self.side = side
        self.state_count = (
            int(effect.left_count)
            if side is BoundarySide.LEFT
            else int(effect.right_count)
        )
        self.alphabet_size = int(effect.alphabet_size)
        table = (
            effect.left_transitions
            if side is BoundarySide.LEFT
            else effect.right_transitions
        )

        def transition(state: int, symbol: int) -> int:
            return int(table[int(state) * self.alphabet_size + int(symbol)])

        self._arena = OrientedFiniteActionArena(
            FiniteKernel(
                self.state_count,
                self.alphabet_size,
                transition,
                name=f"{effect.kernel_name}-{side.name.lower()}",
            ),
            compose_cache_limit=pair_cache_limit,
        )
        self._tile_actions: weakref.WeakKeyDictionary[DyadicTile, OrientedActionRef] = (
            weakref.WeakKeyDictionary()
        )
        self.requests = 0
        self.tile_hits = 0

    def action_ref(self, tile: DyadicTile) -> OrientedActionRef:
        self.requests += 1
        found = self._tile_actions.get(tile)
        if found is not None:
            self.tile_hits += 1
            return found
        built: dict[DyadicTile, OrientedActionRef] = {}
        stack: list[tuple[DyadicTile, bool]] = [(tile, False)]
        while stack:
            current, ready = stack.pop()
            cached = self._tile_actions.get(current)
            if cached is not None:
                built[current] = cached
                continue
            if current.level == 0:
                if current.symbol is None:
                    raise AssertionError(current)
                ref = self._arena.leaf(int(current.symbol))
                self._tile_actions[current] = ref
                built[current] = ref
                continue
            if current.left is None or current.right is None:
                raise AssertionError(current)
            if not ready:
                stack.append((current, True))
                if (
                    current.right not in built
                    and current.right not in self._tile_actions
                ):
                    stack.append((current.right, False))
                if current.left not in built and current.left not in self._tile_actions:
                    stack.append((current.left, False))
                continue
            left = self._tile_actions.get(current.left, built.get(current.left))
            right = self._tile_actions.get(current.right, built.get(current.right))
            if left is None or right is None:
                raise AssertionError((current.node_id, left, right))
            ref = self._arena.compose(left, right)
            self._tile_actions[current] = ref
            built[current] = ref
        return self._tile_actions[tile]

    def contains_tile(self, tile: DyadicTile) -> bool:
        return tile in self._tile_actions

    def action_id(self, tile: DyadicTile) -> int:
        return self.action_ref(tile).action_id

    def apply(self, tile: DyadicTile, state: int) -> int:
        ref = self.action_ref(tile)
        # A RIGHT boundary scan consumes the physical word from high to low.
        return self._arena.apply(
            ref,
            int(state),
            reverse=self.side is BoundarySide.RIGHT,
        )

    @property
    def retained_entries(self) -> int:
        return len(self._tile_actions) + self._arena.retained_entries

    def retained_tiles(self) -> tuple[DyadicTile, ...]:
        return tuple(self._tile_actions.keys())

    def metrics(self) -> FiniteTileActionMetrics:
        metrics = self._arena.metrics()
        return FiniteTileActionMetrics(
            self.requests,
            self.tile_hits,
            metrics.compose_hits,
            metrics.action_alias_hits,
            metrics.action_count,
            metrics.mirror_alias_hits,
            metrics.conjugate_alias_hits,
        )


class FiniteTileActionArena:
    """Own exact left/right oriented action quotients for one finite effect."""

    __slots__ = ("effect", "left", "right")

    def __init__(
        self, effect: FiniteBlockEffect, *, pair_cache_limit: int = 2048
    ) -> None:
        self.effect = effect
        self.left = _SideArena(
            effect, BoundarySide.LEFT, pair_cache_limit=pair_cache_limit
        )
        self.right = _SideArena(
            effect, BoundarySide.RIGHT, pair_cache_limit=pair_cache_limit
        )

    def apply(self, side: BoundarySide, tile: DyadicTile, state: int) -> int:
        arena = self.left if side is BoundarySide.LEFT else self.right
        return arena.apply(tile, int(state))

    def contains_tile(self, side: BoundarySide, tile: DyadicTile) -> bool:
        arena = self.left if side is BoundarySide.LEFT else self.right
        return arena.contains_tile(tile)

    @property
    def retained_entries(self) -> int:
        return self.left.retained_entries + self.right.retained_entries

    def retained_tiles(self) -> tuple[DyadicTile, ...]:
        # The same canonical tile can be present in both oriented side caches.
        return tuple({*self.left.retained_tiles(), *self.right.retained_tiles()})

    def metrics(self) -> tuple[FiniteTileActionMetrics, FiniteTileActionMetrics]:
        return self.left.metrics(), self.right.metrics()


__all__ = ["FiniteTileActionArena", "FiniteTileActionMetrics"]
