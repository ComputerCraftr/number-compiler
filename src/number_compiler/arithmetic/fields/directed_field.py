"""Directed finite-state projections over canonical dyadic fields.

A physical arithmetic carry is a one-way prefix scan.  This module projects
that scan over a recursively interned tile without ever storing a carry vector.
For every canonical tile and finite incoming carry state there is at most one
cached projected tile and outgoing carry.  Reflection/conjugacy are used only
for *action identity* through :class:`OrientedFiniteActionArena`; projection
itself remains in physical LSD->MSD order.
"""

from __future__ import annotations

import weakref
from collections.abc import Callable
from dataclasses import dataclass

from number_compiler.arithmetic.automata.symmetry_powering import (
    FiniteKernel,
    OrientedActionRef,
    OrientedFiniteActionArena,
)
from number_compiler.arithmetic.fields.dyadic_tile import (
    DyadicChunk,
    DyadicSpan,
    DyadicTile,
    join,
    leaf,
)


@dataclass(frozen=True, slots=True)
class DirectedProjection:
    tile: DyadicTile
    outgoing_state: int


@dataclass(frozen=True, slots=True)
class DirectedFieldMetrics:
    projection_requests: int
    projection_hits: int
    projection_entries: int
    action_requests: int
    action_hits: int
    unique_actions: int
    action_alias_hits: int
    mirror_alias_hits: int
    conjugate_alias_hits: int
    compose_hits: int


class DirectedTileTransducerArena:
    """Exact canonical tile transducer with finite LSD->MSD state."""

    __slots__ = (
        "_action_refs",
        "_project",
        "action_hits",
        "action_requests",
        "actions",
        "emit",
        "kernel",
        "output_alphabet_size",
        "projection_hits",
        "projection_requests",
    )

    def __init__(
        self,
        kernel: FiniteKernel,
        emit: Callable[[int, int], int],
        *,
        output_alphabet_size: int,
        compose_cache_limit: int = 4096,
    ) -> None:
        if int(output_alphabet_size) <= 0:
            raise ValueError(output_alphabet_size)
        kernel.verify_conjugacy()
        self.kernel = kernel
        self.emit = emit
        self.output_alphabet_size = int(output_alphabet_size)
        self.actions = OrientedFiniteActionArena(
            kernel,
            compose_cache_limit=compose_cache_limit,
        )
        self._action_refs: weakref.WeakKeyDictionary[DyadicTile, OrientedActionRef] = (
            weakref.WeakKeyDictionary()
        )
        self._project: weakref.WeakKeyDictionary[
            DyadicTile, dict[int, DirectedProjection]
        ] = weakref.WeakKeyDictionary()
        self.projection_requests = self.projection_hits = 0
        self.action_requests = self.action_hits = 0

    def action_ref(self, tile: DyadicTile) -> OrientedActionRef:
        self.action_requests += 1
        found = self._action_refs.get(tile)
        if found is not None:
            self.action_hits += 1
            return found
        built: dict[DyadicTile, OrientedActionRef] = {}
        stack: list[tuple[DyadicTile, bool]] = [(tile, False)]
        while stack:
            node, ready = stack.pop()
            cached = self._action_refs.get(node)
            if cached is not None:
                built[node] = cached
                continue
            if node.level == 0:
                if node.symbol is None:
                    raise AssertionError(node)
                ref = self.actions.leaf(int(node.symbol))
                self._action_refs[node] = ref
                built[node] = ref
                continue
            if node.left is None or node.right is None:
                raise AssertionError(node)
            if not ready:
                stack.append((node, True))
                if node.right not in built and node.right not in self._action_refs:
                    stack.append((node.right, False))
                if node.left not in built and node.left not in self._action_refs:
                    stack.append((node.left, False))
                continue
            left = self._action_refs.get(node.left, built.get(node.left))
            right = self._action_refs.get(node.right, built.get(node.right))
            if left is None or right is None:
                raise AssertionError(node)
            ref = self.actions.compose(left, right)
            self._action_refs[node] = ref
            built[node] = ref
        return self._action_refs[tile]

    def advance(self, tile: DyadicTile, incoming_state: int) -> int:
        """Advance a physical LSD->MSD carry across ``tile``."""
        return self.actions.apply(
            self.action_ref(tile), int(incoming_state), reverse=False
        )

    def advance_reflected_word(self, tile: DyadicTile, incoming_state: int) -> int:
        """Apply the reflected *word action* without reversing physical causality.

        This is for symmetry/conjugacy reasoning and right-context summaries.
        It is not an arithmetic carry scan from MSD toward LSD.
        """
        return self.actions.apply(
            self.action_ref(tile), int(incoming_state), reverse=True
        )

    def project(self, tile: DyadicTile, incoming_state: int) -> DirectedProjection:
        """Project output symbols and outgoing carry in physical LSD->MSD order."""
        incoming_state = int(incoming_state)
        if not 0 <= incoming_state < self.kernel.state_count:
            raise ValueError(incoming_state)
        self.projection_requests += 1
        # Intern the complete oriented action even when projection needs output
        # symbols.  This is where mirror/conjugate equivalent domains share a
        # semantic action ID while the physical projection below remains
        # strictly LSD->MSD.
        expected_outgoing = self.advance(tile, incoming_state)
        per = self._project.get(tile)
        if per is not None:
            found = per.get(incoming_state)
            if found is not None:
                self.projection_hits += 1
                return found

        # Explicit continuation stack.  Frames are (node, incoming, ready).
        built: dict[tuple[DyadicTile, int], DirectedProjection] = {}
        stack: list[tuple[DyadicTile, int, bool]] = [(tile, incoming_state, False)]
        while stack:
            node, state, ready = stack.pop()
            cached_map = self._project.get(node)
            if cached_map is not None and state in cached_map:
                built[(node, state)] = cached_map[state]
                continue
            if node.level == 0:
                if node.symbol is None:
                    raise AssertionError(node)
                symbol = int(node.symbol)
                out_symbol = int(self.emit(state, symbol))
                if not 0 <= out_symbol < self.output_alphabet_size:
                    raise ValueError((state, symbol, out_symbol))
                result = DirectedProjection(
                    leaf(out_symbol),
                    int(self.kernel.transition(state, symbol)),
                )
                self._project.setdefault(node, {})[state] = result
                built[(node, state)] = result
                continue
            if node.left is None or node.right is None:
                raise AssertionError(node)
            if not ready:
                stack.append((node, state, True))
                # left must be known before the right incoming state is known.
                left_cached = self._project.get(node.left)
                if left_cached is None or state not in left_cached:
                    stack.append((node.left, state, False))
                continue
            left_result = self._project.get(node.left, {}).get(
                state, built.get((node.left, state))
            )
            if left_result is None:
                raise AssertionError((node, state, "missing-left"))
            mid = int(left_result.outgoing_state)
            right_result = self._project.get(node.right, {}).get(
                mid, built.get((node.right, mid))
            )
            if right_result is None:
                # Resume parent after right has been projected.
                stack.append((node, state, True))
                stack.append((node.right, mid, False))
                continue
            result = DirectedProjection(
                join(left_result.tile, right_result.tile),
                int(right_result.outgoing_state),
            )
            self._project.setdefault(node, {})[state] = result
            built[(node, state)] = result

        result = self._project[tile][incoming_state]
        if result.outgoing_state != expected_outgoing:
            raise AssertionError((result.outgoing_state, expected_outgoing))
        return result

    def project_span(
        self, span: DyadicSpan, incoming_state: int
    ) -> tuple[DyadicSpan, int]:
        """Project one aligned forest left-to-right without flattening it."""
        state = int(incoming_state)
        chunks: list[DyadicChunk] = []
        for chunk in span.chunks:
            result = self.project(chunk.tile, state)
            chunks.append(DyadicChunk(chunk.start, result.tile))
            state = int(result.outgoing_state)
        return DyadicSpan(span.start, span.length, tuple(chunks)), state

    def advance_span(self, span: DyadicSpan, incoming_state: int) -> int:
        state = int(incoming_state)
        for chunk in span.chunks:
            state = self.advance(chunk.tile, state)
        return state

    def project_symbol_at(
        self,
        span: DyadicSpan,
        position: int,
        incoming_state: int = 0,
    ) -> tuple[int, int, int]:
        """Project exactly one output symbol without materializing its output tile.

        The returned tuple is ``(symbol, state_before, state_after)``.  Complete
        siblings before the queried leaf are skipped with their finite interval
        actions, so work is proportional to the dyadic forest/path depth rather
        than the represented field width.  Physical state propagation remains
        strictly LSD->MSD.
        """
        position = int(position)
        state = int(incoming_state)
        if not span.start <= position < span.end:
            raise IndexError(position)
        for chunk in span.chunks:
            end = chunk.start + chunk.tile.width
            if position >= end:
                state = self.advance(chunk.tile, state)
                continue
            if position < chunk.start:
                raise AssertionError((position, chunk.start))
            node = chunk.tile
            offset = position - chunk.start
            while node.level:
                if node.left is None or node.right is None:
                    raise AssertionError(node)
                left, right = node.left, node.right
                if offset < left.width:
                    node = left
                else:
                    state = self.advance(left, state)
                    offset -= left.width
                    node = right
            if node.symbol is None or offset:
                raise AssertionError((node, offset))
            symbol = int(node.symbol)
            out = int(self.emit(state, symbol))
            if not 0 <= out < self.output_alphabet_size:
                raise ValueError((state, symbol, out))
            after = int(self.kernel.transition(state, symbol))
            return out, state, after
        raise AssertionError((position, span.start, span.end))

    @property
    def projection_entries(self) -> int:
        return sum(len(per) for per in self._project.values())

    def metrics(self) -> DirectedFieldMetrics:
        am = self.actions.metrics()
        return DirectedFieldMetrics(
            self.projection_requests,
            self.projection_hits,
            self.projection_entries,
            self.action_requests,
            self.action_hits,
            am.action_count,
            am.action_alias_hits,
            am.mirror_alias_hits,
            am.conjugate_alias_hits,
            am.compose_hits,
        )


__all__ = [
    "DirectedFieldMetrics",
    "DirectedProjection",
    "DirectedTileTransducerArena",
]
