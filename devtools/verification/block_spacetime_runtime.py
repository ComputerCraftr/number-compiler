"""Joint spatial/temporal macrocell runtime for composed block effects.

Persistent memo keys retain canonical quadtree/action objects. Construction-order
IDs are diagnostics only; they are never a lifetime boundary for HashLife reuse.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, TypeGuard, TypeVar, cast

from devtools.verification.block_recursive import (
    _ProviderLayer,
    _RecursiveBoundaryState,
    _RecursiveResidualAction,
)
from devtools.verification.spacetime_boundary import tile_uniform_symbol
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudget,
    BlockEffect,
    BoundarySide,
    BoundaryState,
    _cache_state_key,
    _effect_key,
    _state_key,
)
from number_compiler.arithmetic.fields.dyadic_tile import DyadicTile, existing_join

if TYPE_CHECKING:
    from devtools.verification.block_composed import ComposedBlockEffect


_MemoKey = TypeVar("_MemoKey")
_MemoValue = TypeVar("_MemoValue")


def _right_frame(
    frame: tuple[object, ...],
) -> tuple[tuple[object, ...], DyadicTile, bool]:
    return (
        cast(tuple[object, ...], frame[1]),
        cast(DyadicTile, frame[2]),
        bool(frame[3]),
    )


def recursive_residual_phase(
    residual: _RecursiveResidualAction | None,
    modulus: int,
) -> int:
    """Return only the bounded alignment phase needed by dyadic composition.

    Production never needs the absolute number of source cells already scanned.
    For a level-k incoming tile, canonical placement depends only on the current
    coordinate modulo ``2**k``; sibling folding needs the phase modulo the parent
    width.  Keeping this calculation modular prevents a growing scalar tape
    extent from becoming hidden runtime state.  Full represented extent is
    reconstructed only by diagnostics.
    """
    modulus = int(modulus)
    if modulus <= 0:
        raise ValueError(modulus)
    phase = 0
    current = residual
    while current is not None and current.previous is not None:
        if current.tile is None:
            raise AssertionError(current)
        phase = (phase + int(current.tile.width)) % modulus
        current = current.previous
    return phase


def is_composed_runtime(effect: object) -> TypeGuard[ComposedBlockEffect]:
    return (
        hasattr(effect, "_partition_enabled")
        and hasattr(effect, "_functional_enabled")
        and hasattr(effect, "_recursive_enabled")
    )


class SpacetimeRuntimeMixin:
    # ComposedBlockEffect supplies these shared caches and child interfaces.
    @property
    def first(self) -> BlockEffect:
        raise NotImplementedError

    @property
    def second(self) -> BlockEffect:
        raise NotImplementedError

    budget: BlockContextBudget
    _states: list[int]
    _recursive_enabled: tuple[bool, bool]
    _recursive_residual_intern: tuple[
        dict[tuple[object, ...], _RecursiveResidualAction] | None,
        dict[tuple[object, ...], _RecursiveResidualAction] | None,
    ]
    _recursive_residual_intern_hits: int
    _recursive_residual_intern_misses: int
    _recursive_value_cache: dict[tuple[object, object], BoundaryState]
    _recursive_value_cache_hits: int
    _recursive_value_cache_misses: int
    _macro_tile_advance_cache: dict[tuple[object, ...], BoundaryState]
    _macro_tile_advance_hits: int
    _macro_tile_advance_misses: int
    _macro_tile_output_cache: dict[tuple[object, ...], object]
    _macro_tile_output_hits: int
    _macro_tile_output_misses: int
    _macro_output_hits: int
    _macro_output_misses: int
    _provider_task_cache: dict[tuple[object, ...], BoundaryState]
    _provider_task_hits: int
    _provider_task_misses: int

    def recursive_side_enabled(self, side: BoundarySide) -> bool:
        return self._recursive_enabled[int(side)]

    def provider_task_lookup(
        self, key: tuple[object, ...], sentinel: object
    ) -> BoundaryState:
        found = self._provider_task_cache.get(key, sentinel)
        if found is sentinel:
            self._provider_task_misses += 1
        else:
            self._provider_task_hits += 1
        return found

    def publish_provider_task(
        self, key: tuple[object, ...], value: BoundaryState
    ) -> None:
        self._memo_store(self._provider_task_cache, key, value)

    def recursive_value_lookup(self, key: tuple[object, object]) -> BoundaryState:
        found = self._recursive_value_cache.get(key)
        if found is not None:
            self._recursive_value_cache_hits += 1
        return found

    def has_recursive_value(self, key: tuple[object, object]) -> bool:
        return key in self._recursive_value_cache

    def publish_recursive_value(
        self, key: tuple[object, object], value: BoundaryState
    ) -> None:
        self._memo_store(self._recursive_value_cache, key, value)
        self._recursive_value_cache_misses += 1

    @staticmethod
    def canonical_child_state(
        effect: object, side: BoundarySide, state: BoundaryState
    ) -> BoundaryState:
        raise NotImplementedError

    def _memo_store(
        self,
        cache: dict[_MemoKey, _MemoValue],
        key: _MemoKey,
        value: _MemoValue,
    ) -> _MemoValue:
        """Store one persistent memo entry and charge it exactly once."""
        if key not in cache:
            self.budget.consume_cache()
        cache[key] = value
        return value

    def intern_recursive_residual(
        self,
        side: BoundarySide,
        previous: _RecursiveResidualAction,
        tile: DyadicTile,
        anchor_after: BoundaryState,
        *,
        reverse: bool = False,
        layers: tuple[_ProviderLayer, ...] = (),
    ) -> _RecursiveResidualAction:
        """Hash-cons one exact occurrence node, folding a canonical dyadic forest.

        ``anchor_after`` is deterministic from ``previous.anchor`` and ``tile``.
        It is stored on the canonical node because that node is also the boundary
        state.  There is no separate boundary-state wrapper and no stored
        ``anchor_before``; for a non-constant node the latter is exactly
        ``previous.anchor``.
        """
        index = int(side)
        pool = self._recursive_residual_intern[index]
        if pool is None:
            raise AssertionError("recursive residual carrier is not enabled")
        anchor_after = self.canonical_child_state(self.first, side, anchor_after)
        current = tile
        current_reverse = reverse
        prior = previous
        while (
            prior.previous is not None
            and prior.tile is not None
            and not layers
            and not prior.layers
            and prior.reversed == current_reverse
            and prior.tile.level == current.level
            and recursive_residual_phase(prior.previous, 2 * current.width) == 0
        ):
            parent = (
                existing_join(current, prior.tile)
                if current_reverse
                else existing_join(prior.tile, current)
            )
            if parent is None:
                break
            current = parent
            prior = prior.previous
        # The pre-action boundary is carried by the previous canonical node; the
        # occurrence identity itself therefore needs only the forest prefix + tile.
        layer_key = tuple(
            (
                _effect_key(layer.effect),
                _cache_state_key(layer.left),
                _cache_state_key(layer.right),
            )
            for layer in layers
        )
        key = (prior, current, current_reverse, layer_key)
        found = pool.get(key)
        if found is not None:
            if found.anchor is not anchor_after and _cache_state_key(
                found.anchor
            ) != _cache_state_key(anchor_after):
                raise AssertionError(
                    (
                        "recursive action anchor mismatch",
                        side,
                        found.anchor,
                        anchor_after,
                    )
                )
            self._recursive_residual_intern_hits += 1
            return found
        out = _RecursiveResidualAction(
            side,
            prior,
            current,
            anchor_after,
            layers,
            reversed=current_reverse,
        )
        pool[key] = out
        self._recursive_residual_intern_misses += 1
        self.budget.consume_node()
        self._states[index] += 1
        from number_compiler.arithmetic.automata.guard import record_residual_metrics

        record_residual_metrics(states=1)
        return out

    def intern_recursive_state(
        self,
        side: BoundarySide,
        anchor: BoundaryState,
        residual: _RecursiveResidualAction,
    ) -> _RecursiveBoundaryState:
        """Return the already-canonical merged occurrence/state node.

        This method remains only as a compatibility seam for callers that used
        to allocate a second wrapper.  It performs a consistency check and never
        allocates, interns, or increments fake state-cache hit/miss counters.
        """
        anchor = self.canonical_child_state(self.first, side, anchor)
        if residual.side is not side:
            raise ValueError((residual.side, side))
        if residual.anchor is not anchor and _cache_state_key(
            residual.anchor
        ) != _cache_state_key(anchor):
            raise AssertionError(
                (
                    "recursive state/action anchor mismatch",
                    side,
                    residual.anchor,
                    anchor,
                )
            )
        return residual

    def _advance_recursive_tile(
        self,
        side: BoundarySide,
        state: _RecursiveBoundaryState,
        tile: DyadicTile,
        *,
        reverse: bool = False,
    ) -> _RecursiveBoundaryState:
        """Advance one canonical tile without manufacturing a second state space.

        The residual retains the exact source action as a hash-consed dyadic
        forest.  Uniform padding is therefore already logarithmic in represented
        length.  Do **not** delete/cap source cells here: doing so can collapse the
        residual forest while leaving its first-child anchor in a different state,
        which creates late noncanonical IDs after the anchors later reconverge.
        """
        if state.side is not side:
            raise ValueError((state.side, side))
        if not self._recursive_enabled[int(side)]:
            raise AssertionError("recursive carrier is not enabled")

        # Align by splitting only existing immutable source tiles.  Point/width
        # execution must not manufacture an exact occurrence span merely to
        # express dyadic alignment.
        phase = recursive_residual_phase(state.residual, tile.width)
        pending: list[tuple[int, DyadicTile, bool]] = [(phase, tile, reverse)]
        aligned_tiles: list[tuple[DyadicTile, bool]] = []
        while pending:
            origin, current, current_reverse = pending.pop()
            if current.level == 0 or origin % current.width == 0:
                aligned_tiles.append((current, current_reverse))
                continue
            if current.left is None or current.right is None:
                raise AssertionError(current)
            logical_left, logical_right = (
                (current.right, current.left)
                if current_reverse
                else (current.left, current.right)
            )
            pending.append(
                (origin + logical_left.width, logical_right, current_reverse)
            )
            pending.append((origin, logical_left, current_reverse))
        anchor = state.anchor
        residual = state.residual
        for current, current_reverse in aligned_tiles:
            before = anchor
            anchor = self.advance_effect_tile_macro(
                self.first,
                side,
                before,
                current,
                reverse=current_reverse,
            )
            residual = self.intern_recursive_residual(
                side,
                residual,
                current,
                anchor,
                reverse=current_reverse,
            )
        return self.intern_recursive_state(side, anchor, residual)

    @staticmethod
    def _provider_symbol(tile: DyadicTile, layers: tuple[_ProviderLayer, ...]) -> int:
        """Evaluate one transient provider leaf without retaining its output."""
        if tile.level or tile.symbol is None:
            raise ValueError("a scalar provider observation requires an original leaf")
        symbol = int(tile.symbol)
        for layer in layers:
            symbol = int(layer.effect.emit(layer.left, symbol, layer.right))
        return symbol

    def _advance_provider_leaf(
        self,
        effect: BlockEffect,
        side: BoundarySide,
        state: BoundaryState,
        tile: DyadicTile,
        layers: tuple[_ProviderLayer, ...],
    ) -> BoundaryState:
        """Advance through a symbolic image leaf while retaining its source leaf.

        Recursive children receive the same immutable original leaf plus the
        provider program.  The transient output scalar is never wrapped in a
        ``DyadicTile`` and never enters a semantic cache key.
        """
        result = self.run_provider_tasks(("ADV", effect, side, state, tile, layers))
        return result

    def _emit_provider_leaf(
        self,
        effect: BlockEffect,
        left: BoundaryState,
        tile: DyadicTile,
        layers: tuple[_ProviderLayer, ...],
        right: BoundaryState,
    ) -> int:
        result = self.run_provider_tasks(("EMIT", effect, left, right, tile, layers))
        if type(result) is not int:
            raise AssertionError("provider emission returned another result sort")
        return result

    def run_provider_tasks(self, root: tuple[object, ...]) -> BoundaryState:
        from devtools.verification.provider_recurrence import run_provider_tasks

        return run_provider_tasks(self, root)

    def _eval_recursive_residual(
        self,
        side: BoundarySide,
        residual: _RecursiveResidualAction,
        argument: BoundaryState,
    ) -> BoundaryState:
        """Evaluate a recursive residual through fused spacetime diamonds.

        The old implementation first materialized ``first(tile)`` as an exact
        future ``DyadicTile`` and then scanned that tile through ``second``.
        Here the first-child boundary interfaces are retained symbolically and
        the second child consumes emitted symbols directly while descending the
        original source tile.  No future exact tile exists at any point.
        """
        opposite = (
            BoundarySide.RIGHT if side is BoundarySide.LEFT else BoundarySide.LEFT
        )
        argument = self.canonical_child_state(self.first, opposite, argument)
        root_key: tuple[object, object] = (residual, _cache_state_key(argument))
        found = self._recursive_value_cache.get(root_key)
        if found is not None:
            self._recursive_value_cache_hits += 1
            return found

        frames: list[
            tuple[
                tuple[object, object],
                DyadicTile,
                bool,
                tuple[_ProviderLayer, ...],
                BoundaryState,
                BoundaryState,
            ]
        ] = []
        current = residual
        current_argument = argument
        base_value: BoundaryState | None = None
        while True:
            key: tuple[object, object] = (current, _cache_state_key(current_argument))
            cached = self._recursive_value_cache.get(key)
            if cached is not None:
                self._recursive_value_cache_hits += 1
                base_value = cached
                break
            if current.previous is None:
                base_value = self.second.initial(side)
                self._memo_store(self._recursive_value_cache, key, base_value)
                self._recursive_value_cache_misses += 1
                break
            if current.tile is None:
                raise AssertionError(current)
            anchor_before = current.previous.anchor
            argument_after = current_argument
            if current.layers:
                argument_before = self._advance_provider_leaf(
                    self.first,
                    opposite,
                    argument_after,
                    current.tile,
                    current.layers,
                )
            else:
                argument_before = self.advance_effect_tile_macro(
                    self.first,
                    opposite,
                    argument_after,
                    current.tile,
                    reverse=not current.reversed,
                )
            frames.append(
                (
                    key,
                    current.tile,
                    current.reversed,
                    current.layers,
                    anchor_before,
                    argument_after,
                )
            )
            current_argument = self.canonical_child_state(
                self.first, opposite, argument_before
            )
            current = current.previous

        if base_value is None:
            raise AssertionError("recursive residual evaluation lost base value")
        value = base_value
        while frames:
            key, tile, tile_reverse, layers, anchor_before, argument_after = (
                frames.pop()
            )
            value = self._advance_second_over_first_output(
                side,
                value,
                tile,
                anchor_before,
                argument_after,
                reverse=tile_reverse,
                layers=layers,
            )
            value = self.canonical_child_state(self.second, side, value)
            if key not in self._recursive_value_cache:
                self._memo_store(self._recursive_value_cache, key, value)
                self._recursive_value_cache_misses += 1
        return value

    def _advance_second_over_first_output(
        self,
        side: BoundarySide,
        second_state: BoundaryState,
        tile: DyadicTile,
        anchor_before: BoundaryState,
        argument_after: BoundaryState,
        *,
        reverse: bool = False,
        layers: tuple[_ProviderLayer, ...] = (),
    ) -> BoundaryState:
        """Advance ``second`` across ``first(tile)`` without creating that image.

        This is the composed HashLife diamond.  Cache keys use one canonical
        source macrocell plus the complete causal boundary states.  A hit skips
        every descendant and every emitted symbol.
        """
        opposite = (
            BoundarySide.RIGHT if side is BoundarySide.LEFT else BoundarySide.LEFT
        )
        root_key: tuple[object, ...] = (
            "fused",
            int(side),
            tile,
            reverse,
            tuple(
                (
                    _effect_key(layer.effect),
                    _cache_state_key(layer.left),
                    _cache_state_key(layer.right),
                )
                for layer in layers
            ),
            _cache_state_key(anchor_before),
            _cache_state_key(argument_after),
            _cache_state_key(second_state),
        )
        found = self._macro_tile_output_cache.get(root_key)
        if found is not None:
            self._macro_output_hits += 1
            self._macro_tile_output_hits += 1
            return found
        self._macro_output_misses += 1
        self._macro_tile_output_misses += 1

        results: list[BoundaryState] = []
        tasks: list[tuple[object, ...]] = [
            (
                "EVAL",
                tile,
                reverse,
                layers,
                anchor_before,
                argument_after,
                second_state,
                True,
            )
        ]
        while tasks:
            frame = tasks.pop()
            tag = frame[0]
            if tag == "EVAL":
                current = cast(DyadicTile, frame[1])
                current_reverse = bool(frame[2])
                current_layers = cast(tuple[_ProviderLayer, ...], frame[3])
                anchor, argument, incoming = frame[4], frame[5], frame[6]
                root_already_missed = bool(frame[7])
                key: tuple[object, ...] = (
                    "fused",
                    int(side),
                    current,
                    current_reverse,
                    tuple(
                        (
                            _effect_key(layer.effect),
                            _cache_state_key(layer.left),
                            _cache_state_key(layer.right),
                        )
                        for layer in current_layers
                    ),
                    _cache_state_key(anchor),
                    _cache_state_key(argument),
                    _cache_state_key(incoming),
                )
                if not root_already_missed:
                    cached = self._macro_tile_output_cache.get(key)
                    if cached is not None:
                        self._macro_output_hits += 1
                        self._macro_tile_output_hits += 1
                        results.append(cached)
                        continue
                    self._macro_output_misses += 1
                    self._macro_tile_output_misses += 1

                if current.level == 0:
                    if current.symbol is None:
                        raise AssertionError(current)
                    first_symbol = self._emit_provider_leaf(
                        self.first,
                        anchor if side is BoundarySide.LEFT else argument,
                        current,
                        current_layers,
                        argument if side is BoundarySide.LEFT else anchor,
                    )
                    if (
                        is_composed_runtime(self.second)
                        and self.second._recursive_enabled[int(side)]
                    ):
                        provider = current_layers + (
                            _ProviderLayer(
                                self.first,
                                anchor if side is BoundarySide.LEFT else argument,
                                argument if side is BoundarySide.LEFT else anchor,
                            ),
                        )
                        out = self._advance_provider_leaf(
                            self.second,
                            side,
                            incoming,
                            current,
                            provider,
                        )
                    else:
                        out = self.second.advance(side, incoming, int(first_symbol))
                    out = self.canonical_child_state(self.second, side, out)
                    self._memo_store(self._macro_tile_output_cache, key, out)
                    results.append(out)
                    continue

                if current.left is None or current.right is None:
                    raise AssertionError(current)
                if current_layers:
                    raise AssertionError(
                        "provider actions must remain bound to source leaves"
                    )
                left, right = (
                    (current.right, current.left)
                    if current_reverse
                    else (current.left, current.right)
                )
                middle_anchor = self.advance_effect_tile_macro(
                    self.first,
                    side,
                    anchor,
                    left,
                    reverse=current_reverse,
                )
                middle_argument = self.advance_effect_tile_macro(
                    self.first,
                    opposite,
                    argument,
                    right,
                    reverse=not current_reverse,
                )
                tasks.append(
                    (
                        "AFTER_LEFT",
                        key,
                        right,
                        current_reverse,
                        current_layers,
                        middle_anchor,
                        argument,
                    )
                )
                tasks.append(
                    (
                        "EVAL",
                        left,
                        current_reverse,
                        current_layers,
                        anchor,
                        middle_argument,
                        incoming,
                        False,
                    )
                )
                continue

            if tag == "AFTER_LEFT":
                key, right, right_reverse = _right_frame(frame)
                right_layers = cast(tuple[_ProviderLayer, ...], frame[4])
                middle_anchor, final_argument = frame[5], frame[6]
                middle_second = results.pop()
                tasks.append(("AFTER_RIGHT", key))
                tasks.append(
                    (
                        "EVAL",
                        right,
                        right_reverse,
                        right_layers,
                        middle_anchor,
                        final_argument,
                        middle_second,
                        False,
                    )
                )
                continue

            if tag == "AFTER_RIGHT":
                key = cast(tuple[object, ...], frame[1])
                out = results.pop()
                self._memo_store(self._macro_tile_output_cache, key, out)
                results.append(out)
                continue
            raise AssertionError(tag)

        if len(results) != 1:
            raise AssertionError(len(results))
        out = results[0]
        self._memo_store(self._macro_tile_output_cache, root_key, out)
        return out

    @staticmethod
    def _advance_uniform_macro(
        effect: BlockEffect,
        side: BoundarySide,
        state: BoundaryState,
        symbol: int,
        count: int,
    ) -> BoundaryState:
        """Advance a uniform macrocell with exact cycle skipping."""
        count = int(count)
        if count <= 0:
            return state
        out = state
        seen: dict[object, tuple[int, BoundaryState]] = {}
        step = 0
        while step < count:
            key = _state_key(out)
            prior = seen.get(key)
            if prior is not None:
                prior_step, prior_state = prior
                if _state_key(prior_state) != key:
                    raise AssertionError((prior_state, out))
                cycle = step - prior_step
                if cycle > 0:
                    skip = (count - step) // cycle
                    if skip:
                        step += skip * cycle
                        continue
            else:
                seen[key] = (step, out)
            out = effect.advance(side, out, int(symbol))
            step += 1
        return out

    def advance_effect_tile_macro(
        self,
        effect: BlockEffect,
        side: BoundarySide,
        state: BoundaryState,
        tile: DyadicTile,
        *,
        reverse: bool = False,
    ) -> BoundaryState:
        """Advance one canonical tile in the cache owned by ``effect``.

        A parent composed node frequently asks one of its temporal children to
        scan a spatial tile while constructing a future macrocell.  Storing that
        action in the *parent* cache duplicates the exact same
        ``(effect, side, state, tile)`` entry when the child is queried directly
        later.  Route composed children to their own memo arena before touching
        this node's cache.  Runtime statistics already traverse the operator DAG,
        so ownership follows the algebra node without losing accounting.
        """
        if is_composed_runtime(effect) and effect is not self:
            return effect.advance_effect_tile_macro(
                effect,
                side,
                state,
                tile,
                reverse=reverse,
            )
        root_key = (
            _effect_key(effect),
            int(side),
            _cache_state_key(state),
            tile,
            reverse,
        )
        found = self._macro_tile_advance_cache.get(root_key)
        if found is not None:
            self._macro_tile_advance_hits += 1
            return found
        self._macro_tile_advance_misses += 1

        results: list[BoundaryState] = []
        tasks: list[tuple[object, ...]] = [("EVAL", tile, reverse, state, True)]
        while tasks:
            frame = tasks.pop()
            tag = frame[0]
            if tag == "EVAL":
                current = frame[1]
                current_reverse = bool(frame[2])
                incoming = frame[3]
                root_already_missed = bool(frame[4])
                if not isinstance(current, DyadicTile):
                    raise AssertionError(current)
                key: tuple[object, ...] = (
                    _effect_key(effect),
                    int(side),
                    _cache_state_key(incoming),
                    current,
                    current_reverse,
                )
                if not root_already_missed:
                    cached = self._macro_tile_advance_cache.get(key)
                    if cached is not None:
                        self._macro_tile_advance_hits += 1
                        results.append(cached)
                        continue
                    self._macro_tile_advance_misses += 1

                if (
                    is_composed_runtime(effect)
                    and isinstance(incoming, _RecursiveBoundaryState)
                    and effect._recursive_enabled[int(side)]
                ):
                    out: BoundaryState = effect._advance_recursive_tile(
                        side,
                        incoming,
                        current,
                        reverse=current_reverse,
                    )
                    self._memo_store(self._macro_tile_advance_cache, key, out)
                    results.append(out)
                    continue

                uniform = tile_uniform_symbol(current)
                if uniform is not None:
                    out = self._advance_uniform_macro(
                        effect, side, incoming, uniform, current.width
                    )
                    self._memo_store(self._macro_tile_advance_cache, key, out)
                    results.append(out)
                    continue
                if current.left is None or current.right is None:
                    raise AssertionError(current)
                left, right = (
                    (current.right, current.left)
                    if current_reverse
                    else (current.left, current.right)
                )
                tasks.append(("AFTER_LEFT", key, right, current_reverse))
                tasks.append(("EVAL", left, current_reverse, incoming, False))
                continue

            if tag == "AFTER_LEFT":
                key, right, right_reverse = _right_frame(frame)
                middle = results.pop()
                tasks.append(("AFTER_RIGHT", key))
                tasks.append(("EVAL", right, right_reverse, middle, False))
                continue

            if tag == "AFTER_RIGHT":
                key = cast(tuple[object, ...], frame[1])
                out = results.pop()
                self._memo_store(self._macro_tile_advance_cache, key, out)
                results.append(out)
                continue
            raise AssertionError(tag)

        if len(results) != 1:
            raise AssertionError(len(results))
        out = results[0]
        self._memo_store(self._macro_tile_advance_cache, root_key, out)
        return out


__all__ = ["SpacetimeRuntimeMixin"]
