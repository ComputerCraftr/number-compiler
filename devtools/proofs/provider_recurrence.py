"""Store-free provider recurrence operations."""

from __future__ import annotations

from typing import TYPE_CHECKING, cast

from devtools.proofs.block_recursive import (
    _ProviderLayer,
    _RecursiveBoundaryState,
)
from number_compiler.arithmetic.contracts.block_effect import (
    BlockEffect,
    BoundarySide,
    BoundaryState,
    _cache_state_key,
)
from number_compiler.arithmetic.fields.dyadic_tile import DyadicTile

if TYPE_CHECKING:
    from devtools.proofs.block_composed import ComposedBlockEffect
    from devtools.proofs.block_spacetime_runtime import SpacetimeRuntimeMixin


def _run_provider_tasks(
    self: SpacetimeRuntimeMixin, root: tuple[object, ...]
) -> BoundaryState:
    from devtools.proofs.block_spacetime_runtime import _is_composed_runtime

    """Evaluate symbolic provider leaves through one nonrecursive task stack."""
    sentinel = object()
    cached_root = self._provider_task_cache.get(root, sentinel)
    if cached_root is not sentinel:
        self._provider_task_hits += 1
        return cached_root
    self._provider_task_misses += 1
    tasks: list[tuple[object, ...]] = [root]
    results: list[BoundaryState] = []
    while tasks:
        frame = tasks.pop()
        tag = frame[0]
        if tag == "ADV":
            effect = cast(BlockEffect, frame[1])
            side = cast(BoundarySide, frame[2])
            state = frame[3]
            tile = cast(DyadicTile, frame[4])
            layers = cast(tuple[_ProviderLayer, ...], frame[5])
            if _is_composed_runtime(effect) and effect._recursive_enabled[int(side)]:
                if not isinstance(state, _RecursiveBoundaryState):
                    raise AssertionError(type(state))
                tasks.append(("ADV_COMPOSED", effect, side, state, tile, layers))
                tasks.append(("ADV", effect.first, side, state.anchor, tile, layers))
            elif layers:
                layer = layers[-1]
                tasks.append(("ADV_PRIMITIVE", effect, side, state))
                tasks.append(
                    (
                        "EMIT",
                        layer.effect,
                        layer.left,
                        layer.right,
                        tile,
                        layers[:-1],
                    )
                )
            else:
                if tile.level or tile.symbol is None:
                    raise ValueError("provider scalar requires an original source leaf")
                results.append(effect.advance(side, state, int(tile.symbol)))
            continue
        if tag == "ADV_PRIMITIVE":
            symbol = results.pop()
            if type(symbol) is not int:
                raise AssertionError("provider symbol left its finite alphabet")
            effect = cast(BlockEffect, frame[1])
            results.append(
                effect.advance(cast(BoundarySide, frame[2]), frame[3], symbol)
            )
            continue
        if tag == "ADV_COMPOSED":
            anchor = results.pop()
            effect = cast("ComposedBlockEffect", frame[1])
            side = cast(BoundarySide, frame[2])
            state = cast(_RecursiveBoundaryState, frame[3])
            tile = cast(DyadicTile, frame[4])
            layers = cast(tuple[_ProviderLayer, ...], frame[5])
            residual = effect._intern_recursive_residual(
                side,
                state.residual,
                tile,
                anchor,
                layers=layers,
            )
            results.append(effect._intern_recursive_state(side, anchor, residual))
            continue
        if tag == "EMIT":
            effect = cast(BlockEffect, frame[1])
            left, right = frame[2], frame[3]
            tile = cast(DyadicTile, frame[4])
            layers = cast(tuple[_ProviderLayer, ...], frame[5])
            if _is_composed_runtime(effect):
                left_anchor = effect._state_anchor(BoundarySide.LEFT, left)
                right_anchor = effect._state_anchor(BoundarySide.RIGHT, right)
                tasks.append(
                    (
                        "EMIT_COMPOSED",
                        effect,
                        left,
                        right,
                        tile,
                        layers,
                        left_anchor,
                        right_anchor,
                    )
                )
                tasks.append(
                    (
                        "ADV",
                        effect.first,
                        BoundarySide.LEFT,
                        left_anchor,
                        tile,
                        layers,
                    )
                )
                tasks.append(
                    (
                        "ADV",
                        effect.first,
                        BoundarySide.RIGHT,
                        right_anchor,
                        tile,
                        layers,
                    )
                )
                tasks.append(
                    ("EMIT", effect.first, left_anchor, right_anchor, tile, layers)
                )
            elif layers:
                layer = layers[-1]
                tasks.append(("EMIT_PRIMITIVE", effect, left, right))
                tasks.append(
                    (
                        "EMIT",
                        layer.effect,
                        layer.left,
                        layer.right,
                        tile,
                        layers[:-1],
                    )
                )
            else:
                if tile.level or tile.symbol is None:
                    raise ValueError("provider scalar requires an original source leaf")
                results.append(int(effect.emit(left, int(tile.symbol), right)))
            continue
        if tag == "EMIT_PRIMITIVE":
            symbol = results.pop()
            if type(symbol) is not int:
                raise AssertionError("provider symbol left its finite alphabet")
            results.append(
                int(
                    cast(BlockEffect, frame[1]).emit(
                        frame[2],
                        symbol,
                        frame[3],
                    )
                )
            )
            continue
        if tag == "EMIT_COMPOSED":
            right_argument = results.pop()
            left_argument = results.pop()
            first_symbol = results.pop()
            if type(first_symbol) is not int:
                raise AssertionError("first output left its finite alphabet")
            effect = cast("ComposedBlockEffect", frame[1])
            left, right = frame[2], frame[3]
            tile = cast(DyadicTile, frame[4])
            layers = cast(tuple[_ProviderLayer, ...], frame[5])
            left_anchor, right_anchor = frame[6], frame[7]
            tasks.append(
                (
                    "EMIT_AFTER_RESIDUALS",
                    effect,
                    tile,
                    layers,
                    left_anchor,
                    right_anchor,
                )
            )
            tasks.append(("RES", effect, BoundarySide.RIGHT, right, right_argument))
            tasks.append(("RES", effect, BoundarySide.LEFT, left, left_argument))
            continue
        if tag == "EMIT_AFTER_RESIDUALS":
            second_right = results.pop()
            second_left = results.pop()
            effect = cast("ComposedBlockEffect", frame[1])
            tile = cast(DyadicTile, frame[2])
            layers = cast(tuple[_ProviderLayer, ...], frame[3])
            provider = layers + (_ProviderLayer(effect.first, frame[4], frame[5]),)
            tasks.append(
                (
                    "EMIT",
                    effect.second,
                    second_left,
                    second_right,
                    tile,
                    provider,
                )
            )
            continue
        if tag == "RES":
            effect = cast("ComposedBlockEffect", frame[1])
            side = cast(BoundarySide, frame[2])
            state = frame[3]
            argument = effect._canonical_child_state(
                effect.first,
                BoundarySide.RIGHT if side is BoundarySide.LEFT else BoundarySide.LEFT,
                frame[4],
            )
            if not isinstance(state, _RecursiveBoundaryState):
                results.append(
                    effect._residual_value_for_argument(side, state, argument)
                )
                continue
            key = (state.residual, _cache_state_key(argument))
            cached = effect._recursive_value_cache.get(key)
            if cached is not None:
                effect._recursive_value_cache_hits += 1
                results.append(cached)
            elif state.previous is None:
                value = effect.second.initial(side)
                effect._memo_store(effect._recursive_value_cache, key, value)
                effect._recursive_value_cache_misses += 1
                results.append(value)
            else:
                if state.tile is None:
                    raise AssertionError("recursive residual has no source tile")
                opposite = (
                    BoundarySide.RIGHT
                    if side is BoundarySide.LEFT
                    else BoundarySide.LEFT
                )
                tasks.append(("RES_ARGUMENT", effect, side, state, argument, key))
                if state.layers:
                    tasks.append(
                        (
                            "ADV",
                            effect.first,
                            opposite,
                            argument,
                            state.tile,
                            state.layers,
                        )
                    )
                else:
                    argument_before = effect._advance_effect_tile_macro(
                        effect.first,
                        opposite,
                        argument,
                        state.tile,
                        reverse=not state.reversed,
                    )
                    results.append(argument_before)
            continue
        if tag == "RES_ARGUMENT":
            argument_before = results.pop()
            effect = cast("ComposedBlockEffect", frame[1])
            state = cast(_RecursiveBoundaryState, frame[3])
            tasks.append(("RES_PREVIOUS", effect, frame[2], state, frame[4], frame[5]))
            tasks.append(("RES", effect, frame[2], state.previous, argument_before))
            continue
        if tag == "RES_PREVIOUS":
            value = results.pop()
            effect = cast("ComposedBlockEffect", frame[1])
            side = cast(BoundarySide, frame[2])
            state = cast(_RecursiveBoundaryState, frame[3])
            previous = state.previous
            if state.tile is None or previous is None:
                raise AssertionError("recursive residual has no source tile")
            tasks.append(("RES_STORE", effect, frame[5]))
            tasks.append(
                (
                    "SECOND",
                    effect,
                    side,
                    value,
                    state.tile,
                    state.layers,
                    previous.anchor,
                    frame[4],
                    state.reversed,
                )
            )
            continue
        if tag == "RES_STORE":
            value = results[-1]
            effect = cast("ComposedBlockEffect", frame[1])
            store_key = cast(tuple[object, object], frame[2])
            if store_key not in effect._recursive_value_cache:
                effect._memo_store(effect._recursive_value_cache, store_key, value)
                effect._recursive_value_cache_misses += 1
            continue
        if tag == "SECOND":
            effect = cast("ComposedBlockEffect", frame[1])
            side = cast(BoundarySide, frame[2])
            incoming = frame[3]
            tile = cast(DyadicTile, frame[4])
            layers = cast(tuple[_ProviderLayer, ...], frame[5])
            anchor, argument, reverse = frame[6], frame[7], bool(frame[8])
            if tile.level == 0:
                provider = layers + (
                    _ProviderLayer(
                        effect.first,
                        anchor if side is BoundarySide.LEFT else argument,
                        argument if side is BoundarySide.LEFT else anchor,
                    ),
                )
                tasks.append(("ADV", effect.second, side, incoming, tile, provider))
                continue
            if layers or tile.left is None or tile.right is None:
                raise AssertionError("provider parent cannot be split")
            opposite = (
                BoundarySide.RIGHT if side is BoundarySide.LEFT else BoundarySide.LEFT
            )
            left, right = (
                (tile.right, tile.left) if reverse else (tile.left, tile.right)
            )
            middle_anchor = effect._advance_effect_tile_macro(
                effect.first,
                side,
                anchor,
                left,
                reverse=reverse,
            )
            middle_argument = effect._advance_effect_tile_macro(
                effect.first,
                opposite,
                argument,
                right,
                reverse=not reverse,
            )
            tasks.append(
                (
                    "SECOND_RIGHT",
                    effect,
                    side,
                    right,
                    middle_anchor,
                    argument,
                    reverse,
                )
            )
            tasks.append(
                (
                    "SECOND",
                    effect,
                    side,
                    incoming,
                    left,
                    (),
                    anchor,
                    middle_argument,
                    reverse,
                )
            )
            continue
        if tag == "SECOND_RIGHT":
            middle = results.pop()
            tasks.append(
                (
                    "SECOND",
                    frame[1],
                    frame[2],
                    middle,
                    frame[3],
                    (),
                    frame[4],
                    frame[5],
                    frame[6],
                )
            )
            continue
        raise AssertionError(tag)
    if len(results) != 1:
        raise AssertionError((root[0], len(results)))
    result = results[0]
    self._memo_store(self._provider_task_cache, root, result)
    return result
