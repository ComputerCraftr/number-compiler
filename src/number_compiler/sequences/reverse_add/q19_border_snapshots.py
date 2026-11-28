"""Exact structural snapshots of retained Q19 border receipt fields."""

from __future__ import annotations

from number_compiler.arithmetic.contracts.input_validation import is_exact_object_tuple

from .border_carry_safety import BorderTile


def typed_scalar_snapshot(value: object) -> tuple[object, object]:
    immutable_types = (int, bool, str, bytes, type(None))
    if type(value) in immutable_types:
        return type(value), value
    return type(value), id(value)


def tuple_snapshot(value: object) -> tuple[object, ...]:
    if not is_exact_object_tuple(value):
        return type(value), id(value)
    return tuple, tuple(typed_scalar_snapshot(item) for item in value)


def outer_pairs_snapshot(value: object) -> tuple[object, ...]:
    if not is_exact_object_tuple(value):
        return type(value), id(value)
    pairs: list[object] = []
    for pair in value:
        if is_exact_object_tuple(pair):
            pairs.append((tuple, tuple(typed_scalar_snapshot(item) for item in pair)))
        else:
            pairs.append(typed_scalar_snapshot(pair))
    return tuple, tuple(pairs)


def window_tile_snapshot(value: object) -> tuple[object, ...]:
    if type(value) is not BorderTile:
        return typed_scalar_snapshot(value)
    return (
        BorderTile,
        typed_scalar_snapshot(value.k),
        typed_scalar_snapshot(value.high),
        typed_scalar_snapshot(value.low),
    )


def window_tiles_snapshot(value: object) -> tuple[object, ...]:
    if not is_exact_object_tuple(value):
        return type(value), id(value)
    return tuple, tuple(window_tile_snapshot(tile) for tile in value)
