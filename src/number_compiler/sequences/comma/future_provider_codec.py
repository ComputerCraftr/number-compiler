"""Bounded canonical decoding for FutureCID class tables."""

from __future__ import annotations

from number_compiler.arithmetic.contracts.input_validation import (
    is_object_list_instance,
)
from number_compiler.sequences.comma.future_authority import FutureClass, FutureControl


def decode_class_map(
    payload: bytes,
    class_count: int,
    *,
    source_count: int,
    max_varint_bytes: int,
) -> tuple[int, ...]:
    """Decode the bounded canonical varint map from sources to class IDs."""
    if type(payload) is not bytes or len(payload) > source_count * max_varint_bytes:
        raise ValueError("future source map exceeds its bounded varint payload")
    values: list[int] = []
    current = 0
    shift = 0
    width = 0
    for byte in payload:
        width += 1
        if width > max_varint_bytes:
            raise ValueError("future source map contains an oversized CID varint")
        current |= (byte & 0x7F) << shift
        if byte & 0x80:
            shift += 7
            continue
        if current >= class_count:
            raise ValueError("future source map contains an out-of-range CID")
        if width > 1 and current < (1 << (7 * (width - 1))):
            raise ValueError("future source map contains a noncanonical CID varint")
        values.append(current)
        if len(values) > source_count:
            raise ValueError("future source map has too many source entries")
        current = 0
        shift = 0
        width = 0
    if width:
        raise ValueError("future source map ends with a truncated CID varint")
    if len(values) != source_count:
        raise ValueError("future source map is truncated or has extra source entries")
    return tuple(values)


def decode_class_rows(
    raw_controls: list[object],
    raw_children: list[object],
    raw_ranks: list[object],
    class_count: int,
) -> tuple[FutureClass, ...]:
    """Decode exactly two ordered children and one optional rank per class."""
    result: list[FutureClass] = []
    for raw_control, raw_row, raw_rank in zip(
        raw_controls, raw_children, raw_ranks, strict=True
    ):
        if not is_object_list_instance(raw_control) or len(raw_control) != 2:
            raise ValueError("future class control is malformed")
        kind, coefficient = raw_control
        if type(kind) is not str:
            raise ValueError("future class control is neither Fork nor Landmine")
        if kind == "fork":
            if type(coefficient) is not int or not 2 <= coefficient <= 9:
                raise ValueError("future Fork control needs its exact coefficient")
            control = FutureControl("fork", coefficient)
        elif kind == "landmine":
            if coefficient is not None:
                raise ValueError("future Landmine control cannot carry a coefficient")
            control = FutureControl("landmine", coefficient)
        else:
            raise ValueError("future class control is neither Fork nor Landmine")
        if not is_object_list_instance(raw_row) or len(raw_row) != 2:
            raise ValueError("future class row must preserve two ordered slots")
        children: list[int | None] = []
        for target in raw_row:
            if target is None:
                children.append(None)
            elif type(target) is int and 0 <= target < class_count:
                children.append(target)
            else:
                raise ValueError("future ordered child leaves the class table")
        if control.kind == "landmine" and children != [None, None]:
            raise ValueError("future Landmine row carries child edges")
        if control.kind == "fork" and any(child is None for child in children):
            raise ValueError("future Fork row lost an ordered child")
        if raw_rank is None:
            rank = None
        elif type(raw_rank) is int and raw_rank >= 0:
            rank = raw_rank
        else:
            raise ValueError("future rank must be a nonnegative integer or null")
        result.append(FutureClass(control, (children[0], children[1]), rank))
    return tuple(result)


__all__ = ["decode_class_map", "decode_class_rows"]
