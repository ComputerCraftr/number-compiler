"""Bounded snapshots for canonical JSON-shaped Python values."""

from __future__ import annotations

from collections.abc import Callable, Iterator, Mapping
from types import MappingProxyType
from typing import cast

WorkCharger = Callable[[int], None]
NodeReserver = Callable[[int], None]
_JSON_SHORT_ESCAPES = frozenset((8, 9, 10, 12, 13))


def snapshot_canonical_json(
    record: Mapping[str, object],
    *,
    max_bytes: int,
    max_depth: int,
    max_nodes: int,
    charge_work: WorkCharger,
    reserve_nodes: NodeReserver | None = None,
) -> dict[str, object]:
    """Make a bounded builtin-dict snapshot while checking its JSON shape.

    Only builtin JSON containers are copied, with a read-only mapping allowed
    at the root. Work is charged in cumulative node, character, and encoded-byte
    chunks before traversal. Optional node reservations are requested before
    creating each output container and its immediate child slots. Integer
    conversion is charged from a safe decimal-size upper bound.
    """
    if type(record) not in (dict, MappingProxyType):
        raise TypeError("JSON snapshot requires an object mapping")
    if type(max_bytes) is not int or max_bytes <= 0:
        raise ValueError("JSON snapshot byte limit must be positive")
    if type(max_depth) is not int or max_depth < 0:
        raise ValueError("JSON snapshot depth limit must be nonnegative")
    if type(max_nodes) is not int or max_nodes <= 0:
        raise ValueError("JSON snapshot node limit must be positive")

    charged_units = 0

    def charge_progress(
        *, visited_nodes: int = 0, scanned_characters: int = 0, json_bytes: int = 1
    ) -> None:
        nonlocal charged_units
        target = max(
            1,
            (visited_nodes + 4095) // 4096,
            (scanned_characters + 65_535) // 65_536,
            (json_bytes + 65_535) // 65_536,
        )
        if target > charged_units:
            amount = target - charged_units
            if not callable(charge_work):
                raise TypeError("JSON snapshot requires a work charger")
            charge_work(amount)
            charged_units = target

    charge_progress()
    size = 1  # Canonical JSON newline.
    visited = 0

    def add_size(current: int, amount: int) -> int:
        updated = current + amount
        charge_progress(json_bytes=updated)
        if updated > max_bytes:
            raise ValueError("JSON value exceeds the bounded JSON size")
        return updated

    scanned_characters = 0

    def string_size(value: str, *, current_size: int, visited_nodes: int) -> int:
        nonlocal scanned_characters
        size = 2  # JSON quotes.
        if len(value) > max_bytes - current_size - size:
            raise ValueError("JSON value exceeds the bounded JSON size")

        offset = 0
        while offset < len(value):
            chunk_end = min(offset + 65_536, len(value))
            scanned = scanned_characters + chunk_end - offset
            charge_progress(
                visited_nodes=visited_nodes,
                scanned_characters=scanned,
                json_bytes=current_size + size,
            )
            for index in range(offset, chunk_end):
                codepoint = ord(value[index])
                if codepoint in (34, 92):
                    size += 2
                elif codepoint < 0x20:
                    size += 2 if codepoint in _JSON_SHORT_ESCAPES else 6
                elif codepoint < 0x80:
                    size += 1
                elif codepoint <= 0xFFFF:
                    size += 6
                else:
                    size += 12
            charge_progress(
                visited_nodes=visited_nodes,
                scanned_characters=scanned,
                json_bytes=current_size + size,
            )
            if current_size + size > max_bytes:
                raise ValueError("JSON value exceeds the bounded JSON size")
            offset = chunk_end
            scanned_characters = scanned
        return size

    def visit_node(depth: int) -> int:
        nonlocal visited
        next_visited = visited + 1
        charge_progress(
            visited_nodes=next_visited,
            scanned_characters=scanned_characters,
            json_bytes=size,
        )
        if next_visited > max_nodes:
            raise ValueError("JSON value exceeds its bounded node count")
        if depth > max_depth:
            raise ValueError("JSON value nesting exceeds its bound")
        visited = next_visited
        return visited

    def reserve_container_and_slots(count: int) -> None:
        if reserve_nodes is None:
            return
        if not callable(reserve_nodes):
            raise TypeError("JSON snapshot node reserver must be callable")
        reserve_nodes(count)

    def assign(parent: object, slot: object, value: object) -> None:
        if parent is root_holder:
            root_holder[0] = value
        elif type(parent) is list:
            cast(list[object], parent).append(value)
        elif type(parent) is dict:
            if type(slot) is not str:
                raise TypeError("JSON snapshot object slot must be a string key")
            cast(dict[str, object], parent)[slot] = value
        else:
            raise TypeError("JSON snapshot has an invalid internal destination")

    # The one-slot root holder is part of the bounded transient snapshot.
    reserve_container_and_slots(2)
    # Frames are (kind, source, destination, slot, depth, cursor, count).
    root_holder: list[object] = [None]
    stack: list[tuple[str, object, object, object, int, int, int]] = [
        ("value", record, root_holder, None, 0, 0, 0)
    ]
    while stack:
        frame_kind, value, destination, slot, depth, cursor, count = stack.pop()

        if frame_kind == "list":
            source_list = cast(list[object], value)
            target_list = cast(list[object], destination)
            if cursor >= count:
                continue
            try:
                child = source_list[cursor]
            except IndexError as exc:
                raise ValueError("JSON list changed during bounded snapshot") from exc
            stack.append(
                ("list", source_list, target_list, None, depth, cursor + 1, count)
            )
            stack.append(("value", child, target_list, None, depth, 0, 0))
            continue

        if frame_kind == "dict":
            iterator = cast(Iterator[tuple[object, object]], value)
            copied_dict = cast(dict[str, object], destination)
            if cursor <= 0:
                continue
            try:
                key, child = next(iterator)
            except StopIteration as exc:
                raise ValueError("JSON object changed during bounded snapshot") from exc
            except RuntimeError as exc:
                raise ValueError("JSON object changed during bounded snapshot") from exc
            if type(key) is not str:
                raise TypeError("JSON object keys must be strings")
            key_node = visit_node(depth)
            size = add_size(
                size,
                string_size(
                    key,
                    current_size=size,
                    visited_nodes=key_node,
                ),
            )
            stack.append(("dict", iterator, copied_dict, None, depth, cursor - 1, 0))
            stack.append(("value", child, copied_dict, key, depth, 0, 0))
            continue

        node = visit_node(depth)
        if value is None:
            size = add_size(size, 4)
            assign(destination, slot, None)
        elif type(value) is bool:
            size = add_size(size, 4 if value else 5)
            assign(destination, slot, value)
        elif type(value) is int:
            # log10(2) exceeds 301029/1000000, giving a safe lower bound for
            # early rejection and a safe upper bound for conversion charging.
            if max(0, value.bit_length() - 1) * 301029 // 1_000_000 >= max_bytes:
                raise ValueError("JSON integer exceeds the bounded JSON size")
            digit_upper_bound = (
                value.bit_length() * 30103 // 100_000 + 1 + (1 if value < 0 else 0)
            )
            charge_progress(
                visited_nodes=node,
                scanned_characters=scanned_characters,
                json_bytes=size + digit_upper_bound,
            )
            try:
                number_size = len(str(value))
            except ValueError as exc:
                raise ValueError("JSON integer exceeds the bounded JSON size") from exc
            size = add_size(size, number_size)
            assign(destination, slot, value)
        elif type(value) is str:
            size = add_size(
                size,
                string_size(
                    value,
                    current_size=size,
                    visited_nodes=node,
                ),
            )
            assign(destination, slot, value)
        elif type(value) is list:
            child_count = len(value)
            if node + child_count > max_nodes:
                raise ValueError("JSON value exceeds its bounded node count")
            size = add_size(size, 2 + max(0, child_count - 1))
            reserve_container_and_slots(1 + child_count)
            copied_list: list[object] = []
            assign(destination, slot, copied_list)
            stack.append(("list", value, copied_list, None, depth + 1, 0, child_count))
        elif type(value) is dict or (depth == 0 and type(value) is MappingProxyType):
            child_count = len(value)
            if node + 2 * child_count > max_nodes:
                raise ValueError("JSON value exceeds its bounded node count")
            size = add_size(
                size,
                2 + 2 * child_count + max(0, child_count - 1),
            )
            reserve_container_and_slots(1 + 2 * child_count)
            copied_dict = {}
            assign(destination, slot, copied_dict)
            try:
                iterator = iter(value.items())
            except RuntimeError as exc:
                raise ValueError("JSON object changed during bounded snapshot") from exc
            stack.append(
                ("dict", iterator, copied_dict, None, depth + 1, child_count, 0)
            )
        else:
            raise TypeError("JSON value contains a non-JSON object")

    charge_progress(
        visited_nodes=visited,
        scanned_characters=scanned_characters,
        json_bytes=size,
    )
    snapshot = root_holder[0] if root_holder else None
    if type(snapshot) is not dict:
        raise TypeError("JSON snapshot root must be an object")
    return cast(dict[str, object], snapshot)
