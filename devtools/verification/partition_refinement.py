"""Small finite partition refinement shared by verification experiments."""

from __future__ import annotations

from collections.abc import Callable, Hashable, Iterable


def parent_split_count(parent: Iterable[int], child: Iterable[int]) -> int:
    """Count parent blocks that refine into more than one child block."""
    children: dict[int, set[int]] = {}
    for parent_id, child_id in zip(parent, child, strict=True):
        children.setdefault(parent_id, set()).add(child_id)
    return sum(len(values) > 1 for values in children.values())


def stable_partition(
    states: Iterable[int],
    initial_key: Callable[[int], Hashable],
    signature: Callable[[int, dict[int, int]], Hashable],
) -> dict[int, int]:
    """Refine finite states until the signature partition stops changing."""
    ordered = tuple(states)
    classes: dict[Hashable, int] = {}
    part: dict[int, int] = {}
    for state in ordered:
        key = initial_key(state)
        classes.setdefault(key, len(classes))
        part[state] = classes[key]
    while True:
        classes = {}
        new: dict[int, int] = {}
        for state in ordered:
            key = signature(state, part)
            classes.setdefault(key, len(classes))
            new[state] = classes[key]
        if new == part:
            return part
        part = new


def partition_representatives(
    part: dict[int, int],
) -> tuple[dict[int, int], dict[int, int]]:
    """Return one state per class and a dense class-number remapping."""
    representatives: dict[int, int] = {}
    for state, class_id in part.items():
        representatives.setdefault(class_id, state)
    remap = {class_id: index for index, class_id in enumerate(sorted(representatives))}
    return representatives, remap
