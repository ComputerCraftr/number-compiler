"""Fixed-point refinement of caller-supplied finite deterministic graphs.

Every successor must belong to the declared universe. None denotes a forbidden
port, never an unexplored frontier. Observations must contain the complete
consumer contract. This utility neither discovers a universe nor authenticates
that a supplied graph models an arithmetic execution.
"""

from __future__ import annotations

from collections.abc import Hashable, Sequence
from dataclasses import dataclass


def canonical_partition(signatures: tuple[object, ...]) -> tuple[int, ...]:
    ordered = sorted(set(signatures), key=repr)
    identities = {signature: index for index, signature in enumerate(ordered)}
    return tuple(identities[signature] for signature in signatures)


def class_members(
    class_ids: Sequence[int], classes: int
) -> tuple[tuple[int, ...], ...]:
    """Group state indices by a complete, densely numbered partition."""
    if type(classes) is not int or classes < 0:
        raise ValueError("finite observer class count must be nonnegative")
    groups: list[list[int]] = [[] for _ in range(classes)]
    for state, class_id in enumerate(class_ids):
        if type(class_id) is not int or not 0 <= class_id < classes:
            raise ValueError("finite observer class id leaves its partition")
        groups[class_id].append(state)
    if any(not group for group in groups):
        raise ValueError("finite observer partition contains an empty class")
    return tuple(tuple(group) for group in groups)


def map_partition_row(
    row: Sequence[int | None], class_ids: Sequence[int]
) -> tuple[int | None, ...]:
    """Map ordered state targets to their class ids, preserving forbidden slots."""
    mapped: list[int | None] = []
    for target in row:
        if target is None:
            mapped.append(None)
        elif type(target) is not int or not 0 <= target < len(class_ids):
            raise ValueError("finite observer target leaves its partition")
        else:
            mapped.append(class_ids[target])
    return tuple(mapped)


def partition_quotient_rows(
    rows: Sequence[Sequence[int | None]],
    class_ids: Sequence[int],
    classes: int,
) -> tuple[tuple[int | None, ...], ...]:
    """Build one mapped row per class, validating successor congruence."""
    if len(rows) != len(class_ids):
        raise ValueError("finite observer rows and classes must have equal size")
    members = class_members(class_ids, classes)
    mapped = tuple(map_partition_row(row, class_ids) for row in rows)
    quotient: list[tuple[int | None, ...]] = []
    for group in members:
        row = mapped[group[0]]
        if any(mapped[state] != row for state in group[1:]):
            raise ValueError("finite observer partition is not successor closed")
        quotient.append(row)
    return tuple(quotient)


def closed_partition_quotient_rows(
    rows: Sequence[Sequence[int | None]], class_ids: Sequence[int], classes: int
) -> tuple[tuple[int, ...], ...]:
    """Build quotient rows for a graph whose every ordered edge is admitted."""
    if any(target is None for row in rows for target in row):
        raise ValueError("closed finite observer graph contains a forbidden edge")
    quotient = partition_quotient_rows(rows, class_ids, classes)
    dense: list[tuple[int, ...]] = []
    for row in quotient:
        dense_row: list[int] = []
        for target in row:
            if target is None:
                raise AssertionError("closed quotient introduced a forbidden edge")
            dense_row.append(target)
        dense.append(tuple(dense_row))
    return tuple(dense)


def partition_equivalent(first: Sequence[Hashable], second: Sequence[Hashable]) -> bool:
    """Test equality of partitions in linear time, independent of label names."""
    if len(first) != len(second):
        return False
    forward: dict[Hashable, Hashable] = {}
    backward: dict[Hashable, Hashable] = {}
    for left, right in zip(first, second, strict=True):
        if forward.setdefault(left, right) != right:
            return False
        if backward.setdefault(right, left) != left:
            return False
    return True


@dataclass(frozen=True, slots=True)
class FiniteObserverMinimization:
    classes: int
    class_ids: tuple[int, ...]
    rounds: int


def minimize_finite_observer(
    successors: Sequence[Sequence[int | None]],
    outputs: Sequence[Hashable],
) -> FiniteObserverMinimization:
    """Greatest stable refinement of complete observations and admissibility.

    Ordered edge slots can include both next context and next residual. Both
    participate in every round. State sorts belong in the output labels when
    a graph includes more than one kind of state. No horizon cutoff is used.
    """
    rows = tuple(tuple(row) for row in successors)
    labels = tuple(outputs)
    size = len(rows)
    arity = len(rows[0]) if rows else 0
    if len(labels) != size or any(len(row) != arity for row in rows):
        raise ValueError("finite observer rows must have matching dimensions")
    if any(
        target is not None and (type(target) is not int or not 0 <= target < size)
        for row in rows
        for target in row
    ):
        raise ValueError("every admitted successor must be in the declared universe")
    initial: dict[Hashable, int] = {}
    classes = tuple(
        initial.setdefault((label, tuple(t is not None for t in row)), len(initial))
        for label, row in zip(labels, rows, strict=True)
    )
    rounds = 0
    while True:
        mapping: dict[Hashable, int] = {}
        refined = tuple(
            mapping.setdefault(
                (classes[state], tuple(None if t is None else classes[t] for t in row)),
                len(mapping),
            )
            for state, row in enumerate(rows)
        )
        rounds += 1
        if partition_equivalent(classes, refined):
            return FiniteObserverMinimization(len(mapping), refined, rounds)
        classes = refined
