"""Fixed-point refinement of caller-supplied finite deterministic graphs.

Every successor must belong to the declared universe. None denotes a forbidden
port, never an unexplored frontier. Observations must contain the complete
consumer contract. This utility neither discovers a universe nor authenticates
that a supplied graph models an arithmetic execution.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Hashable, Sequence


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
