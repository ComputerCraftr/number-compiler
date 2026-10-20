"""Graph-only helpers for finite transducer trim operations."""

from __future__ import annotations

from collections import deque
from collections.abc import Callable, Iterable, Mapping, MutableMapping, Sequence
from typing import Generic, Protocol, TypeVar


class _Arc(Protocol):
    @property
    def inp(self) -> int: ...

    @property
    def out(self) -> int: ...

    @property
    def dest(self) -> int: ...


T = TypeVar("T", bound=object)
E = TypeVar("E")


class DenseInterner(Generic[T]):
    """Stable dense IDs for finite graph carriers."""

    def __init__(self) -> None:
        self.values: list[T] = []
        self.index: dict[T, int] = {}

    def intern(self, value: T) -> int:
        old = self.index.get(value)
        if old is not None:
            return old
        result = len(self.values)
        self.index[value] = result
        self.values.append(value)
        return result


def determinize_subsets(
    alphabet: Sequence[int],
    startset: Iterable[int],
    transitions: Mapping[tuple[int, int], Iterable[int]],
) -> tuple[int, dict[tuple[int, int], int], tuple[frozenset[int], ...]]:
    """Build reachable subset IDs for an NFA without choosing a DFA wrapper."""
    subsets: list[frozenset[int]] = []
    identifiers: dict[frozenset[int], int] = {}

    def intern(states: Iterable[int]) -> int:
        frozen = frozenset(states)
        old = identifiers.get(frozen)
        if old is not None:
            return old
        result = len(subsets)
        identifiers[frozen] = result
        subsets.append(frozen)
        return result

    start = intern(startset)
    result: dict[tuple[int, int], int] = {}
    queue = deque([start])
    seen: set[int] = set()
    while queue:
        state = queue.popleft()
        if state in seen:
            continue
        seen.add(state)
        for symbol in alphabet:
            successors: set[int] = set()
            for source in subsets[state]:
                successors.update(transitions.get((source, symbol), ()))
            if not successors:
                continue
            destination = intern(successors)
            result[state, symbol] = destination
            if destination not in seen:
                queue.append(destination)
    return start, result, tuple(subsets)


def product_states(
    left: Sequence[int], right: Sequence[int]
) -> tuple[list[tuple[int, int]], tuple[int, ...], Callable[[tuple[int, int]], int]]:
    """Create a product state's dense carrier and its initial IDs."""
    interner: DenseInterner[tuple[int, int]] = DenseInterner()
    initials = tuple(
        interner.intern((first, second)) for first in left for second in right
    )
    return interner.values, initials, interner.intern


def append_reachable_edge(
    edges: MutableMapping[int, list[E]],
    source: int,
    edge: E,
    destination: int,
    seen: set[int],
    queue: deque[int],
) -> None:
    """Store one edge and schedule its destination for a finite graph walk."""
    edges.setdefault(source, []).append(edge)
    if destination not in seen:
        queue.append(destination)


def input_index(
    arcs: Mapping[int, Sequence[_Arc]],
) -> dict[int, dict[int, list[_Arc]]]:
    """Index outgoing arcs by source state and input symbol."""
    result: dict[int, dict[int, list[_Arc]]] = {state: {} for state in arcs}
    for state, outgoing in arcs.items():
        for arc in outgoing:
            result[state].setdefault(arc.inp, []).append(arc)
    return result


def compose_edges(
    initials: Sequence[int],
    pairs: Sequence[tuple[int, int]],
    left_arcs: Mapping[int, Sequence[_Arc]],
    right_index: Mapping[int, Mapping[int, Sequence[_Arc]]],
    intern: Callable[[tuple[int, int]], int],
) -> dict[int, list[tuple[int, int, int]]]:
    """Build reachable product edges as ``(input, output, destination)`` tuples."""
    edges: dict[int, list[tuple[int, int, int]]] = {}
    queue = deque(initials)
    seen: set[int] = set()
    while queue:
        state_id = queue.popleft()
        if state_id in seen:
            continue
        seen.add(state_id)
        left_state, right_state = pairs[state_id]
        for left_arc in left_arcs.get(left_state, ()):
            for right_arc in right_index.get(right_state, {}).get(left_arc.out, ()):
                destination = intern((left_arc.dest, right_arc.dest))
                edges.setdefault(state_id, []).append(
                    (left_arc.inp, right_arc.out, destination)
                )
                if destination not in seen:
                    queue.append(destination)
    return edges


def compose_arc_table(
    initials: Sequence[int],
    pairs: Sequence[tuple[int, int]],
    left_arcs: Mapping[int, Sequence[_Arc]],
    right_arcs: Mapping[int, Sequence[_Arc]],
    intern: Callable[[tuple[int, int]], int],
    make_arc: Callable[[tuple[int, int, int]], E],
) -> tuple[dict[int, dict[int, list[_Arc]]], dict[int, list[E]]]:
    """Index the right graph and materialize reachable product edges."""
    indexed = input_index(right_arcs)
    raw = compose_edges(initials, pairs, left_arcs, indexed, intern)
    return indexed, {
        state: [make_arc(edge) for edge in edges] for state, edges in raw.items()
    }


def compose_suffix_outputs(
    start_state: int,
    suffix: Sequence[int],
    right_index: Mapping[int, Mapping[int, Sequence[_Arc]]],
    right_finals: Mapping[int, tuple[int, ...]],
) -> set[tuple[int, ...]]:
    """Push a left final suffix through the indexed right transducer."""
    frontier: set[tuple[int, tuple[int, ...]]] = {(start_state, ())}
    for symbol in suffix:
        next_frontier: set[tuple[int, tuple[int, ...]]] = set()
        for state, output in frontier:
            for arc in right_index.get(state, {}).get(symbol, ()):
                next_frontier.add((arc.dest, output + (arc.out,)))
        frontier = next_frontier
    return {
        output + right_finals[state]
        for state, output in frontier
        if state in right_finals
    }


def compose_product_graph(
    left_initials: Sequence[int],
    right_initials: Sequence[int],
    left_arcs: Mapping[int, Sequence[_Arc]],
    right_arcs: Mapping[int, Sequence[_Arc]],
    make_arc: Callable[[tuple[int, int, int]], E],
) -> tuple[
    list[tuple[int, int]],
    tuple[int, ...],
    dict[int, dict[int, list[_Arc]]],
    dict[int, list[E]],
]:
    """Intern the reachable product and return its indexed composed graph."""
    pairs, initials, intern = product_states(left_initials, right_initials)
    indexed, arcs = compose_arc_table(
        initials, pairs, left_arcs, right_arcs, intern, make_arc
    )
    return pairs, initials, indexed, arcs


def quotient_graph(
    part: Mapping[int, int],
    representatives: Mapping[int, int],
    remap: Mapping[int, int],
    arcs: Mapping[int, Sequence[_Arc]],
    finals: Mapping[int, tuple[int, ...]],
    initials: Sequence[int],
    make_arc: Callable[[int, int, int], E],
) -> tuple[dict[int, tuple[E, ...]], dict[int, tuple[int, ...]], tuple[int, ...]]:
    """Build a dense transducer graph from a stable state partition."""
    quotient_arcs = {
        remap[class_id]: tuple(
            make_arc(inp, out, dest)
            for inp, out, dest in sorted(
                {
                    (arc.inp, arc.out, remap[part[arc.dest]])
                    for arc in arcs.get(state, ())
                }
            )
        )
        for class_id, state in representatives.items()
    }
    quotient_finals = {remap[part[state]]: output for state, output in finals.items()}
    quotient_initials = tuple(sorted({remap[part[state]] for state in initials}))
    return quotient_arcs, quotient_finals, quotient_initials


def trim_ids(
    initials: Sequence[int],
    arcs: Mapping[int, Sequence[_Arc]],
    finals: Mapping[int, object],
) -> dict[int, int]:
    """Return dense IDs for states reachable from initials and co-reachable to finals."""
    reachable = set(initials)
    queue = deque(initials)
    while queue:
        state = queue.popleft()
        for arc in arcs.get(state, ()):
            if arc.dest not in reachable:
                reachable.add(arc.dest)
                queue.append(arc.dest)
    reverse: dict[int, list[int]] = {}
    for state, outgoing in arcs.items():
        for arc in outgoing:
            reverse.setdefault(arc.dest, []).append(state)
    live = set(finals)
    queue = deque(live)
    while queue:
        state = queue.popleft()
        for predecessor in reverse.get(state, ()):
            if predecessor not in live:
                live.add(predecessor)
                queue.append(predecessor)
    return {state: index for index, state in enumerate(sorted(reachable & live))}
