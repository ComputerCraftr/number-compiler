"""Replay a frozen first-Entry bind trace without trusting its output root."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from statistics import median
from time import perf_counter_ns
from typing import NamedTuple

from devtools.benchmarks.comma_mdd_shift import TRIALS, phase_value
from devtools.paths import report_output
from number_compiler.arithmetic.contracts.input_validation import (
    is_object_list_instance,
    string_keyed_mapping,
)
from number_compiler.sequences.comma.boundary_chart import PERIOD
from number_compiler.sequences.comma.future_source_mdd import (
    MAX_NODES,
    RADICES,
    SourceBranch,
    SourceLeaf,
    SourceNode,
)

MappingRows = tuple[tuple[int, int], ...]


class BindKey(NamedTuple):
    source: int
    fallback: int
    mapping: MappingRows


class Trace(NamedTuple):
    nodes: tuple[SourceNode, ...]
    key: BindKey
    output: int


def naturals(value: object) -> tuple[int, ...]:
    if not is_object_list_instance(value) or any(
        type(item) is not int or item < 0 for item in value
    ):
        raise ValueError("bind trace requires a natural-number array")
    return tuple(item for item in value if type(item) is int)


def load_trace(path: Path) -> Trace:
    data: object = json.loads(path.read_text(encoding="utf-8"))
    record = string_keyed_mapping(data)
    if record is None:
        raise ValueError("bind trace must be an object")
    if naturals(record.get("radices")) != RADICES:
        raise ValueError("bind trace uses different CRT axes")
    rows = record.get("nodes")
    if not is_object_list_instance(rows) or not 0 < len(rows) <= MAX_NODES:
        raise ValueError("bind trace has invalid table size")
    nodes: list[SourceNode] = []
    for row in rows:
        if not is_object_list_instance(row):
            raise ValueError("bind trace node must be an array")
        if len(row) == 1:
            (payload,) = naturals(row)
            nodes.append(SourceLeaf(payload))
            continue
        if len(row) != 2 or type(row[0]) is not int or not 0 <= row[0] < len(RADICES):
            raise ValueError("bind trace branch has an invalid axis")
        axis = row[0]
        children = naturals(row[1])
        if len(children) != RADICES[axis] or any(
            child >= len(nodes)
            or (isinstance(node := nodes[child], SourceBranch) and node.axis <= axis)
            for child in children
        ):
            raise ValueError("bind trace branch is not topologically ordered")
        nodes.append(SourceBranch(axis, children))

    def root(value: object) -> int:
        if type(value) is not int or not 0 <= value < len(nodes):
            raise ValueError("bind trace root is outside its table")
        return value

    mapping = record.get("mapping")
    if not is_object_list_instance(mapping):
        raise ValueError("bind trace mapping must be an array")
    entries: list[tuple[int, int]] = []
    for pair in mapping:
        payload, target = naturals(pair)
        entries.append((payload, root(target)))
    if len(dict(entries)) != len(entries):
        raise ValueError("bind trace has duplicate mapping labels")
    key = BindKey(
        root(record.get("source")), root(record.get("fallback")), tuple(entries)
    )
    return Trace(tuple(nodes), key, root(record.get("output")))


class BindTraversal:
    """Count executed cofactors while independently rebuilding the ordered result."""

    def __init__(self, nodes: tuple[SourceNode, ...], *, selected: bool) -> None:
        self.nodes = list(nodes)
        self.interned = {node: index for index, node in enumerate(nodes)}
        self.selected = selected
        self.supports: dict[int, frozenset[int]] = {}
        self.binds: dict[BindKey, int] = {}
        self.cofactors = 0
        self.selected_rows = 0

    def support(self, root: int) -> frozenset[int]:
        pending = [(root, False)]
        while pending:
            index, ready = pending.pop()
            if index in self.supports:
                continue
            node = self.nodes[index]
            if isinstance(node, SourceLeaf):
                self.supports[index] = frozenset((node.cid,))
            elif ready:
                self.supports[index] = frozenset().union(
                    *(self.supports[child] for child in node.children)
                )
            else:
                pending.append((index, True))
                pending.extend((child, False) for child in reversed(node.children))
        return self.supports[root]

    def cofactor(self, root: int, axis: int, slot: int) -> int:
        self.cofactors += 1
        node = self.nodes[root]
        return (
            node.children[slot]
            if isinstance(node, SourceBranch) and node.axis == axis
            else root
        )

    def _restricted(self, key: BindKey) -> BindKey:
        support = self.support(key.source)
        return BindKey(
            key.source,
            key.fallback,
            tuple(row for row in key.mapping if row[0] in support),
        )

    def _branch(self, axis: int, children: tuple[int, ...]) -> int:
        if all(root == children[0] for root in children):
            return children[0]
        branch = SourceBranch(axis, children)
        result = self.interned.setdefault(branch, len(self.nodes))
        if result == len(self.nodes):
            self.nodes.append(branch)
        return result

    def bind(self, key: BindKey) -> int:
        key = self._restricted(key)
        pending: list[tuple[BindKey, int, tuple[BindKey, ...]]] = [(key, -1, ())]
        while pending:
            current, axis, child_keys = pending.pop()
            if current in self.binds:
                continue
            if axis >= 0:
                self.binds[current] = self._branch(
                    axis, tuple(self.binds[child] for child in child_keys)
                )
                continue
            route = dict(current.mapping)
            source = self.nodes[current.source]
            if isinstance(source, SourceLeaf):
                self.binds[current] = route.get(source.cid, current.fallback)
                continue
            roots = (current.fallback, *(target for _, target in current.mapping))
            axis = min(
                (
                    source.axis,
                    *(
                        node.axis
                        for root in roots
                        if isinstance(node := self.nodes[root], SourceBranch)
                    ),
                )
            )
            rows = tuple(
                self.cofactor(current.source, axis, slot)
                for slot in range(RADICES[axis])
            )
            sources = tuple(self.nodes[row] for row in rows)
            if self.selected and all(isinstance(node, SourceLeaf) for node in sources):
                children = tuple(
                    self.cofactor(route.get(node.cid, current.fallback), axis, slot)
                    for slot, node in enumerate(sources)
                    if isinstance(node, SourceLeaf)
                )
                self.selected_rows += len(children)
                self.binds[current] = self._branch(axis, children)
                continue
            child_keys = tuple(
                self._restricted(
                    BindKey(
                        row,
                        self.cofactor(current.fallback, axis, slot),
                        tuple(
                            (label, self.cofactor(target, axis, slot))
                            for label, target in current.mapping
                        ),
                    )
                )
                for slot, row in enumerate(rows)
            )
            pending.append((current, axis, child_keys))
            pending.extend((child, -1, ()) for child in reversed(child_keys))
        return self.binds[key]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("trace", type=Path)
    trace = load_trace(parser.parse_args().trace)
    mapping = dict(trace.key.mapping)
    expected = tuple(
        phase_value(
            trace.nodes,
            mapping.get(
                phase_value(trace.nodes, trace.key.source, phase), trace.key.fallback
            ),
            phase,
        )
        for phase in range(PERIOD)
    )
    if any(
        phase_value(trace.nodes, trace.output, phase) != value
        for phase, value in enumerate(expected)
    ):
        raise AssertionError("frozen output disagrees with the pointwise bind")
    samples: dict[bool, list[int]] = {False: [], True: []}
    work: dict[bool, tuple[int, int, int]] = {}
    for trial in range(TRIALS):
        for selected in (False, True) if trial % 2 == 0 else (True, False):
            replay = BindTraversal(trace.nodes, selected=selected)
            start = perf_counter_ns()
            result = replay.bind(trace.key)
            samples[selected].append(perf_counter_ns() - start)
            if any(
                phase_value(replay.nodes, result, phase) != value
                for phase, value in enumerate(expected)
            ):
                raise AssertionError("replayed bind disagrees with the pointwise bind")
            counts = (replay.cofactors, len(replay.binds), replay.selected_rows)
            if work.setdefault(selected, counts) != counts:
                raise AssertionError("identical bind replay executed different work")
    result_report = {
        mode: {
            "cofactors": work[selected][0],
            "cold_bind_keys": work[selected][1],
            "selected_leaf_rows": work[selected][2],
            "samples_ns": samples[selected],
            "median_ns": median(samples[selected]),
        }
        for selected, mode in ((False, "eager"), (True, "selected"))
    }
    output = report_output("devtools.benchmarks.comma_mdd_bind", "comparison.json")
    output.write_text(json.dumps(result_report, indent=2) + "\n", encoding="utf-8")
    print(output)


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
