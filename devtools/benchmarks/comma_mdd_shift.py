"""Compare Future shift traversals on exact boundary-return requests."""

from __future__ import annotations

import json
from collections.abc import Iterable
from hashlib import sha256
from math import lcm
from statistics import median
from time import perf_counter_ns
from typing import Literal, NamedTuple

from devtools.paths import isabelle_root, report_output
from devtools.verification.comma_semantic_future_artifact import (
    runtime_candidate_record_from_m204_data,
)
from number_compiler.sequences.comma.boundary_chart import PERIOD
from number_compiler.sequences.comma.boundary_quotient import (
    BoundaryState,
    construct_completed_return,
)
from number_compiler.sequences.comma.future_provider_codec import parse_future_candidate
from number_compiler.sequences.comma.future_source_mdd import (
    RADICES,
    FutureSourceMDD,
    SourceBranch,
    SourceLeaf,
    SourceNode,
)

Mode = Literal["split", "fused", "node-period"]
MODES: tuple[Mode, ...] = ("split", "fused", "node-period")
TRIALS = 5


class Request(NamedTuple):
    root: int
    shift: int


class ShiftTraversal:
    """Fresh, interning replay of the three construction routes."""

    def __init__(self, diagram: FutureSourceMDD) -> None:
        self.nodes = list(diagram.nodes)
        self.interned = {node: index for index, node in enumerate(self.nodes)}
        self.cache: dict[tuple[int, int, int], int] = {}
        self.periods: dict[int, int] = {}
        self.visits = 0

    def node_period(self, root: int) -> int:
        period = self.periods.get(root)
        if period is None:
            node = self.nodes[root]
            if isinstance(node, SourceLeaf):
                period = 1
            else:
                period = lcm(RADICES[node.axis], *map(self.node_period, node.children))
            self.periods[root] = period
        return period

    def visit(self, root: int, shift: int, delta: int, *, normalize: bool) -> int:
        if normalize:
            shift %= self.node_period(root)
        key = (root, shift, delta)
        cached = self.cache.get(key)
        if cached is not None:
            return cached
        self.visits += 1
        node = self.nodes[root]
        if isinstance(node, SourceLeaf):
            encoded: SourceNode = SourceLeaf(node.cid + delta)
        else:
            width = RADICES[node.axis]
            children = tuple(
                self.visit(
                    node.children[(slot + shift) % width],
                    shift,
                    delta,
                    normalize=normalize,
                )
                for slot in range(width)
            )
            encoded = SourceBranch(node.axis, children)
        result = self.interned.get(encoded)
        if result is None:
            result = len(self.nodes)
            self.interned[encoded] = result
            self.nodes.append(encoded)
        self.cache[key] = result
        return result

    def run(self, request: Request, mode: Mode) -> int:
        if mode == "split":
            encoded = self.visit(request.root, 0, 1, normalize=False)
            if request.shift == 0:
                return encoded
            return self.visit(encoded, request.shift, 0, normalize=False)
        return self.visit(
            request.root, request.shift, 1, normalize=mode == "node-period"
        )


def phase_value(
    nodes: list[SourceNode] | tuple[SourceNode, ...], root: int, phase: int
) -> int:
    """Evaluate directly in the original phase coordinate."""
    node = nodes[root]
    while isinstance(node, SourceBranch):
        node = nodes[node.children[phase % RADICES[node.axis]]]
    return node.cid


def requests_for(diagram: FutureSourceMDD) -> tuple[Request, ...]:
    """Derive the class and shift requests from exact returns on every source."""
    requests: dict[Request, None] = {}
    kinds: tuple[Literal["N", "Z"], ...] = ("N", "Z")
    for kind in kinds:
        for leading in range(2, 10):
            for phase in range(PERIOD):
                source = BoundaryState(kind, leading, phase)
                result = construct_completed_return(source, grouped_near=True)
                for child in result.ordered_children:
                    family = child.a - 2 + (8 if child.kind == "Z" else 0)
                    requests[Request(diagram.roots[family], result.exponent_delta)] = (
                        None
                    )
    return tuple(requests)


def candidate() -> FutureSourceMDD:
    directory = isabelle_root() / "families/comma/comma_semantic_future_instance"
    source = (directory / "semantic_future_m204_candidate_data.ML").read_text(
        encoding="utf-8"
    )
    graph = (directory / "semantic_future_m204_graph_data.ML").read_text(
        encoding="utf-8"
    )

    def ignore_work(_amount: int) -> None:
        pass

    record = runtime_candidate_record_from_m204_data(source, graph)
    return parse_future_candidate(record, charge_work=ignore_work).source_classes


def verify_outputs(
    diagram: FutureSourceMDD,
    requests: tuple[Request, ...],
    nodes: list[SourceNode],
    results: Iterable[int],
) -> str:
    digest = sha256()
    for request, root in zip(requests, results, strict=True):
        for phase in range(PERIOD):
            expected = (
                phase_value(diagram.nodes, request.root, phase + request.shift) + 1
            )
            value = phase_value(nodes, root, phase)
            if value != expected:
                raise AssertionError(f"wrong class for {request} at phase {phase}")
            digest.update(value.to_bytes(2, "big"))
    return digest.hexdigest()


def main() -> None:
    diagram = candidate()
    requests = requests_for(diagram)
    samples: dict[Mode, list[int]] = {mode: [] for mode in MODES}
    visits: dict[Mode, int] = {}
    checksums: dict[Mode, str] = {}
    for trial in range(TRIALS):
        order = MODES if trial % 2 == 0 else MODES[::-1]
        for mode in order:
            traversal = ShiftTraversal(diagram)
            start = perf_counter_ns()
            results = tuple(traversal.run(request, mode) for request in requests)
            samples[mode].append(perf_counter_ns() - start)
            if visits.setdefault(mode, traversal.visits) != traversal.visits:
                raise AssertionError("identical traversal executed different work")
            if trial == 0:
                checksums[mode] = verify_outputs(
                    diagram, requests, traversal.nodes, results
                )
    if len(set(checksums.values())) != 1:
        raise AssertionError("Future shift routes produced different class values")
    report = {
        "scope": "Python MDD construction model on source-derived Future requests",
        "requests": len(requests),
        "phase_checks_per_route": len(requests) * PERIOD,
        "checksum": checksums["fused"],
        "cold_visits": visits,
        "samples_ns": samples,
        "median_ns": {mode: median(times) for mode, times in samples.items()},
    }
    output = report_output("devtools.benchmarks.comma_mdd_shift", "comparison.json")
    output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(output)


if __name__ == "__main__":
    main()
