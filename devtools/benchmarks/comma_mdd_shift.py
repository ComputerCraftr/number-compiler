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
        pending = [(root, False)]
        while pending:
            index, ready = pending.pop()
            if index in self.periods:
                continue
            node = self.nodes[index]
            if isinstance(node, SourceLeaf):
                self.periods[index] = 1
            elif ready:
                self.periods[index] = lcm(
                    RADICES[node.axis],
                    *(self.periods[child] for child in node.children),
                )
            else:
                pending.append((index, True))
                pending.extend((child, False) for child in reversed(node.children))
        return self.periods[root]

    def _shift_key(
        self, root: int, shift: int, delta: int, normalize: bool
    ) -> tuple[int, int, int]:
        return root, shift % self.node_period(root) if normalize else shift, delta

    def visit(self, root: int, shift: int, delta: int, *, normalize: bool) -> int:
        key = self._shift_key(root, shift, delta, normalize)
        pending: list[
            tuple[tuple[int, int, int], tuple[tuple[int, int, int], ...] | None]
        ] = [(key, None)]
        while pending:
            current, children = pending.pop()
            if current in self.cache:
                continue
            index, phase, increment = current
            node = self.nodes[index]
            if children is not None:
                assert isinstance(node, SourceBranch)
                encoded: SourceNode = SourceBranch(
                    node.axis, tuple(self.cache[child] for child in children)
                )
            else:
                self.visits += 1
                if isinstance(node, SourceLeaf):
                    encoded = SourceLeaf(node.cid + increment)
                else:
                    width = RADICES[node.axis]
                    children = tuple(
                        self._shift_key(
                            node.children[(slot + phase) % width],
                            phase,
                            increment,
                            normalize,
                        )
                        for slot in range(width)
                    )
                    pending.append((current, children))
                    pending.extend((child, None) for child in reversed(children))
                    continue
            result = self.interned.get(encoded)
            if result is None:
                result = len(self.nodes)
                self.interned[encoded] = result
                self.nodes.append(encoded)
            self.cache[current] = result
        return self.cache[key]

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
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
