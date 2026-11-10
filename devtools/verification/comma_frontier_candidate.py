"""Untrusted Continue-frontier input and independent one-step differential audit.

This reader never issues a proof or a production action. In particular, an empty
24th preimage does not authenticate its input transition diagram. The bounded
chart teacher below checks that separate obligation as executable evidence only.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path

from devtools.runs import run_reported
from devtools.verification.comma_b1_quotient import B1State, observe_b1
from number_compiler.arithmetic.contracts.input_validation import (
    is_object_list,
    require_integer,
    string_keyed_mapping,
)
from number_compiler.sequences.comma.boundary_chart import PERIOD

RADICES = (3, 4, 11, 7)
CLASS_COUNT = 46
ENDPOINTS = ((299, 33), (66, 10), (298, 12), (67, 32), (68, 1))


@dataclass(frozen=True)
class Terminal:
    target: int


@dataclass(frozen=True)
class Branch:
    axis: int
    children: tuple[int, ...]


Node = Terminal | Branch


def _items(value: object) -> list[object]:
    if not is_object_list(value):
        raise ValueError("candidate field must be a JSON array")
    return value


def _integers(value: object, lower: int, upper: int) -> tuple[int, ...]:
    return tuple(
        require_integer(item, "candidate integer", lower, upper)
        for item in _items(value)
    )


def _nodes(value: object) -> tuple[Node, ...]:
    nodes: list[Node] = []
    unique: set[Node] = set()
    for raw in _items(value):
        row = _items(raw)
        if len(row) != 2:
            raise ValueError("candidate node must contain an axis and payload")
        axis = require_integer(row[0], "axis", 0, len(RADICES))
        node: Node
        if axis == len(RADICES):
            node = Terminal(require_integer(row[1], "target", -1, CLASS_COUNT - 1))
        else:
            children = _integers(row[1], 0, len(nodes) - 1)
            if len(children) != RADICES[axis]:
                raise ValueError("candidate branch arity differs from its CRT axis")
            if len(set(children)) == 1:
                raise ValueError("candidate contains an unreduced branch")
            for child_id in children:
                child = nodes[child_id]
                if isinstance(child, Branch) and child.axis <= axis:
                    raise ValueError("candidate axes must increase along edges")
            node = Branch(axis, children)
        if node in unique:
            raise ValueError("candidate contains a duplicate node")
        unique.add(node)
        nodes.append(node)
    return tuple(nodes)


@dataclass(frozen=True)
class FrontierCandidate:
    """Local node indices are data references, never semantic authority."""

    nodes: tuple[Node, ...]
    roots: tuple[int, ...]

    @classmethod
    def from_document(cls, value: object) -> FrontierCandidate:
        document = string_keyed_mapping(value)
        if document is None:
            raise ValueError("candidate must be a JSON object")
        if require_integer(document.get("rounds"), "rounds") != 24:
            raise ValueError("candidate must describe the 24-step obligation")
        endpoints = tuple(
            _integers(row, 0, PERIOD - 1)
            for row in _items(document.get("bad_terminal_endpoints"))
        )
        if len(endpoints) != len(ENDPOINTS) or set(endpoints) != set(ENDPOINTS):
            raise ValueError("candidate endpoint obligation differs")
        nodes = _nodes(document.get("one_step_nodes"))
        roots = _integers(document.get("one_step_roots"), 0, len(nodes) - 1)
        if len(roots) != CLASS_COUNT:
            raise ValueError("candidate must have one root per class")
        reached: set[int] = set()
        pending = list(roots)
        while pending:
            current = pending.pop()
            if current in reached:
                continue
            reached.add(current)
            node = nodes[current]
            if isinstance(node, Branch):
                pending.extend(node.children)
        if len(reached) != len(nodes):
            raise ValueError("candidate contains unreachable nodes")
        return cls(nodes, roots)

    def target(self, state: B1State) -> int | None:
        """Evaluate the external phase in this document's explicit CRT order."""
        fiber = require_integer(state.fiber, "fiber", 0, CLASS_COUNT - 1)
        phase = require_integer(state.phase, "phase", 0, PERIOD - 1)
        node = self.nodes[self.roots[fiber]]
        while isinstance(node, Branch):
            node = self.nodes[node.children[phase % RADICES[node.axis]]]
        return None if node.target == -1 else node.target


@dataclass(frozen=True)
class TransitionMismatch:
    source: B1State
    expected: int | None
    actual: int | None


@dataclass(frozen=True)
class DifferentialResult:
    checked_occurrences: int
    mismatches: int
    first_mismatch: TransitionMismatch | None


def audit_one_step(candidate: FrontierCandidate) -> DifferentialResult:
    """Stream the finite oracle comparison; retain no phase-signature table."""
    mismatches = 0
    first = None
    for fiber in range(CLASS_COUNT):
        for phase in range(PERIOD):
            state = B1State(fiber, phase)
            successor = observe_b1(state).successor
            expected = None if successor is None else successor.fiber
            actual = candidate.target(state)
            if expected != actual:
                mismatches += 1
                if first is None:
                    first = TransitionMismatch(state, expected, actual)
    return DifferentialResult(CLASS_COUNT * PERIOD, mismatches, first)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidate", type=Path)
    arguments = parser.parse_args()
    path: Path = arguments.candidate
    document: object = json.loads(path.read_text())
    candidate = FrontierCandidate.from_document(document)
    result = audit_one_step(candidate)
    print(json.dumps({"kernel_accepted": False, **asdict(result)}, indent=2))
    return int(result.mismatches != 0)


if __name__ == "__main__":
    raise SystemExit(run_reported(main))
