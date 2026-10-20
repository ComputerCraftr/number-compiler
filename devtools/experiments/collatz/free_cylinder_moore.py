"""Exact Moore projections of bounded Collatz source-cylinder relations.

The free-cylinder constructor deliberately keeps a rich audit terminal containing
endpoint transport, physical clock and ordered physical support.  Those are not
all semantic identity for every consumer.  This module derives *consumer-
relative* quotients by relabeling those terminals and reducing the same exact
ordered source-bit decision DAG.

The resulting DAG is the finite derivative/Cayley residual graph for the chosen
observation: a node is identified by its current observation and its ordered
zero/one continuations.  No source Cartesian table and no chronological Collatz
tree is materialized.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

from devtools.experiments.collatz.free_cylinder_consumers import ConsumerAction
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.functions.decision import (
    DecisionStructureMetrics,
    MultiTerminalDecisionArena,
)
from number_compiler.arithmetic.functions.finite_observer import (
    minimize_finite_observer,
)

CollatzMooreObservation = Literal["endpoint", "endpoint-clock", "support"]


def _observation_label(value: object, observation: CollatzMooreObservation) -> object:
    if value is None:
        return None
    if type(value) is not ConsumerAction:
        raise TypeError("Collatz Moore projection requires consumer-action terminals")
    if observation == "endpoint":
        return value.output
    if observation == "endpoint-clock":
        return value.output, value.event_weight, value.physical_ticks
    if observation == "support":
        return value
    raise ValueError(f"unknown Collatz Moore observation: {observation!r}")


@dataclass(frozen=True, slots=True)
class CollatzSpatialMooreCertificate:
    """Exact Moore minimization of the low-to-high source-prefix machine."""

    reachable_states: int
    classes: int
    rounds: int

    @property
    def merged_states(self) -> int:
        return self.reachable_states - self.classes


@dataclass(frozen=True, slots=True)
class CollatzSpatialMooreProjection:
    """Canonical ordered-source Moore quotient for one consumer observation."""

    observation: CollatzMooreObservation
    arena: MultiTerminalDecisionArena
    root: int

    def __post_init__(self) -> None:
        if any(domain != 2 for domain in self.arena.domains):
            raise ValueError("Collatz Moore derivatives require binary coordinates")
        if type(self.root) is not int or not 0 <= self.root < self.arena.node_count:
            raise ValueError("Moore projection requires an existing exact root")

    @property
    def metrics(self) -> DecisionStructureMetrics:
        return self.arena.structural_metrics(self.root)

    @property
    def dag_nodes(self) -> int:
        metrics = self.metrics
        return metrics.terminals + metrics.internal_nodes

    def certificate(self, *, max_states: int = 65536) -> CollatzSpatialMooreCertificate:
        """Minimize all reachable binary derivatives of this projected relation.

        States are ``(consumed_source_bits, canonical cofactor root)`` pairs.
        This makes skipped don't-care coordinates explicit while still sharing
        equal derivatives.  Terminal observations are visible only after the
        complete finite source word has been consumed.
        """
        if type(max_states) is not int or max_states < 1:
            raise ValueError("Moore state budget must be a positive integer")
        start = (0, self.root)
        ids: dict[tuple[int, int], int] = {start: 0}
        queue: list[tuple[int, int]] = [start]
        rows: list[tuple[int | None, int | None]] = []
        outputs: list[object] = []
        cursor = 0
        while cursor < len(queue):
            depth, root = queue[cursor]
            cursor += 1
            if depth == self.arena.arity:
                rows.append((None, None))
                outputs.append(("terminal", self.arena.terminal_value(root)))
                continue
            successors: list[int] = []
            for bit in (0, 1):
                child_root = self.arena.cofactor(root, {self.arena.order[depth]: bit})
                child = (depth + 1, child_root)
                child_id = ids.get(child)
                if child_id is None:
                    if len(ids) >= max_states:
                        raise BlockContextBudgetExceeded(
                            "Moore derivative state budget"
                        )
                    child_id = len(ids)
                    ids[child] = child_id
                    queue.append(child)
                successors.append(child_id)
            rows.append((successors[0], successors[1]))
            outputs.append(("pending",))
        result = minimize_finite_observer(rows, outputs)
        return CollatzSpatialMooreCertificate(
            len(queue),
            result.classes,
            result.rounds,
        )

    def evaluate(self, source: int) -> object:
        """Evaluate the projected terminal on the represented finite source word."""
        if type(source) is not int or source < 0:
            raise ValueError("projected Collatz source must be a nonnegative integer")
        if source.bit_length() > self.arena.arity:
            raise ValueError("source exceeds projected Collatz source precision")
        coordinates = tuple((source >> bit) & 1 for bit in range(self.arena.arity))
        return self.arena.evaluate(self.root, coordinates)

    def derivative(self, prefix: int, width: int) -> tuple[int, int]:
        """Return ``(consumed_bits, root)`` for one low-to-high source derivative."""
        if type(prefix) is not int or type(width) is not int:
            raise TypeError("Collatz derivative prefix requires exact integers")
        if width < 0 or width > self.arena.arity or prefix < 0 or prefix >= 1 << width:
            raise ValueError((prefix, width))
        assignments = {
            self.arena.order[bit]: (prefix >> bit) & 1 for bit in range(width)
        }
        return width, self.arena.cofactor(self.root, assignments)


def project_collatz_spatial_moore(
    arena: MultiTerminalDecisionArena,
    root: int,
    observation: CollatzMooreObservation,
) -> CollatzSpatialMooreProjection:
    """Relabel one exact cylinder decision relation and reduce to Moore normal form."""
    if observation not in ("endpoint", "endpoint-clock", "support"):
        raise ValueError(f"unknown Collatz Moore observation: {observation!r}")
    projected, projected_root = arena.relabel_terminals(
        root,
        lambda value: _observation_label(value, observation),
    )
    return CollatzSpatialMooreProjection(observation, projected, projected_root)


__all__ = [
    "CollatzMooreObservation",
    "CollatzSpatialMooreCertificate",
    "CollatzSpatialMooreProjection",
    "project_collatz_spatial_moore",
]
