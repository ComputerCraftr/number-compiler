"""Measured work performed by source-restricted Mahler center relations."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from enum import StrEnum

from number_compiler.arithmetic.fields.boolean_transfer import (
    BooleanSparseComposition,
)


class MahlerCenterWorkEvent(StrEnum):
    """Completed work units emitted while a center transfer is being built."""

    POINTED_SUCCESSOR_STEP = "pointed-successor-step"
    CANDIDATE_TRANSITION_VISIT = "candidate-transition-visit"
    SPARSE_INTERMEDIATE_EDGE_VISIT = "sparse-intermediate-edge-visit"
    SPARSE_COMPOSITION = "sparse-composition"
    CANONICAL_ROW_MATERIALIZATION = "canonical-row-materialization"


MahlerCenterWorkSink = Callable[[MahlerCenterWorkEvent, int], None]


@dataclass(frozen=True, slots=True)
class MahlerCenterRelationWork:
    """Counters owned by the finite center-relation producer.

    These count operations at their execution sites. ``full_row_products_avoided``
    counts cold relation steps handled by sparse composition instead of the old
    canonical 100-row product; it is not inferred from a temporal horizon in a
    metrics adapter.
    """

    candidate_transitions_evaluated: int = 0
    full_driver_matrices_avoided: int = 0
    sparse_step_rows_materialized: int = 0
    sparse_edges_emitted: int = 0
    sparse_intermediate_edges_visited: int = 0
    sparse_row_joins: int = 0
    sparse_joined_target_edges: int = 0
    sparse_composed_edges: int = 0
    sparse_compositions: int = 0
    full_row_products_avoided: int = 0
    full_row_products_performed: int = 0
    canonical_rows_materialized: int = 0

    def __post_init__(self) -> None:
        values = (
            self.candidate_transitions_evaluated,
            self.full_driver_matrices_avoided,
            self.sparse_step_rows_materialized,
            self.sparse_edges_emitted,
            self.sparse_intermediate_edges_visited,
            self.sparse_row_joins,
            self.sparse_joined_target_edges,
            self.sparse_composed_edges,
            self.sparse_compositions,
            self.full_row_products_avoided,
            self.full_row_products_performed,
            self.canonical_rows_materialized,
        )
        for value in values:
            if type(value) is not int or value < 0:
                raise ValueError(
                    "Mahler relation work values must be exact nonnegative integers"
                )

    def then(
        self,
        other: MahlerCenterRelationWork,
        composition: BooleanSparseComposition[int],
        *,
        canonical_rows_materialized: int,
    ) -> MahlerCenterRelationWork:
        """Add adjacent work and account for the sparse product just performed."""
        if type(other) is not MahlerCenterRelationWork:
            raise TypeError("Mahler relation work requires its matching record")
        if type(composition) is not BooleanSparseComposition:
            raise TypeError("Mahler relation composition requires measured sparse work")
        if (
            type(canonical_rows_materialized) is not int
            or canonical_rows_materialized < 0
        ):
            raise ValueError("canonical row materialization count is invalid")
        return MahlerCenterRelationWork(
            candidate_transitions_evaluated=(
                self.candidate_transitions_evaluated
                + other.candidate_transitions_evaluated
            ),
            full_driver_matrices_avoided=(
                self.full_driver_matrices_avoided + other.full_driver_matrices_avoided
            ),
            sparse_step_rows_materialized=(
                self.sparse_step_rows_materialized + other.sparse_step_rows_materialized
            ),
            sparse_edges_emitted=self.sparse_edges_emitted + other.sparse_edges_emitted,
            sparse_intermediate_edges_visited=(
                self.sparse_intermediate_edges_visited
                + other.sparse_intermediate_edges_visited
                + composition.intermediate_edges_visited
            ),
            sparse_row_joins=(
                self.sparse_row_joins + other.sparse_row_joins + composition.row_joins
            ),
            sparse_joined_target_edges=(
                self.sparse_joined_target_edges
                + other.sparse_joined_target_edges
                + composition.joined_target_edges
            ),
            sparse_composed_edges=(
                self.sparse_composed_edges
                + other.sparse_composed_edges
                + composition.result_edges
            ),
            sparse_compositions=(
                self.sparse_compositions + other.sparse_compositions + 1
            ),
            full_row_products_avoided=(
                self.full_row_products_avoided + other.full_row_products_avoided + 1
            ),
            full_row_products_performed=(
                self.full_row_products_performed + other.full_row_products_performed
            ),
            canonical_rows_materialized=(
                self.canonical_rows_materialized
                + other.canonical_rows_materialized
                + canonical_rows_materialized
            ),
        )

    def packet(self) -> dict[str, int]:
        """Return a read-only snapshot of work already charged by the owner."""
        return {
            "candidate_transitions_evaluated": self.candidate_transitions_evaluated,
            "full_driver_matrices_avoided": self.full_driver_matrices_avoided,
            "sparse_step_rows_materialized": self.sparse_step_rows_materialized,
            "sparse_edges_emitted": self.sparse_edges_emitted,
            "sparse_intermediate_edges_visited": (
                self.sparse_intermediate_edges_visited
            ),
            "sparse_row_joins": self.sparse_row_joins,
            "sparse_joined_target_edges": self.sparse_joined_target_edges,
            "sparse_composed_edges": self.sparse_composed_edges,
            "sparse_compositions": self.sparse_compositions,
            "full_row_products_avoided": self.full_row_products_avoided,
            "full_row_products_performed": self.full_row_products_performed,
            "canonical_rows_materialized": self.canonical_rows_materialized,
        }


__all__ = (
    "MahlerCenterRelationWork",
    "MahlerCenterWorkEvent",
    "MahlerCenterWorkSink",
)
