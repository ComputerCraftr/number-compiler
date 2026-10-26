"""Source-conditioned sparse construction for Mahler center transfers.

This module constructs the necessary center relation from adjacent admitted
source fibers. It does not issue source authority: callers must supply the
already authenticated candidate fibers and bilateral port certificates.
"""

from __future__ import annotations

from number_compiler.arithmetic.fields.boolean_transfer import (
    BooleanSparseRows,
    BooleanStateSpace,
    boolean_sparse_rows_then,
)
from number_compiler.sequences.antihydra.mahler_center_algebra import (
    STATES,
    center_next,
)
from number_compiler.sequences.antihydra.mahler_center_relation_work import (
    MahlerCenterRelationWork,
    MahlerCenterWorkEvent,
    MahlerCenterWorkSink,
)
from number_compiler.sequences.antihydra.mahler_low_border_carry import (
    MahlerLowBorderCarryCertificate,
)
from number_compiler.sequences.antihydra.mahler_port_puncture import (
    MahlerCenterPortPuncture,
)


def compose_source_conditional_relation(
    sources: tuple[int, ...],
    positions: tuple[int, ...],
    candidate_sets: tuple[set[int], ...],
    low_ports: tuple[MahlerLowBorderCarryCertificate | None, ...],
    port_tables: tuple[dict[int, MahlerCenterPortPuncture], ...],
    *,
    state_space: BooleanStateSpace[int],
    work_sink: MahlerCenterWorkSink | None = None,
) -> tuple[tuple[int, ...], MahlerCenterRelationWork]:
    """Compose adjacent source-fiber transitions without dense row products.

    Each input fiber and port table is prepared and authenticated by the
    source owner. The returned relation is only the conditional 100-state
    projection; exact integer witnesses remain with the source transfer.
    """
    if len(sources) < 2:
        raise ValueError("source-conditioned relation needs an adjacent source edge")
    if not (
        len(sources) == len(positions) == len(candidate_sets)
        and len(low_ports) == len(port_tables) == len(sources) - 1
    ):
        raise ValueError("source-conditioned relation inputs are misaligned")

    reachable_rows: dict[int, int] = {}
    candidate_transitions_evaluated = 0
    full_driver_matrices_avoided = 0
    sparse_step_rows_materialized = 0
    sparse_edges_emitted = 0
    sparse_intermediate_edges_visited = 0
    sparse_row_joins = 0
    sparse_joined_target_edges = 0
    sparse_composed_edges = 0
    sparse_compositions = 0
    full_row_products_avoided = 0

    for index in range(len(sources) - 1):
        current_s = positions[index]
        next_s = positions[index + 1]
        step_rows: dict[int, int] = {}
        for candidate in candidate_sets[index]:
            candidate_transitions_evaluated += 1
            if work_sink is not None:
                work_sink(MahlerCenterWorkEvent.CANDIDATE_TRANSITION_VISIT, 1)
            full_driver_matrices_avoided += 1
            center = (candidate // 10**current_s) % 100
            low_base = 10**current_s
            upper = candidate // (100 * low_base)
            low_port = low_ports[index]
            if low_port is None:
                lower = candidate % low_base
                carry = (3 * lower + (candidate & 1)) // low_base
                next_fixed = center_next(center, carry, upper & 1)
                next_source = (3 * candidate + (candidate & 1)) // 2
            else:
                if (candidate & 1) != (low_port.source & 1):
                    raise ArithmeticError(
                        "candidate changed its authenticated low inlet"
                    )
                port = port_tables[index].get(candidate)
                if port is None:
                    raise ArithmeticError("candidate has no bilateral port witness")
                carry = low_port.actual_carry
                next_fixed, outgoing, next_upper = low_port.upper_transfer(
                    center, upper
                )
                if (
                    port.lower_carry != carry
                    or port.center_upper_carry != outgoing
                    or port.upper_division_inlet != ((upper + outgoing) & 1)
                    or port.fixed_next_center != next_fixed
                    or port.next_source // (100 * low_base) != next_upper
                ):
                    raise ArithmeticError("punctured ports disagree with matrix inputs")
                next_source = port.next_source
            if next_fixed != (next_source // low_base) % 100:
                raise ArithmeticError("100-state center transfer lost its exact carry")
            if center_next(center, carry, upper & 1) != next_fixed:
                raise ArithmeticError("center row ignored its certified low carry")
            if next_source in candidate_sets[index + 1]:
                next_center = (next_source // 10**next_s) % 100
                step_rows[center] = step_rows.get(center, 0) | (1 << next_center)

        sparse_step_rows_materialized += len(step_rows)
        sparse_edges_emitted += sum(row.bit_count() for row in step_rows.values())
        # The former implementation built a dense driver matrix and multiplied
        # it once at each admitted source-fiber step.
        full_row_products_avoided += 1
        if index == 0:
            reachable_rows = step_rows
            continue

        composed = boolean_sparse_rows_then(
            BooleanSparseRows[int].from_mapping(state_space, reachable_rows),
            BooleanSparseRows[int].from_mapping(state_space, step_rows),
        )
        reachable_rows = dict(composed.rows.as_mapping())
        sparse_compositions += 1
        sparse_intermediate_edges_visited += composed.intermediate_edges_visited
        sparse_row_joins += composed.row_joins
        sparse_joined_target_edges += composed.joined_target_edges
        sparse_composed_edges += composed.result_edges
        if work_sink is not None:
            if composed.intermediate_edges_visited:
                work_sink(
                    MahlerCenterWorkEvent.SPARSE_INTERMEDIATE_EDGE_VISIT,
                    composed.intermediate_edges_visited,
                )
            work_sink(MahlerCenterWorkEvent.SPARSE_COMPOSITION, 1)

    canonical_rows = tuple(reachable_rows.get(root, 0) for root in range(STATES))
    if work_sink is not None:
        work_sink(
            MahlerCenterWorkEvent.CANONICAL_ROW_MATERIALIZATION,
            len(canonical_rows),
        )
    work = MahlerCenterRelationWork(
        candidate_transitions_evaluated=candidate_transitions_evaluated,
        full_driver_matrices_avoided=full_driver_matrices_avoided,
        sparse_step_rows_materialized=sparse_step_rows_materialized,
        sparse_edges_emitted=sparse_edges_emitted,
        sparse_intermediate_edges_visited=sparse_intermediate_edges_visited,
        sparse_row_joins=sparse_row_joins,
        sparse_joined_target_edges=sparse_joined_target_edges,
        sparse_composed_edges=sparse_composed_edges,
        sparse_compositions=sparse_compositions,
        full_row_products_avoided=full_row_products_avoided,
        full_row_products_performed=0,
        canonical_rows_materialized=len(canonical_rows),
    )
    return canonical_rows, work


__all__ = ("compose_source_conditional_relation",)
