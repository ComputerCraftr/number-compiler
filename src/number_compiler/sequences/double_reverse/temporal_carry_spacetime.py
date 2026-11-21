"""Finite exact temporal squaring for the normalized 2rev10 carry stencil.

The helper computes a finite causal cone for ``T²``. Perfect binary tiles are
interned by their exact digit children inside one invocation, so distinct SLP
grammars for the same bounded source window share semantic tiles. Temporary
tile references are not retained across calls. This is a finite successor
constructor, not an all-depth period certificate.
"""

from __future__ import annotations

from collections.abc import Callable

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.temporal_cone import (
    CarrySpacetimePower,
    TemporalSquarePublicationFailed,
    TemporalSquareScratchCapacityRefused,
    TemporalSquareScratchReservation,
    TemporalSquareStats,
)
from number_compiler.resources.owned_memo import LedgerReservation

from .stencil_moore import f_port_cell
from .temporal_packed_diagonal import (
    PACKED_DIAGONAL_MIN_STEPS,
    publish_packed_diagonal,
    record_square_work,
)

_MAX_CELLS = 4096
_MAX_T2_STEPS = 1024
_MAX_LARGE_PACKED_T2_STEPS = 16384


def temporal_square_cone(
    arena: LedgerSLPArena,
    root: int,
    steps: int,
    *,
    scratch_owner: int,
    max_cells: int = _MAX_CELLS,
    on_source_task: Callable[[bool], None] | None = None,
    on_cone_visit: Callable[[bool], None] | None = None,
    on_tile_pair: Callable[[], None] | None = None,
    account_semantic_metrics: bool = False,
) -> tuple[int, TemporalSquareStats]:
    """Compute an exact ``T²`` cone from one complete ``4*steps`` causal halo."""
    if type(arena) is not LedgerSLPArena:
        raise TypeError("temporal square requires its exact ledgered SLP arena")
    if type(steps) is not int or steps < 1 or steps & (steps - 1):
        raise ValueError("temporal square requires a positive dyadic horizon")
    if steps > _MAX_T2_STEPS:
        raise ValueError("temporal square horizon exceeds the admitted bound")
    if type(max_cells) is not int or max_cells < 4 or max_cells > _MAX_CELLS:
        raise ValueError("temporal square cell bound is invalid")
    if type(scratch_owner) is not int or scratch_owner < 0:
        raise ValueError("temporal square scratch owner is invalid")
    if type(account_semantic_metrics) is not bool:
        raise TypeError("semantic metrics selector must be Boolean")
    if type(root) is not int or not 0 <= root < len(arena.nodes):
        raise ValueError("temporal square source root is invalid")
    arena.empty()
    source_width = arena.nodes[root].length
    if source_width != 4 * steps or source_width > max_cells:
        raise ValueError("temporal square source is not its complete admitted halo")

    reservation = LedgerReservation(arena.ledger, scratch_owner)
    with TemporalSquareScratchReservation(reservation) as scratch:
        packed_attempt: TemporalSquareStats | None = None
        if steps >= PACKED_DIAGONAL_MIN_STEPS:
            stats = TemporalSquareStats(0, 0, 0, 0, 0)
            publication_checkpoint = len(arena.nodes)
            published_root: int | None = None
            try:
                packed_result = publish_packed_diagonal(
                    arena,
                    root,
                    steps,
                    scratch,
                    on_source_task,
                    stats,
                )
                published_root = packed_result[0]
                return packed_result
            except TemporalSquareScratchCapacityRefused:
                if len(arena.nodes) != publication_checkpoint:
                    raise AssertionError(
                        "packed scratch refusal occurred after output publication"
                    ) from None
                # Release packed scratch before using the exact semantic path.
                scratch.release_unused_capacity()
                packed_attempt = stats
            finally:
                if account_semantic_metrics and packed_attempt is None:
                    # Packed work counts source visits and row transforms.
                    try:
                        record_square_work(arena, stats)
                    except BaseException as record_error:
                        if (
                            published_root is not None
                            and len(arena.nodes) > publication_checkpoint
                        ):
                            try:
                                arena.rollback_unpublished_suffix(
                                    publication_checkpoint
                                )
                            except BaseException as cleanup_error:
                                raise cleanup_error from record_error
                        raise
        try:
            power = CarrySpacetimePower(
                scratch, on_cone_visit, on_tile_pair, four_cell_action=f_port_cell
            )
        except BaseException:
            if account_semantic_metrics and packed_attempt is not None:
                record_square_work(arena, packed_attempt)
            raise
        publication_checkpoint = len(arena.nodes)
        published_semantic_root: int | None = None
        try:
            source = power.compile_slp(
                arena,
                root,
                max_cells,
                on_source_task,
            )
            scratch.release_unused_capacity()
            center = power.middle(source)
            scratch.use_exact_growth()
            publication_checkpoint = len(arena.nodes)
            result = power.publish(arena, center)
            if arena.nodes[result].length != source_width // 2:
                try:
                    arena.rollback_unpublished_suffix(publication_checkpoint)
                except BaseException as cleanup_error:
                    raise AssertionError(
                        "temporal cone output width changed and rollback failed"
                    ) from cleanup_error
                raise AssertionError("temporal cone output has the wrong width")
            published_semantic_root = result
            stats = power.stats
            if packed_attempt is not None:
                stats.source_traversal_tasks += packed_attempt.source_traversal_tasks
                stats.packed_row_evaluations += packed_attempt.packed_row_evaluations
                stats.packed_row_operand_bits += packed_attempt.packed_row_operand_bits
                stats.packed_output_digit_visits += (
                    packed_attempt.packed_output_digit_visits
                )
            return result, stats
        finally:
            try:
                if account_semantic_metrics:
                    # Record partial/completed work before dropping the graph.
                    try:
                        record_square_work(
                            arena, power.stats, packed_attempt, include_semantic=True
                        )
                    except BaseException as record_error:
                        if (
                            published_semantic_root is not None
                            and len(arena.nodes) > publication_checkpoint
                        ):
                            try:
                                arena.rollback_unpublished_suffix(
                                    publication_checkpoint
                                )
                            except BaseException as cleanup_error:
                                raise cleanup_error from record_error
                            published_semantic_root = None
                        raise
            finally:
                try:
                    # Tracebacks retain frames, so clear the DAG on failures.
                    power.release_temporary_storage()
                except BaseException as cleanup_error:
                    if (
                        published_semantic_root is not None
                        and len(arena.nodes) > publication_checkpoint
                    ):
                        try:
                            arena.rollback_unpublished_suffix(publication_checkpoint)
                        except BaseException as rollback_error:
                            raise rollback_error from cleanup_error
                    raise


def try_source_bound_square_cone(
    arena: LedgerSLPArena,
    root: int,
    steps: int,
    scratch_owner: int,
) -> int | None:
    """Publish one exact cone; ``None`` declines before packed output publication."""
    if type(steps) is not int or steps < 1 or steps & (steps - 1):
        raise ValueError("source-bound cone requires a positive dyadic horizon")
    if steps > _MAX_T2_STEPS:
        if steps > _MAX_LARGE_PACKED_T2_STEPS:
            return None
        if type(arena) is not LedgerSLPArena:
            raise TypeError("source-bound cone requires its ledgered SLP arena")
        arena.empty()
        if type(root) is not int or not 0 <= root < len(arena.nodes):
            raise ValueError("source-bound cone root is invalid")
        if arena.nodes[root].length != 4 * steps:
            raise ValueError("source-bound cone needs its complete causal halo")
        if type(scratch_owner) is not int or scratch_owner < 0:
            raise ValueError("source-bound cone scratch owner is invalid")
        checkpoint = len(arena.nodes)
        stats = TemporalSquareStats(0, 0, 0, 0, 0)
        published: int | None = None
        work_recorded = False
        try:
            with TemporalSquareScratchReservation(
                LedgerReservation(arena.ledger, scratch_owner)
            ) as scratch:
                try:
                    published, _ = publish_packed_diagonal(
                        arena,
                        root,
                        steps,
                        scratch,
                        None,
                        stats,
                    )
                except TemporalSquareScratchCapacityRefused:
                    if len(arena.nodes) != checkpoint:
                        raise AssertionError(
                            "packed scratch refusal occurred after publication"
                        ) from None
                    work_recorded = True
                    record_square_work(arena, stats)
                    return None
                work_recorded = True
                record_square_work(arena, stats)
        except BaseException as error:
            if not work_recorded:
                try:
                    record_square_work(arena, stats)
                except BaseException as record_error:
                    raise error from record_error
            if published is not None and len(arena.nodes) > checkpoint:
                try:
                    arena.rollback_unpublished_suffix(checkpoint)
                except BaseException as cleanup_error:
                    raise error from cleanup_error
            raise
        return published

    publication_checkpoint = len(arena.nodes)

    try:
        result, _statistics = temporal_square_cone(
            arena,
            root,
            steps,
            scratch_owner=scratch_owner,
            max_cells=_MAX_CELLS,
            account_semantic_metrics=True,
        )
    except TemporalSquareScratchCapacityRefused:
        if len(arena.nodes) != publication_checkpoint:
            raise AssertionError(
                "scratch refusal occurred after temporal cone publication"
            ) from None
        return None

    return result


__all__ = [
    "TemporalSquarePublicationFailed",
    "TemporalSquareScratchCapacityRefused",
    "temporal_square_cone",
    "try_source_bound_square_cone",
]
