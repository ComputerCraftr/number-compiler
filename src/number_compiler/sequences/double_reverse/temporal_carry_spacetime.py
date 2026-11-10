"""Finite exact temporal squaring for the normalized 2rev10 carry stencil.

The helper computes a finite causal cone for ``T²``. Perfect binary tiles are
interned by their exact digit children inside one invocation, so distinct SLP
grammars for the same bounded source window share semantic tiles. Temporary
tile references are not retained across calls. This is a finite successor
constructor, not an all-depth period certificate.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp_walks import iter_symbols
from number_compiler.resources.owned_memo import LedgerReservation

from .stencil_moore import stencil_cell
from .temporal_packed_diagonal import (
    PACKED_DIAGONAL_MIN_STEPS,
    TemporalSquarePublicationFailed,
    TemporalSquareScratchCapacityRefused,
    TemporalSquareScratchReservation,
    TemporalSquareStats,
    publish_packed_diagonal,
    record_square_work,
    release_charged_container,
)

_MAX_CELLS = 4096
_MAX_T2_STEPS = 1024
_MAX_LARGE_PACKED_T2_STEPS = 16384

# The exact 10-symbol spatial alphabet is tiny and immutable. Compile its
# 1,000 three-digit decisions once; temporal cones still use the same
# `stencil_cell` law, with no source- or phase-dependent cached rows.
_STENCIL_TABLE: tuple[int, ...] = tuple(
    stencil_cell(left, center, right)
    for left in range(10)
    for center in range(10)
    for right in range(10)
)


@dataclass(frozen=True, slots=True)
class _TileNode:
    level: int
    left: int
    right: int


@dataclass(slots=True)
class _ConeFrame:
    """One explicit postorder frame for a bounded temporal cone visit."""

    tile: int
    stage: int = 0
    a: int = 0
    b: int = 0
    c: int = 0
    d: int = 0
    u: int = 0
    v: int = 0
    w: int = 0
    uv: int = 0


class _CarrySpacetimePower:
    """Per-call exact-content tile and temporal-power arenas."""

    __slots__ = (
        "_canonical_tile_reuses",
        "_computed_cones",
        "_intern",
        "_on_tile_pair",
        "_on_cone_visit",
        "_powers",
        "_reused_cones",
        "_retained_graph_entries",
        "_retained_graph_nodes",
        "_scratch",
        "_source_traversal_tasks",
        "_tiles",
    )

    def __init__(
        self,
        scratch: TemporalSquareScratchReservation,
        on_cone_visit: Callable[[bool], None] | None,
        on_tile_pair: Callable[[], None] | None,
    ) -> None:
        self._scratch = scratch
        self._on_cone_visit = on_cone_visit
        self._on_tile_pair = on_tile_pair
        # Reserve the fixed terminal alphabet before allocating its roots.
        scratch.acquire(10, 10)
        self._tiles = [_TileNode(0, digit, digit) for digit in range(10)]
        self._intern: dict[tuple[int, int], int] = {}
        self._powers: dict[int, int] = {}
        self._retained_graph_entries = 10
        self._retained_graph_nodes = 10
        self._computed_cones = 0
        self._reused_cones = 0
        self._canonical_tile_reuses = 0
        self._source_traversal_tasks = 0

    @property
    def stats(self) -> TemporalSquareStats:
        return TemporalSquareStats(
            semantic_tiles=len(self._tiles),
            temporal_cones=self._computed_cones,
            reused_cones=self._reused_cones,
            source_traversal_tasks=self._source_traversal_tasks,
            canonical_tile_reuses=self._canonical_tile_reuses,
            packed_row_evaluations=0,
        )

    def release_temporary_storage(self) -> None:
        """Drop the content graph even when a caller retains an exception."""
        self._powers.clear()
        self._intern.clear()
        self._tiles.clear()
        self._scratch.release(
            self._retained_graph_entries,
            self._retained_graph_nodes,
        )
        self._retained_graph_entries = 0
        self._retained_graph_nodes = 0

    def pair(self, left: int, right: int) -> int:
        """Intern one ordered, equal-level pair by exact child identities."""
        if self._on_tile_pair is not None:
            self._on_tile_pair()
        left_node = self._tiles[left]
        right_node = self._tiles[right]
        if left_node.level != right_node.level:
            raise ValueError("cannot join noncongruent dyadic tiles")
        key = (left, right)
        previous = self._intern.get(key)
        if previous is not None:
            self._canonical_tile_reuses += 1
            return previous

        # Reserve the interner row and semantic tile before publishing either.
        self._scratch.acquire(2, 2)
        self._retained_graph_entries += 2
        self._retained_graph_nodes += 2
        result = len(self._tiles)
        self._intern[key] = result
        self._tiles.append(_TileNode(left_node.level + 1, left, right))
        return result

    def compile_slp(
        self,
        arena: LedgerSLPArena,
        root: int,
        max_cells: int,
        on_source_task: Callable[[bool], None] | None,
    ) -> int:
        """Read an admitted SLP once and fold it into a canonical binary tile."""
        if type(root) is not int or not 0 <= root < len(arena.nodes):
            raise ValueError("invalid temporal cone source root")
        width = arena.nodes[root].length
        if width < 4 or width & (width - 1):
            raise ValueError("temporal cone source must have power-of-two width")
        if width > max_cells:
            raise ValueError("temporal cone source exceeds its admitted width")

        # The binary accumulator is O(log(width)); its retained entries are
        # separately charged before each push. iter_symbols accounts every
        # pending grammar/repeat task and releases them even if traversal fails.
        forest: list[tuple[int, int]] = []
        retained_forest = 0

        def reserve_task() -> None:
            self._scratch.acquire()

        def release_tasks(count: int) -> None:
            self._scratch.release(count, count)

        def record_source_task(_is_node: bool) -> None:
            self._source_traversal_tasks += 1
            if on_source_task is not None:
                on_source_task(_is_node)

        symbols = iter_symbols(
            arena,
            root,
            on_task=record_source_task,
            reserve_task=reserve_task,
            release_tasks=release_tasks,
        )
        symbol_count = 0
        try:
            for digit in symbols:
                if symbol_count >= max_cells:
                    raise ValueError(
                        "temporal cone source traversal exceeded its bound"
                    )
                if type(digit) is not int or not 0 <= digit <= 9:
                    raise ValueError("temporal cone source contains a nondecimal digit")
                symbol_count += 1
                tile = digit
                level = 0
                while forest and forest[-1][0] == level:
                    previous_level, previous = forest.pop()
                    retained_forest -= 1
                    self._scratch.release()
                    if previous_level != level:
                        raise AssertionError("temporal tile accumulator is malformed")
                    tile = self.pair(previous, tile)
                    level += 1
                self._scratch.acquire()
                retained_forest += 1
                try:
                    forest.append((level, tile))
                except BaseException as error:
                    retained_forest -= 1
                    self._scratch.release()
                    raise error
            if symbol_count != width or len(forest) != 1:
                raise ValueError("temporal cone traversal did not cover its source")
            expected_level = width.bit_length() - 1
            level, root_tile = forest.pop()
            retained_forest -= 1
            self._scratch.release()
            if level != expected_level:
                raise ValueError("temporal cone source has an incomplete binary tile")
            return root_tile
        finally:
            try:
                symbols.close()
            finally:
                release_charged_container(self._scratch, forest.clear, retained_forest)

    def middle(self, root: int) -> int:
        """Compute a canonical temporal cone with bounded iterative postorder.

        Each descent removes one dyadic level, so the admitted 4,096-cell
        bound caps the explicit frame stack at 12 levels independently of
        source-SLP height and ``--nth``. Memoization is keyed by exact
        *semantic tile content*, never a source occurrence or word identity.
        """
        level = self._tiles[root].level
        if level < 2 or level > _MAX_CELLS.bit_length() - 1:
            raise ValueError("temporal cone tile is outside the admitted depth")
        # Four accounting slots per dyadic frame cover one invocation, its
        # intermediate tile IDs and the local return. No source word/window
        # is expanded for this stack.
        stack_charge = 4 * level
        self._scratch.acquire(stack_charge, stack_charge)
        frames = [_ConeFrame(root)]
        returned: int | None = None
        # Local aliases avoid repeated owner-field loads in the bounded
        # postorder loop. They refer to the same per-call, ledgered stores.
        powers = self._powers
        tiles = self._tiles
        pair = self.pair
        stencil = _STENCIL_TABLE
        try:
            while frames:
                frame = frames[-1]
                if frame.stage == 0:
                    previous = powers.get(frame.tile)
                    if previous is not None:
                        self._reused_cones += 1
                        if self._on_cone_visit is not None:
                            self._on_cone_visit(True)
                        frames.pop()
                        returned = previous
                        continue
                    self._computed_cones += 1
                    if self._on_cone_visit is not None:
                        self._on_cone_visit(False)
                    node = tiles[frame.tile]
                    if node.level < 2:
                        raise ValueError("four source digits are required per cone")
                    left_tile = tiles[node.left]
                    right_tile = tiles[node.right]
                    frame.a, frame.b = left_tile.left, left_tile.right
                    frame.c, frame.d = right_tile.left, right_tile.right
                    if node.level == 2:
                        result = pair(
                            stencil[frame.a * 100 + frame.b * 10 + frame.c],
                            stencil[frame.b * 100 + frame.c * 10 + frame.d],
                        )
                        self._scratch.acquire()
                        self._retained_graph_entries += 1
                        self._retained_graph_nodes += 1
                        powers[frame.tile] = result
                        frames.pop()
                        returned = result
                        continue
                    frame.stage = 1
                    frames.append(_ConeFrame(pair(frame.a, frame.b)))
                    continue

                if returned is None:
                    raise AssertionError("postorder cone child has no result")
                child_result = returned
                returned = None
                if frame.stage == 1:
                    frame.u = child_result
                    frame.stage = 2
                    frames.append(_ConeFrame(pair(frame.b, frame.c)))
                elif frame.stage == 2:
                    frame.v = child_result
                    frame.stage = 3
                    frames.append(_ConeFrame(pair(frame.c, frame.d)))
                elif frame.stage == 3:
                    frame.w = child_result
                    frame.uv = pair(frame.u, frame.v)
                    frame.stage = 4
                    frames.append(_ConeFrame(frame.uv))
                elif frame.stage == 4:
                    frame.uv = child_result
                    frame.stage = 5
                    frames.append(_ConeFrame(pair(frame.v, frame.w)))
                elif frame.stage == 5:
                    result = pair(frame.uv, child_result)
                    # Retain scratch charge until this per-call bank is released.
                    self._scratch.acquire()
                    self._retained_graph_entries += 1
                    self._retained_graph_nodes += 1
                    powers[frame.tile] = result
                    frames.pop()
                    returned = result
                else:
                    raise AssertionError("unknown temporal cone postorder stage")
            if returned is None:
                raise AssertionError("root temporal cone produced no result")
            return returned
        finally:
            release_charged_container(self._scratch, frames.clear, stack_charge)

    def publish(self, arena: LedgerSLPArena, root: int) -> int:
        """Publish the computed center into the same SLP arena transactionally."""
        checkpoint = len(arena.nodes)
        outputs: dict[int, int] = {}
        tasks: list[tuple[int, bool]] = []
        retained_outputs = 0
        retained_tasks = 0

        def push_task(tile: int, done: bool) -> None:
            nonlocal retained_tasks
            self._scratch.acquire()
            try:
                tasks.append((tile, done))
            except BaseException as error:
                self._scratch.release()
                raise error
            retained_tasks += 1

        def remember(tile: int, slp_root: int) -> None:
            nonlocal retained_outputs
            self._scratch.acquire()
            try:
                outputs[tile] = slp_root
            except BaseException as error:
                self._scratch.release()
                raise error
            retained_outputs += 1

        try:
            push_task(root, False)
            while tasks:
                tile, done = tasks.pop()
                retained_tasks -= 1
                self._scratch.release()
                if tile in outputs:
                    continue
                node = self._tiles[tile]
                if node.level == 0:
                    remember(tile, arena.terminal(node.left))
                elif done:
                    remember(
                        tile, arena.concat(outputs[node.left], outputs[node.right])
                    )
                else:
                    push_task(tile, True)
                    if node.right not in outputs:
                        push_task(node.right, False)
                    if node.left not in outputs:
                        push_task(node.left, False)
            return outputs[root]
        except BaseException as error:
            try:
                arena.rollback_unpublished_suffix(checkpoint)
            except BaseException as cleanup_error:
                raise error from cleanup_error
            if isinstance(error, TemporalSquareScratchCapacityRefused):
                raise TemporalSquarePublicationFailed(
                    "scratch capacity was exhausted while publishing cone output"
                ) from error
            raise
        finally:
            release_charged_container(self._scratch, outputs.clear, retained_outputs)
            release_charged_container(self._scratch, tasks.clear, retained_tasks)


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
            power = _CarrySpacetimePower(scratch, on_cone_visit, on_tile_pair)
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
