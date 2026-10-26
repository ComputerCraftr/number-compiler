"""Bounded exact temporal squaring for the normalized 2rev10 carry stencil.

The helper computes a finite causal cone for ``T²``. Perfect binary tiles are
interned by their exact digit children inside one invocation, so distinct SLP
grammars for the same bounded source window share the same semantic tiles.
Those temporary tile references are never returned or retained across calls.
This is a finite successor constructor, not an all-depth period certificate.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import Literal

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp_walks import iter_symbols
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.resources.metric_keys import (
    double_reverse as _double_reverse_keys,
)
from number_compiler.resources.owned_memo import LedgerReservation

from .stencil_moore import stencil_cell

_MAX_CELLS = 2048
_MAX_T2_STEPS = 512


class TemporalSquareScratchCapacityRefused(BlockContextBudgetExceeded):
    """The bounded semantic compiler refused its temporary scratch budget."""


class TemporalSquarePublicationFailed(BlockContextBudgetExceeded):
    """A completed semantic cone could not be published into the SLP arena."""


@dataclass(frozen=True, slots=True)
class TemporalSquareStats:
    """Executed work for one finite semantic cone computation."""

    semantic_tiles: int
    temporal_cones: int
    reused_cones: int
    source_traversal_tasks: int
    canonical_tile_reuses: int


@dataclass(frozen=True, slots=True)
class _TileNode:
    level: int
    left: int
    right: int


_PowerTaskKind = Literal["visit", "join_inputs", "finish"]


@dataclass(frozen=True, slots=True)
class _PowerTask:
    kind: _PowerTaskKind
    tile: int


def _release_charged_container(
    scratch: _ScratchReservation,
    clear: Callable[[], None],
    retained: int,
) -> None:
    """Clear one charged temporary container and return its live count."""
    if retained:
        scratch.release(retained, retained)
        clear()


class _ScratchReservation:
    """Batch ledger reservations while tracking exact live scratch use."""

    __slots__ = (
        "_growth_chunk",
        "_held_entries",
        "_held_nodes",
        "_live_entries",
        "_live_nodes",
        "_reservation",
    )

    def __init__(self, reservation: LedgerReservation) -> None:
        self._reservation = reservation
        self._growth_chunk = 64
        self._held_entries = 0
        self._held_nodes = 0
        self._live_entries = 0
        self._live_nodes = 0

    def acquire(self, entries: int = 1, nodes: int = 1) -> None:
        next_entries = self._live_entries + entries
        next_nodes = self._live_nodes + nodes
        missing_entries = max(0, next_entries - self._held_entries)
        missing_nodes = max(0, next_nodes - self._held_nodes)
        if missing_entries or missing_nodes:
            extra_entries = max(
                missing_entries,
                self._growth_chunk if missing_entries else 0,
            )
            extra_nodes = max(
                missing_nodes,
                self._growth_chunk if missing_nodes else 0,
            )
            try:
                self._reservation.reserve(
                    entries=extra_entries,
                    nodes=extra_nodes,
                )
            except BlockContextBudgetExceeded:
                try:
                    self._reservation.reserve(
                        entries=missing_entries,
                        nodes=missing_nodes,
                    )
                except BlockContextBudgetExceeded as exact_error:
                    raise TemporalSquareScratchCapacityRefused(
                        str(exact_error)
                    ) from exact_error
                self._held_entries += missing_entries
                self._held_nodes += missing_nodes
            else:
                self._held_entries += extra_entries
                self._held_nodes += extra_nodes
        self._live_entries = next_entries
        self._live_nodes = next_nodes

    def release(self, entries: int = 1, nodes: int = 1) -> None:
        if (
            entries < 0
            or nodes < 0
            or entries > self._live_entries
            or nodes > self._live_nodes
        ):
            raise ValueError("scratch release exceeds live temporary storage")
        self._live_entries -= entries
        self._live_nodes -= nodes

    def release_unused_capacity(self) -> None:
        """Return chunk slack before retained SLP output competes for budget."""
        unused_entries = self._held_entries - self._live_entries
        unused_nodes = self._held_nodes - self._live_nodes
        if unused_entries or unused_nodes:
            self._reservation.release(entries=unused_entries, nodes=unused_nodes)
            self._held_entries = self._live_entries
            self._held_nodes = self._live_nodes

    def use_exact_growth(self) -> None:
        """Stop over-reserving while publishing output nodes to the SLP arena."""
        self.release_unused_capacity()
        self._growth_chunk = 1

    def __enter__(self) -> _ScratchReservation:
        self._reservation.__enter__()
        return self

    def __exit__(
        self,
        exc_type: object,
        exc_value: object,
        traceback: object,
    ) -> Literal[False]:
        self._reservation.__exit__(exc_type, exc_value, traceback)
        return False


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
        scratch: _ScratchReservation,
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
                _release_charged_container(self._scratch, forest.clear, retained_forest)

    def middle(self, root: int) -> int:
        """Evaluate U_t with an explicit postorder worklist, never recursion."""
        tasks: list[_PowerTask] = []
        values: list[int] = []
        retained_tasks = 0
        retained_values = 0

        def push_task(kind: _PowerTaskKind, tile: int) -> None:
            nonlocal retained_tasks
            self._scratch.acquire()
            try:
                tasks.append(_PowerTask(kind, tile))
            except BaseException as error:
                self._scratch.release()
                raise error
            retained_tasks += 1

        def pop_task() -> _PowerTask:
            nonlocal retained_tasks
            task = tasks.pop()
            retained_tasks -= 1
            self._scratch.release()
            return task

        def push_value(tile: int) -> None:
            nonlocal retained_values
            self._scratch.acquire()
            try:
                values.append(tile)
            except BaseException as error:
                self._scratch.release()
                raise error
            retained_values += 1

        def pop_value() -> int:
            nonlocal retained_values
            tile = values.pop()
            retained_values -= 1
            self._scratch.release()
            return tile

        def record_cone(reused: bool) -> None:
            if self._on_cone_visit is not None:
                self._on_cone_visit(reused)
            if reused:
                self._reused_cones += 1
            else:
                self._computed_cones += 1

        def remember(source: int, result: int) -> None:
            self._scratch.acquire()
            self._retained_graph_entries += 1
            self._retained_graph_nodes += 1
            self._powers[source] = result

        try:
            push_task("visit", root)
            while tasks:
                task = pop_task()
                tile = task.tile
                if task.kind == "visit":
                    previous = self._powers.get(tile)
                    if previous is not None:
                        record_cone(True)
                        push_value(previous)
                        continue

                    record_cone(False)
                    node = self._tiles[tile]
                    if node.level < 2:
                        raise ValueError("four source digits are required per cone")
                    left_tile = self._tiles[node.left]
                    right_tile = self._tiles[node.right]
                    a, b = left_tile.left, left_tile.right
                    c, d = right_tile.left, right_tile.right
                    if node.level == 2:
                        result = self.pair(stencil_cell(a, b, c), stencil_cell(b, c, d))
                        remember(tile, result)
                        push_value(result)
                        continue

                    ab = self.pair(a, b)
                    bc = self.pair(b, c)
                    cd = self.pair(c, d)
                    push_task("join_inputs", tile)
                    push_task("visit", cd)
                    push_task("visit", bc)
                    push_task("visit", ab)
                elif task.kind == "join_inputs":
                    w = pop_value()
                    v = pop_value()
                    u = pop_value()
                    uv = self.pair(u, v)
                    vw = self.pair(v, w)
                    push_task("finish", tile)
                    push_task("visit", vw)
                    push_task("visit", uv)
                elif task.kind == "finish":
                    right_result = pop_value()
                    left_result = pop_value()
                    result = self.pair(left_result, right_result)
                    remember(tile, result)
                    push_value(result)
                else:
                    raise AssertionError("unknown temporal cone task")
            if len(values) != 1:
                raise AssertionError("temporal cone worklist left extra results")
            return pop_value()
        finally:
            _release_charged_container(self._scratch, values.clear, retained_values)
            _release_charged_container(self._scratch, tasks.clear, retained_tasks)

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
            _release_charged_container(self._scratch, outputs.clear, retained_outputs)
            _release_charged_container(self._scratch, tasks.clear, retained_tasks)


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
) -> tuple[int, TemporalSquareStats]:
    """Compute the exact center after a bounded dyadic number of ``T²`` steps.

    The source is one complete ``4*steps``-digit causal halo.  The result is
    published into the same ledger-owned arena only after the semantic cone
    has completed.  Scratch refusal is distinguished from malformed input and
    from failure while publishing the completed output.
    """
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
    if type(root) is not int or not 0 <= root < len(arena.nodes):
        raise ValueError("temporal square source root is invalid")
    arena.empty()  # Check the arena lifecycle through its public API.
    source_width = arena.nodes[root].length
    if source_width != 4 * steps or source_width > max_cells:
        raise ValueError("temporal square source is not its complete admitted halo")

    reservation = LedgerReservation(arena.ledger, scratch_owner)
    with _ScratchReservation(reservation) as scratch:
        power = _CarrySpacetimePower(scratch, on_cone_visit, on_tile_pair)
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
            stats = power.stats
            return result, stats
        finally:
            # Exception tracebacks retain local frames. Clear the potentially
            # large semantic DAG before the reservation releases its charges.
            power.release_temporary_storage()


def try_source_bound_square_cone(
    arena: LedgerSLPArena,
    root: int,
    steps: int,
    scratch_owner: int,
) -> int | None:
    """Publish one exact powered cone, or decline before output publication.

    ``None`` means the bounded semantic compiler could not reserve its
    prepublication scratch state; the existing exact Hashlife path can then
    proceed. Other construction, authority and output failures propagate.
    """
    if type(steps) is not int or steps < 1 or steps & (steps - 1):
        raise ValueError("source-bound cone requires a positive dyadic horizon")
    if steps > _MAX_T2_STEPS:
        return None

    publication_checkpoint = len(arena.nodes)

    def record_source_task(_is_node: bool) -> None:
        arena.ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_SQUARE_REGION_VISITS
        )

    def record_cone_visit(reused: bool) -> None:
        counter = (
            _double_reverse_keys.DOUBLE_REVERSE_HASHLIFE_CONE_HITS
            if reused
            else _double_reverse_keys.DOUBLE_REVERSE_HASHLIFE_CONES
        )
        arena.ledger.bump(counter)

    def record_tile_pair() -> None:
        arena.ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_SQUARE_REGION_VISITS
        )

    try:
        result, _statistics = temporal_square_cone(
            arena,
            root,
            steps,
            scratch_owner=scratch_owner,
            max_cells=_MAX_CELLS,
            on_source_task=record_source_task,
            on_cone_visit=record_cone_visit,
            on_tile_pair=record_tile_pair,
        )
    except TemporalSquareScratchCapacityRefused:
        if len(arena.nodes) != publication_checkpoint:
            raise AssertionError(
                "scratch refusal occurred after temporal cone publication"
            ) from None
        return None

    return result
