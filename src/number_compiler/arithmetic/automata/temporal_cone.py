"""Ledgered exact-content tiles for finite overlapping temporal cones."""

from __future__ import annotations

from collections.abc import Callable
from contextlib import closing, nullcontext
from dataclasses import dataclass
from itertools import islice
from typing import Literal

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp_interval import fold_slp_interval
from number_compiler.arithmetic.automata.slp_walks import iter_symbols, symbol_at
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.lifecycle import cleanup_all
from number_compiler.resources.owned_memo import LedgerReservation

_MAX_CELLS = 4096


@dataclass(slots=True)
class TemporalSquareStats:
    """Executed work; packed operand bits are a conservative logical charge."""

    semantic_tiles: int
    temporal_cones: int
    reused_cones: int
    source_traversal_tasks: int
    canonical_tile_reuses: int
    packed_row_evaluations: int = 0
    packed_row_operand_bits: int = 0
    packed_output_digit_visits: int = 0


class TemporalSquareScratchCapacityRefused(BlockContextBudgetExceeded):
    """The bounded semantic compiler refused its temporary scratch budget."""


class TemporalSquarePublicationFailed(BlockContextBudgetExceeded):
    """A completed semantic cone could not be published into the SLP arena."""


def release_charged_container(
    scratch: TemporalSquareScratchReservation,
    clear: Callable[[], None],
    retained: int,
) -> None:
    """Clear one charged temporary container and return its live count."""
    if retained:
        try:
            scratch.release(retained, retained)
        finally:
            clear()


class TemporalSquareScratchReservation:
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
        if (
            type(entries) is not int
            or entries < 0
            or type(nodes) is not int
            or nodes < 0
        ):
            raise ValueError("scratch reservation increments must be nonnegative")
        next_entries = self._live_entries + entries
        next_nodes = self._live_nodes + nodes
        if next_entries <= self._held_entries and next_nodes <= self._held_nodes:
            # Reuse previously reserved chunk capacity.
            self._live_entries = next_entries
            self._live_nodes = next_nodes
            return
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

    def try_acquire(self, entries: int, nodes: int) -> bool:
        """Reserve before optional construction, or leave the workspace intact."""
        try:
            self.acquire(entries, nodes)
        except TemporalSquareScratchCapacityRefused:
            return False
        return True

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

    def __enter__(self) -> TemporalSquareScratchReservation:
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


class CarrySpacetimePower:
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
        "_cell_action",
        "_four_cell_action",
        "_slp_tiles",
        "_slp_tile_entries",
        "_slp_published",
        "_slp_published_entries",
    )

    def __init__(
        self,
        scratch: TemporalSquareScratchReservation,
        on_cone_visit: Callable[[bool], None] | None,
        on_tile_pair: Callable[[], None] | None,
        *,
        cell_action: Callable[[int, int], int] | None = None,
        four_cell_action: Callable[[int, int, int, int], tuple[int, int]] | None = None,
    ) -> None:
        if (cell_action is None) == (four_cell_action is None):
            raise ValueError("a temporal cone requires exactly one local action")
        self._scratch = scratch
        self._on_cone_visit = on_cone_visit
        self._on_tile_pair = on_tile_pair
        # Reserve the fixed terminal alphabet before allocating its roots.
        alphabet_size = 100 if cell_action is not None else 10
        scratch.acquire(alphabet_size, alphabet_size)
        self._tiles = [_TileNode(0, digit, digit) for digit in range(alphabet_size)]
        self._cell_action = cell_action
        self._four_cell_action = four_cell_action
        self._intern: dict[tuple[int, int], int] = {}
        self._powers: dict[int, int] = {}
        self._retained_graph_entries = alphabet_size
        self._retained_graph_nodes = alphabet_size
        self._computed_cones = 0
        self._reused_cones = 0
        self._canonical_tile_reuses = 0
        self._source_traversal_tasks = 0
        self._slp_tiles: dict[tuple[LedgerSLPArena, int, int], int] = {}
        self._slp_tile_entries = 0
        self._slp_published: dict[tuple[LedgerSLPArena, int, int], int] = {}
        self._slp_published_entries = 0

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
        self._slp_tiles.clear()
        self._slp_published.clear()
        self._scratch.release(
            self._retained_graph_entries
            + self._slp_tile_entries
            + self._slp_published_entries,
            self._retained_graph_nodes
            + self._slp_tile_entries
            + self._slp_published_entries,
        )
        self._slp_tile_entries = 0
        self._slp_published_entries = 0
        self._retained_graph_entries = 0
        self._retained_graph_nodes = 0

    def _discard_published(self) -> None:
        retained = self._slp_published_entries
        self._slp_published.clear()
        self._slp_published_entries = 0
        self._scratch.release(retained, retained)

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
        if type(root) is not int or not 0 <= root < len(self._tiles):
            raise ValueError("invalid temporal cone root")
        published = self._powers.get(root)
        if published is not None:
            self._reused_cones += 1
            if self._on_cone_visit is not None:
                self._on_cone_visit(True)
            return published
        level = self._tiles[root].level
        if (
            level < (1 if self._cell_action is not None else 2)
            or level > _MAX_CELLS.bit_length() - 1
        ):
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
                    if node.level == 1 and self._cell_action is not None:
                        result = self._cell_action(node.left, node.right)
                        self._scratch.acquire()
                        self._retained_graph_entries += 1
                        self._retained_graph_nodes += 1
                        powers[frame.tile] = result
                        frames.pop()
                        returned = result
                        continue
                    if node.level < 2:
                        raise ValueError("four source digits are required per cone")
                    left_tile = tiles[node.left]
                    right_tile = tiles[node.right]
                    frame.a, frame.b = left_tile.left, left_tile.right
                    frame.c, frame.d = right_tile.left, right_tile.right
                    if node.level == 2:
                        if self._cell_action is None:
                            if self._four_cell_action is None:
                                raise ValueError("temporal cone has no four-cell law")
                            left, right = self._four_cell_action(
                                frame.a, frame.b, frame.c, frame.d
                            )
                            result = pair(left, right)
                        else:
                            ab = self._cell_action(frame.a, frame.b)
                            bc = self._cell_action(frame.b, frame.c)
                            cd = self._cell_action(frame.c, frame.d)
                            result = pair(
                                self._cell_action(ab, bc), self._cell_action(bc, cd)
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

    def advance_blocks(self, source: tuple[int, ...], span: int) -> tuple[int, ...]:
        """Advance a padded base-100 word with a one-sided H action."""
        if (
            self._cell_action is None
            or type(span) is not int
            or span < 1
            or span & (span - 1)
        ):
            raise ValueError("padded H advancement needs a dyadic cell action")
        if any(type(cell) is not int or not 0 <= cell < 100 for cell in source):
            raise ValueError("padded H source contains an invalid base-100 cell")
        if not source or span > _MAX_CELLS // 2:
            raise ValueError("padded H cone exceeds its admitted extent")
        # One zero tile on each side covers the complete past light cone.
        # Reusing its root avoids pairing every position in either halo.
        blocks = (len(source) + span - 1) // span
        endpoint_cells = len(source) + span
        workspace = 2 * (blocks + 1) * span + 2 * span + span.bit_length() + 4
        self._scratch.acquire(workspace, workspace)
        result: list[int] = []
        pending: list[int] = []
        row: list[int] = []
        try:
            zero = 0
            for _ in range(span.bit_length() - 1):
                zero = self.pair(zero, zero)
            previous = zero
            for start in range(0, (blocks + 1) * span, span):
                current = zero
                if start < len(source):
                    row = list(source[start : start + span])
                    current = self._padded_cell_tile(row, span)
                pending.append(self.middle(self.pair(previous, current)))
                while pending and len(result) < endpoint_cells:
                    node = self._tiles[pending.pop()]
                    if node.level == 0:
                        result.append(node.left)
                    else:
                        pending.append(node.right)
                        pending.append(node.left)
                previous = current
            return tuple(result)
        finally:
            result.clear()
            pending.clear()
            row.clear()
            self._scratch.release(workspace, workspace)

    def _padded_cell_tile(self, row: list[int], span: int) -> int:
        """Consume one bounded inlet and its right zero padding."""
        row.extend([0] * (span - len(row)))
        count = span
        while count > 1:
            count //= 2
            for index in range(count):
                row[index] = self.pair(row[2 * index], row[2 * index + 1])
        return row[0]

    def _tile_from_cell_slp(self, arena: LedgerSLPArena, root: int) -> int:
        """Compile one power-of-two cell SLP by exact semantic subtree IDs.

        Full REPEAT nodes and equal halves are compiled once and reused across
        every requested block and dyadic time split. No physical occurrence
        expansion is needed for repeated input segments.
        """
        length = arena.nodes[root].length
        if length < 1 or length & (length - 1) or length > _MAX_CELLS:
            raise ValueError("H cell tile needs dyadic SLP extent")
        memo = self._slp_tiles
        generation = arena.node_id_generation

        def key(node: int) -> tuple[LedgerSLPArena, int, int]:
            return arena, generation, node

        tasks: list[tuple[int, int, int, bool]] = [(root, 0, 0, False)]
        frame_budget = 4 * (length.bit_length() + 1)
        self._scratch.acquire(frame_budget, frame_budget)
        try:
            while tasks:
                node, left, right, ready = tasks.pop()
                if key(node) in memo:
                    continue
                n = arena.nodes[node].length
                if n == 1:
                    value = symbol_at(arena, node, 0)
                    if type(value) is not int or not 0 <= value < 100:
                        raise ValueError("H source SLP contains a non-base-100 cell")
                    tile = value
                    self._source_traversal_tasks += 1
                elif not ready:
                    half = n // 2
                    slp_node = arena.nodes[node]
                    if (
                        slp_node.kind == "CONCAT"
                        and arena.nodes[slp_node.left].length == half
                        and arena.nodes[slp_node.right].length == half
                    ):
                        left, right = slp_node.left, slp_node.right
                    elif slp_node.kind == "REPEAT" and slp_node.count % 2 == 0:
                        left = arena.repeat(slp_node.child, slp_node.count // 2)
                        right = left
                    else:
                        left = fold_slp_interval(
                            arena,
                            node,
                            0,
                            half,
                            identity=arena.empty_id,
                            length=lambda index: arena.nodes[index].length,
                            full_value=lambda index, _rev: index,
                            compose=arena.concat,
                            repeat=arena.repeat,
                        )
                        right = fold_slp_interval(
                            arena,
                            node,
                            half,
                            n,
                            identity=arena.empty_id,
                            length=lambda index: arena.nodes[index].length,
                            full_value=lambda index, _rev: index,
                            compose=arena.concat,
                            repeat=arena.repeat,
                        )
                    tasks.append((node, left, right, True))
                    if key(right) not in memo:
                        tasks.append((right, 0, 0, False))
                    if key(left) not in memo:
                        tasks.append((left, 0, 0, False))
                    continue
                else:
                    tile = self.pair(memo[key(left)], memo[key(right)])
                self._scratch.acquire()
                self._slp_tile_entries += 1
                memo[key(node)] = tile
            return memo[key(root)]
        finally:
            tasks.clear()
            self._scratch.release(frame_budget, frame_budget)

    def advance_blocks_slp(
        self, arena: LedgerSLPArena, source_root: int, span: int
    ) -> int:
        """Power H on a base-100 SLP without forming an intermediate whole row.

        The SLP is LSD-first. Each demanded dyadic inlet is sliced from the
        existing CONCAT/REPEAT grammar, compiled into the *same* semantic tile
        interner as ``advance_blocks``, and its output tile is published to an
        SLP immediately. Only one bounded dyadic inlet is expanded at a time.
        The result remains a root usable by the next selected temporal power.
        """
        if (
            self._cell_action is None
            or type(arena) is not LedgerSLPArena
            or type(source_root) is not int
            or not 0 <= source_root < len(arena.nodes)
            or type(span) is not int
            or span < 1
            or span & (span - 1)
            or span > _MAX_CELLS // 2
        ):
            raise ValueError("padded H SLP advancement needs a dyadic cell action")
        cells = arena.nodes[source_root].length
        if not cells:
            raise ValueError("padded H source SLP must contain cells")
        blocks = (cells + span - 1) // span
        endpoint_cells = cells + span
        checkpoint = len(arena.nodes)
        node = arena.nodes[source_root]
        if node.kind == "REPEAT":
            unit_width = arena.nodes[node.child].length
            unit_blocks = unit_width // span
            held = 6 * unit_blocks + span.bit_length() + 32
            if (
                0 < unit_blocks <= 256
                and unit_width % span == 0
                and self._scratch.try_acquire(held, held)
            ):
                try:
                    zero = 0
                    for _ in range(span.bit_length() - 1):
                        zero = self.pair(zero, zero)
                    unit_tiles: list[int] = []
                    for start in range(0, unit_width, span):
                        if unit_width == span:
                            section = node.child
                        else:
                            section = fold_slp_interval(
                                arena,
                                node.child,
                                start,
                                start + span,
                                identity=arena.empty_id,
                                length=lambda index: arena.nodes[index].length,
                                full_value=lambda index, _reverse: index,
                                compose=arena.concat,
                                repeat=arena.repeat,
                            )
                        unit_tiles.append(self._tile_from_cell_slp(arena, section))

                    def transition(left: int, right: int) -> int:
                        return self.publish(arena, self.middle(self.pair(left, right)))

                    first = transition(zero, unit_tiles[0])
                    interior = [
                        transition(unit_tiles[index - 1], unit_tiles[index])
                        for index in range(1, unit_blocks)
                    ]
                    seam = transition(unit_tiles[-1], unit_tiles[0])
                    tail = transition(unit_tiles[-1], zero)
                    repeated = arena.repeat(
                        arena.concat_many((seam, *interior)), node.count - 1
                    )
                    output = arena.concat_many((first, *interior, repeated, tail))
                    if arena.nodes[output].length != endpoint_cells:
                        raise AssertionError("repeated H tile produced a wrong extent")
                    return output
                except BaseException as error:
                    try:
                        cleanup_all(
                            (
                                lambda: arena.rollback_unpublished_suffix(checkpoint),
                                self._discard_published,
                            )
                        )
                    except BaseException as cleanup_error:
                        raise error from cleanup_error
                    raise
                finally:
                    self._scratch.release(held, held)
        reserve = 2 * (blocks + 1) + span.bit_length() + 16
        stream_reserve = reserve + 3 * span
        stream_inlet = (
            node.kind != "REPEAT"
            and cells < _MAX_CELLS
            and cells % span != 0
            and self._scratch.try_acquire(stream_reserve, stream_reserve)
        )
        if stream_inlet:
            reserve = stream_reserve
        else:
            self._scratch.acquire(reserve, reserve)
        pieces: list[int] = []

        def interval(begin: int, end: int) -> int:
            return fold_slp_interval(
                arena,
                source_root,
                begin,
                end,
                identity=arena.empty_id,
                length=lambda node: arena.nodes[node].length,
                full_value=lambda node, _reverse: node,
                compose=arena.concat,
                repeat=arena.repeat,
            )

        try:
            symbols = (
                iter_symbols(
                    arena,
                    source_root,
                    on_task=self._count_cell_source_task,
                    reserve_task=self._scratch.acquire,
                    release_tasks=lambda count: self._scratch.release(count, count),
                )
                if stream_inlet
                else None
            )
            with closing(symbols) if symbols is not None else nullcontext():
                zero = 0
                for _ in range(span.bit_length() - 1):
                    zero = self.pair(zero, zero)
                previous = zero
                for start in range(0, (blocks + 1) * span, span):
                    current = zero
                    if start < cells:
                        if symbols is not None:
                            width = min(cells - start, span)
                            row = list(islice(symbols, width))
                            if len(row) != width or any(
                                type(cell) is not int or not 0 <= cell < 100
                                for cell in row
                            ):
                                raise ValueError(
                                    "padded H source contains an invalid inlet"
                                )
                            current = self._padded_cell_tile(row, span)
                        else:
                            section = interval(start, min(cells, start + span))
                            missing = span - arena.nodes[section].length
                            if missing:
                                section = arena.concat(
                                    section, arena.repeat(arena.terminal(0), missing)
                                )
                            current = self._tile_from_cell_slp(arena, section)
                    tile = self.middle(self.pair(previous, current))
                    pieces.append(self.publish(arena, tile))
                    previous = current
                if symbols is not None and next(symbols, None) is not None:
                    raise ValueError("padded H source exceeds its admitted extent")
                output = arena.concat_many(pieces)
                # A final non-full block was right-padded. Exclude just that
                # excess via a structural SLP interval, not a full-cell replay.
                return fold_slp_interval(
                    arena,
                    output,
                    0,
                    endpoint_cells,
                    identity=arena.empty_id,
                    length=lambda node: arena.nodes[node].length,
                    full_value=lambda node, _reverse: node,
                    compose=arena.concat,
                    repeat=arena.repeat,
                )
        except BaseException as error:
            try:
                cleanup_all(
                    (
                        lambda: arena.rollback_unpublished_suffix(checkpoint),
                        self._discard_published,
                    )
                )
            except BaseException as cleanup_error:
                raise error from cleanup_error
            raise
        finally:
            pieces.clear()
            self._scratch.release(reserve, reserve)

    def _count_cell_source_task(self, _is_node: bool) -> None:
        self._source_traversal_tasks += 1

    def publish(self, arena: LedgerSLPArena, root: int) -> int:
        """Publish the computed center into the same SLP arena transactionally."""
        checkpoint = len(arena.nodes)
        generation = arena.node_id_generation
        outputs = self._slp_published

        def key(tile: int) -> tuple[LedgerSLPArena, int, int]:
            return arena, generation, tile

        known = outputs.get(key(root))
        if known is not None:
            return known
        tasks: list[tuple[int, bool]] = []
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
            self._scratch.acquire()
            try:
                outputs[key(tile)] = slp_root
            except BaseException as error:
                self._scratch.release()
                raise error
            self._slp_published_entries += 1

        try:
            push_task(root, False)
            while tasks:
                tile, done = tasks.pop()
                retained_tasks -= 1
                self._scratch.release()
                if key(tile) in outputs:
                    continue
                node = self._tiles[tile]
                if node.level == 0:
                    remember(tile, arena.terminal(node.left))
                elif done:
                    remember(
                        tile,
                        arena.concat(outputs[key(node.left)], outputs[key(node.right)]),
                    )
                else:
                    push_task(tile, True)
                    if key(node.right) not in outputs:
                        push_task(node.right, False)
                    if key(node.left) not in outputs:
                        push_task(node.left, False)
            return outputs[key(root)]
        except BaseException as error:
            try:
                cleanup_all(
                    (
                        lambda: arena.rollback_unpublished_suffix(checkpoint),
                        self._discard_published,
                    )
                )
            except BaseException as cleanup_error:
                raise error from cleanup_error
            if isinstance(error, TemporalSquareScratchCapacityRefused):
                raise TemporalSquarePublicationFailed(
                    "scratch capacity was exhausted while publishing cone output"
                ) from error
            raise
        finally:
            release_charged_container(self._scratch, tasks.clear, retained_tasks)
