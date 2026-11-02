"""Bounded exact temporal squaring for the normalized 2rev10 carry stencil.

The helper computes a finite causal cone for ``T²``. Perfect binary tiles are
interned by their exact digit children inside one invocation, so distinct SLP
grammars for the same bounded source window share the same semantic tiles.
Those temporary tile references are never returned or retained across calls.
This is a finite successor constructor, not an all-depth period certificate.
"""

from __future__ import annotations

from collections.abc import Callable, Iterator
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

_MAX_CELLS = 4096
_MAX_T2_STEPS = 1024
_PACKED_DIAGONAL_MIN_STEPS = 64

# The exact 10-symbol spatial alphabet is tiny and immutable. Compile its
# 1,000 three-digit decisions once; temporal cones still use the same
# `stencil_cell` law, with no source- or phase-dependent cached rows.
_STENCIL_TABLE: tuple[int, ...] = tuple(
    stencil_cell(left, center, right)
    for left in range(10)
    for center in range(10)
    for right in range(10)
)


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


def _record_square_work(
    arena: LedgerSLPArena,
    stats: TemporalSquareStats,
    packed_attempt: TemporalSquareStats | None = None,
    *,
    include_semantic: bool = False,
) -> None:
    """Record one packed attempt and optional semantic fallback exactly once."""
    packed = packed_attempt
    source_visits = stats.source_traversal_tasks + (
        0 if packed is None else packed.source_traversal_tasks
    )
    rows = stats.packed_row_evaluations + (
        0 if packed is None else packed.packed_row_evaluations
    )
    output_visits = stats.packed_output_digit_visits + (
        0 if packed is None else packed.packed_output_digit_visits
    )
    operand_bits = stats.packed_row_operand_bits + (
        0 if packed is None else packed.packed_row_operand_bits
    )
    region_visits = source_visits + rows + output_visits
    if include_semantic:
        region_visits += stats.semantic_tiles - 10 + stats.canonical_tile_reuses
    ledger = arena.ledger
    ledger.bump(
        _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_SQUARE_REGION_VISITS, region_visits
    )
    ledger.bump(
        _double_reverse_keys.DOUBLE_REVERSE_PACKED_DIAGONAL_ROW_EVALUATIONS, rows
    )
    ledger.bump(
        _double_reverse_keys.DOUBLE_REVERSE_PACKED_DIAGONAL_ROW_OPERAND_BITS,
        operand_bits,
    )
    if include_semantic:
        ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_HASHLIFE_CONES, stats.temporal_cones
        )
        ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_HASHLIFE_CONE_HITS, stats.reused_cones
        )


def _packed_digit_planes(word: int, mask: int) -> tuple[int, int, int, int]:
    """Decode four stencil predicates across packed decimal nibbles."""
    a = word & mask
    b = (word >> 1) & mask
    c = (word >> 2) & mask
    h = (word >> 3) & mask
    no_a = ~a & mask
    no_b = ~b & mask
    no_c = ~c & mask
    no_h = ~h & mask

    equal_1 = no_h & no_c & no_b & a
    equal_2 = no_h & no_c & b & no_a
    equal_3 = no_h & no_c & b & a
    equal_4 = no_h & c & no_b & no_a
    equal_6 = no_h & c & b & no_a
    equal_7 = no_h & c & b & a
    equal_8 = h & no_c & no_b & no_a
    equal_9 = h & no_c & no_b & a
    return (
        equal_3 | equal_4 | equal_8 | equal_9,
        equal_1 | equal_4 | equal_6 | equal_9,
        equal_2 | equal_7,
        h | (c & (b | a)),
    )


def _packed_diagonal_middle(
    word: int,
    steps: int,
    *,
    stats: TemporalSquareStats | None = None,
) -> int:
    """Apply the finite ``T²`` diagonal to a packed 4*steps-digit window."""
    if type(word) is not int or word < 0:
        raise ValueError("packed temporal source must be a nonnegative integer")
    if type(steps) is not int or steps < 1:
        raise ValueError("packed temporal horizon must be positive")
    source_width = 4 * steps
    full_lanes = ((1 << (4 * source_width)) - 1) // 15
    if stats is not None:
        # Charge the one-time packed mask build and source-width guard at the
        # full source-lane width; small shift/divisor constants are excluded.
        stats.packed_row_operand_bits += 4 * (4 * source_width)
    if word >> (4 * source_width):
        raise ValueError("packed temporal source exceeds its admitted window")
    lanes = 0
    mod_ge3 = 0
    twice_bit2 = 0
    mod_eq2 = 0
    threshold = 0
    center_bit1 = 0
    center_bit2 = 0
    center_bit3 = 0
    center_high = 0
    left_high = 0
    right_carry = 0
    candidate = 0
    overflow = 0
    try:
        # 57 binary ops + 19 unary ops account for 133 operand widths; four
        # extra widths cover carry/overflow paths. Charge all at lane width
        # plus a four-bit guard, without bit_length calls in the row loop.
        for row_index in range(steps):
            if stats is not None:
                active_digits = source_width - 2 * row_index
                stats.packed_row_operand_bits += 137 * (4 * active_digits + 4)
                stats.packed_row_evaluations += 1
            lanes = full_lanes >> 8
            # Drop the previous row's wide planes before decoding this row;
            # the reservation below covers the peak set, not accumulated
            # temporaries across the complete horizon.
            mod_ge3 = 0
            twice_bit2 = 0
            mod_eq2 = 0
            threshold = 0
            center_bit1 = 0
            center_bit2 = 0
            center_bit3 = 0
            center_high = 0
            left_high = 0
            right_carry = 0
            candidate = 0
            overflow = 0
            mod_ge3, twice_bit2, mod_eq2, threshold = _packed_digit_planes(
                word, full_lanes
            )
            center_bit1 = (mod_ge3 >> 4) & lanes
            center_bit2 = (twice_bit2 >> 4) & lanes
            center_bit3 = (mod_eq2 >> 4) & lanes
            center_high = (threshold >> 4) & lanes
            left_high = (threshold >> 8) & lanes
            right_carry = (mod_ge3 & lanes) | ((mod_eq2 & lanes) & center_high)
            candidate = (center_bit1 << 1) | (center_bit2 << 2) | (center_bit3 << 3)
            candidate += (left_high << 1) + right_carry
            overflow = center_bit3 & left_high
            word = candidate - ((overflow << 3) | (overflow << 1))
            full_lanes = lanes
        return word
    finally:
        # Do not leave wide, request-local operands reachable from a retained
        # exception traceback after the caller releases its reservation.
        word = full_lanes = lanes = mod_ge3 = twice_bit2 = 0
        mod_eq2 = threshold = center_bit1 = center_bit2 = center_bit3 = 0
        center_high = left_high = right_carry = candidate = overflow = 0


class TemporalSquareScratchCapacityRefused(BlockContextBudgetExceeded):
    """The bounded semantic compiler refused its temporary scratch budget."""


class TemporalSquarePublicationFailed(BlockContextBudgetExceeded):
    """A completed semantic cone could not be published into the SLP arena."""


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


def _release_charged_container(
    scratch: _ScratchReservation,
    clear: Callable[[], None],
    retained: int,
) -> None:
    """Clear one charged temporary container and return its live count."""
    if retained:
        scratch.release(retained, retained)
        clear()


def _pack_source_window(
    arena: LedgerSLPArena,
    root: int,
    width: int,
    scratch: _ScratchReservation,
    on_source_task: Callable[[bool], None] | None,
    stats: TemporalSquareStats,
) -> int:
    """Read one exact SLP source window into high-digit-first nibbles."""
    packed = 0
    count = 0

    def record_task(is_node: bool) -> None:
        stats.source_traversal_tasks += 1
        if on_source_task is not None:
            on_source_task(is_node)

    symbols = iter_symbols(
        arena,
        root,
        on_task=record_task,
        reserve_task=scratch.acquire,
        release_tasks=lambda amount: scratch.release(amount, amount),
    )
    try:
        for digit in symbols:
            if type(digit) is not int or not 0 <= digit <= 9:
                raise ValueError("temporal cone source contains a nondecimal digit")
            count += 1
            if count > width:
                raise ValueError("temporal cone source exceeds its admitted window")
            packed = (packed << 4) | digit
        if count != width:
            raise ValueError("temporal cone traversal did not cover its source")
        return packed
    finally:
        try:
            symbols.close()
        finally:
            packed = 0
            count = 0


def _publish_packed_diagonal(
    arena: LedgerSLPArena,
    root: int,
    steps: int,
    scratch: _ScratchReservation,
    on_source_task: Callable[[bool], None] | None,
    stats: TemporalSquareStats,
) -> tuple[int, TemporalSquareStats]:
    """Apply and publish a bounded packed diagonal in the existing SLP arena."""
    source_width = 4 * steps
    result_width = 2 * steps
    # Reserve peak packed operands and the complete output tuple before use;
    # iter_symbols separately reserves each live traversal task.
    packed_bits = 4 * source_width
    packed_limbs = (packed_bits + 63) // 64
    workspace = 20 * packed_limbs + result_width
    scratch.acquire(workspace, workspace)
    scratch.use_exact_growth()
    packed = 0
    middle = 0
    digits: tuple[int, ...] = ()
    checkpoint = len(arena.nodes)
    try:
        packed = _pack_source_window(
            arena,
            root,
            source_width,
            scratch,
            on_source_task,
            stats,
        )
        middle = _packed_diagonal_middle(packed, steps, stats=stats)
        if middle >> (4 * result_width):
            raise AssertionError("packed diagonal exceeded its admitted output width")

        def unpack_digits() -> Iterator[int]:
            for index in range(result_width - 1, -1, -1):
                stats.packed_output_digit_visits += 1
                yield (middle >> (4 * index)) & 0xF

        digits = tuple(unpack_digits())
        for digit in digits:
            stats.packed_output_digit_visits += 1
            if digit > 9:
                raise AssertionError("packed diagonal emitted a nondecimal digit")

        try:
            # Charge the complete admitted publication input before calling
            # the arena; a failed publication retains its attempted work.
            stats.packed_output_digit_visits += result_width
            result = arena.word(digits)
        except TemporalSquareScratchCapacityRefused as error:
            raise TemporalSquarePublicationFailed(
                "scratch capacity was exhausted while publishing packed output"
            ) from error
        if arena.nodes[result].length != result_width:
            raise AssertionError("packed diagonal output has the wrong width")
        return result, stats
    except BaseException as error:
        if len(arena.nodes) > checkpoint:
            try:
                arena.rollback_unpublished_suffix(checkpoint)
            except BaseException as cleanup_error:
                raise error from cleanup_error
        raise
    finally:
        packed = 0
        middle = 0
        digits = ()
        scratch.release(workspace, workspace)


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
            # Existing chunk capacity already covers this exact live growth.
            # Keep live accounting current without another ledger dispatch.
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
                _release_charged_container(self._scratch, forest.clear, retained_forest)

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
                    # Each retained semantic cone owns an explicit scratch
                    # charge until the per-call bank is released.
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
            _release_charged_container(self._scratch, frames.clear, stack_charge)

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
    account_semantic_metrics: bool = False,
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
    if type(account_semantic_metrics) is not bool:
        raise TypeError("semantic metrics selector must be Boolean")
    if type(root) is not int or not 0 <= root < len(arena.nodes):
        raise ValueError("temporal square source root is invalid")
    arena.empty()  # Check the arena lifecycle through its public API.
    source_width = arena.nodes[root].length
    if source_width != 4 * steps or source_width > max_cells:
        raise ValueError("temporal square source is not its complete admitted halo")

    reservation = LedgerReservation(arena.ledger, scratch_owner)
    with _ScratchReservation(reservation) as scratch:
        packed_attempt: TemporalSquareStats | None = None
        if steps >= _PACKED_DIAGONAL_MIN_STEPS:
            stats = TemporalSquareStats(0, 0, 0, 0, 0)
            publication_checkpoint = len(arena.nodes)
            published_root: int | None = None
            try:
                packed_result = _publish_packed_diagonal(
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
                    # Packed work counts source visits and row transforms, not
                    # semantic Hashlife tiles.
                    try:
                        _record_square_work(arena, stats)
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
                _record_square_work(arena, packed_attempt)
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
                        _record_square_work(
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
