"""Budgeted packed diagonal for exact finite 2rev10 temporal transfer."""

from __future__ import annotations

from collections.abc import Callable, Iterator, Sequence
from dataclasses import dataclass
from typing import Literal, overload

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp_walks import iter_symbols
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.resources.metric_keys import (
    double_reverse as _double_reverse_keys,
)
from number_compiler.resources.owned_memo import LedgerReservation

PACKED_DIAGONAL_MIN_STEPS = 64


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


class _CountedDigits(Sequence[int]):
    """Own clearable output digits and charge each publisher read."""

    __slots__ = ("_digits", "_stats")

    def __init__(self, stats: TemporalSquareStats) -> None:
        self._digits: list[int] = []
        self._stats = stats

    def append(self, digit: int) -> None:
        self._digits.append(digit)

    def clear(self) -> None:
        self._digits.clear()

    def __len__(self) -> int:
        return len(self._digits)

    @overload
    def __getitem__(self, index: int) -> int: ...

    @overload
    def __getitem__(self, index: slice) -> tuple[int, ...]: ...

    def __getitem__(self, index: int | slice) -> int | tuple[int, ...]:
        if isinstance(index, slice):
            sliced = tuple(self._digits[index])
            self._stats.packed_output_digit_visits += len(sliced)
            return sliced
        self._stats.packed_output_digit_visits += 1
        return self._digits[index]

    def __iter__(self) -> Iterator[int]:
        index = 0
        while index < len(self._digits):
            digit = self._digits[index]
            self._stats.packed_output_digit_visits += 1
            yield digit
            index += 1


def record_square_work(
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


def packed_digit_predicates(word: int, mask: int) -> tuple[int, int, int, int]:
    """Decode the four exact threshold predicates without digit equality rows.

    Every nibble is already certified to be decimal (0..9).  On this
    admitted alphabet the Boolean expressions are strictly smaller than the
    previous eight equality masks.  These predicates are the **same**
    two-step stencil outputs; no alternative carry publisher is introduced.
    """
    a = word & mask
    b = (word >> 1) & mask
    c = (word >> 2) & mask
    h = (word >> 3) & mask
    return (
        h | (c & ~a & ~b) | (a & b & ~c),
        (a & ~b & ~c) | (c & ~a),
        b & ~(a ^ c),
        h | (c & (a | b)),
    )


def packed_diagonal_middle(
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
        # Charge mask construction at full lane width.
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
        # Charge 137 lane widths per row, including carry and overflow paths.
        for row_index in range(steps):
            if stats is not None:
                active_digits = source_width - 2 * row_index
                stats.packed_row_operand_bits += 137 * (4 * active_digits + 4)
                stats.packed_row_evaluations += 1
            lanes = full_lanes >> 8
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
            mod_ge3, twice_bit2, mod_eq2, threshold = packed_digit_predicates(
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
        # Clear large operands from retained failure tracebacks.
        word = full_lanes = lanes = mod_ge3 = twice_bit2 = 0
        mod_eq2 = threshold = center_bit1 = center_bit2 = center_bit3 = 0
        center_high = left_high = right_carry = candidate = overflow = 0


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
        scratch.release(retained, retained)
        clear()


def pack_source_window(
    arena: LedgerSLPArena,
    root: int,
    width: int,
    scratch: TemporalSquareScratchReservation,
    on_source_task: Callable[[bool], None] | None,
    stats: TemporalSquareStats,
) -> int:
    """Read one exact SLP source window into high-digit-first nibbles."""
    count = 0
    # A spatial word is two packed decimal nibbles per byte. Allocate one
    # charged buffer and hand the conversion to CPython's C-level big-int
    # constructor, instead of creating O(width) ever-larger big integers.
    # This is an exact source-word packing optimization, not another stencil.
    buffer_bytes = (width + 1) // 2
    leading_nibble = width & 1
    scratch.acquire(buffer_bytes, buffer_bytes)
    packed_bytes: bytearray | None = None
    try:
        packed_bytes = bytearray(buffer_bytes)

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
                if count >= width:
                    raise ValueError("temporal cone source exceeds its admitted window")
                nibble_index = count + leading_nibble
                index = nibble_index >> 1
                if nibble_index & 1:
                    packed_bytes[index] |= digit
                else:
                    packed_bytes[index] = digit << 4
                count += 1
            if count != width:
                raise ValueError("temporal cone traversal did not cover its source")
            # An odd-width word uses only the low nibble of its first byte.
            return int.from_bytes(packed_bytes, "big")
        finally:
            symbols.close()
    finally:
        if packed_bytes is not None:
            packed_bytes.clear()
        scratch.release(buffer_bytes, buffer_bytes)


def publish_packed_diagonal(
    arena: LedgerSLPArena,
    root: int,
    steps: int,
    scratch: TemporalSquareScratchReservation,
    on_source_task: Callable[[bool], None] | None,
    stats: TemporalSquareStats,
) -> tuple[int, TemporalSquareStats]:
    """Apply and publish a bounded packed diagonal in the existing SLP arena."""
    source_width = 4 * steps
    result_width = 2 * steps
    # Reserve packed operands and output; traversal tasks reserve separately.
    packed_bits = 4 * source_width
    packed_limbs = (packed_bits + 63) // 64
    workspace = 20 * packed_limbs + result_width
    scratch.acquire(workspace, workspace)
    scratch.use_exact_growth()
    packed = 0
    middle = 0
    digits = _CountedDigits(stats)
    checkpoint = len(arena.nodes)
    try:
        packed = pack_source_window(
            arena,
            root,
            source_width,
            scratch,
            on_source_task,
            stats,
        )
        middle = packed_diagonal_middle(packed, steps, stats=stats)
        if middle >> (4 * result_width):
            raise AssertionError("packed diagonal exceeded its admitted output width")

        for index in range(result_width - 1, -1, -1):
            stats.packed_output_digit_visits += 1
            digits.append((middle >> (4 * index)) & 0xF)
        for digit in digits:
            if digit > 9:
                raise AssertionError("packed diagonal emitted a nondecimal digit")

        try:
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
        digits.clear()
        scratch.release(workspace, workspace)


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


__all__ = [
    "PACKED_DIAGONAL_MIN_STEPS",
    "TemporalSquarePublicationFailed",
    "TemporalSquareScratchCapacityRefused",
    "TemporalSquareScratchReservation",
    "TemporalSquareStats",
    "publish_packed_diagonal",
    "record_square_work",
    "release_charged_container",
]
