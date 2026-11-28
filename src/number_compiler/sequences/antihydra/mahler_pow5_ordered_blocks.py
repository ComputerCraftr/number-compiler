"""Bounded chronological ×5 actions with content-interned prefixes."""

from __future__ import annotations

from collections.abc import Generator, Iterable, Iterator
from contextlib import contextmanager, nullcontext
from dataclasses import dataclass
from sys import getsizeof, int_info
from types import TracebackType
from typing import TYPE_CHECKING, Self

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp import SLPNode
from number_compiler.arithmetic.automata.slp_interval import (
    fold_slp_dag,
    fold_slp_interval,
)
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.ordered_matrix import (
    Matrix2,
    MatrixEntries,
    ordered_decimal_continuant,
)
from number_compiler.arithmetic.fields.radix import radix_width
from number_compiler.resources.ledger import LedgerReservation, ResourceLedger
from number_compiler.resources.lifecycle import cleanup_all, cleanup_on_error

if TYPE_CHECKING:
    from number_compiler.arithmetic.automata.carry_spacetime_trace import (
        Pow5SpatialTrace,
    )
    from number_compiler.sequences.antihydra.mahler_cf_reciprocal_tile import (
        ReciprocalTile,
    )

_MAX_EXPONENT = 4096
_MAX_BLOCK_ROWS = 64
_MAX_SPATIAL_WIDTH = 32
# 5**8 is the last whole row with a six-column settled action.
_SETTLED_SPATIAL_END = 8
_SPATIAL_DIGIT_BITS = 24
_ASCII_DECIMAL = bytes(range(48, 58))
_NUMERIC_TO_ASCII = bytes.maketrans(bytes(range(10)), _ASCII_DECIMAL)

# Include the immutable native bank and bounded temporary endpoint tuples.
_PREFIX_INDEX_WORDS = (getsizeof(b"") + 32 * 17 + 7) // 8 + 32
_CLIP_LETTERS = 16


def _row_prefix_words(rows: int, coefficients: int) -> int:
    digits = (4 * coefficients + int_info.bits_per_digit - 1) // int_info.bits_per_digit
    matrix_bytes = getsizeof((0, 0, 0, 0)) + 4 * (
        getsizeof(0) + digits * int_info.sizeof_digit
    )
    # Include both prefix tuples during construction, including their references.
    prefix_bytes = 2 * (getsizeof(()) + rows * (getsizeof((0,)) - getsizeof(())))
    return (prefix_bytes + rows * matrix_bytes + 7) // 8


# The replaced action and its replacement can coexist during publication.
_CLIP_WORDS = _row_prefix_words(2, _CLIP_LETTERS) + 2 * (
    (getsizeof((0, 0, 0, ())) + 3 * getsizeof(0) + 7) // 8
)


@dataclass(frozen=True, slots=True)
class Pow5OrderedBlock:
    """A source-issued chronological product with exact prefix access."""

    _owner: Pow5OrderedBlockSource
    _epoch: int

    @property
    def coefficient_count(self) -> int:
        return self._owner.checked_count(self, self._epoch)

    @property
    def product(self) -> Matrix2:
        return self._owner.checked_product(self, self._epoch)

    def prefix(self, length: int) -> Matrix2:
        """Return the first length coefficients in physical order."""
        return self.segment(0, length)

    def segment(self, start: int, length: int) -> Matrix2:
        """Return a source-authenticated interval in physical order."""
        return self._owner.checked_segment(self, self._epoch, start, length)


def _pack_settled_decimal(value: int) -> int:
    """Encode a source-qualified settled value into decimal lanes."""
    packed = 0
    shift = 0
    while value:
        value, digit = divmod(value, 10)
        packed |= digit << shift
        shift += 24
    return packed


def _reciprocal_window(
    quotient: int, width: int, threshold: int, start: int, rows: int, cap: int
) -> tuple[tuple[int, ...], int, int]:
    """Choose significant widths and the exact final cut from the first inlet."""
    place = threshold // 10
    if not place <= quotient < threshold:
        raise ArithmeticError("power-of-five width admission failed")
    if rows == 1 or cap <= width - start:
        count = min(width - start, cap)
        end = start + count
        return (width,), count, 0 if end == width else end

    # For t=1,2,3 the extra decade starts at input 2,4,8 times
    # the leading place respectively. At t=4 it starts at 8/5.
    widths = [width, width + (quotient >= 2 * place)]
    if rows >= 3:
        widths.append(width + 1 + (quotient >= 4 * place))
    if rows >= 4:
        widths.append(width + 2 + (quotient >= 8 * place))
    if rows == 5:
        widths.append(width + 2 + (5 * quotient >= 8 * place))
    total = sum(widths) - start
    if cap >= total:
        return tuple(widths), total, 0
    cut = cap + start
    for index, selected in enumerate(widths):
        if cut <= selected:
            return tuple(widths[: index + 1]), cap, 0 if cut == selected else cut
        cut -= selected
    raise ArithmeticError("reciprocal cut outside admitted widths")


class Pow5OrderedBlockSource:
    """Publish bounded ordered actions from one canonical ×5 source."""

    def __init__(
        self,
        ledger: ResourceLedger,
        *,
        shared_cache: bool = True,
        spatial: bool = False,
        reciprocal: bool = False,
    ) -> None:
        if (
            type(ledger) is not ResourceLedger
            or type(shared_cache) is not bool
            or type(spatial) is not bool
            or type(reciprocal) is not bool
            or spatial
            and reciprocal
        ):
            raise TypeError(
                "ordered CF source requires a ledger and Boolean cache policy"
            )
        self.ledger = ledger
        self.shared_cache = shared_cache
        self._reciprocal = reciprocal
        self._tile: ReciprocalTile | None = None
        self._tile_binding: (
            tuple[
                ReciprocalTile,
                int,
                tuple[int, ...],
                int,
                int,
                tuple[int, int, int, int],
                int | None,
                int | None,
                tuple[int, tuple[int, int, int, int]] | None,
                bool,
                bytes | None,
                bool,
                tuple[MatrixEntries, ...],
            ]
            | None
        ) = None
        self._owner = ledger.register(
            f"mahler-cf-ordered-{ledger.owner_count}", "ordered-cf-source"
        )
        self._exponent: int = 0
        self._value: int = 1
        self._offset = 0
        self._width = 1
        self._threshold = 10
        self._source_binding: tuple[int, int, int, int, int] | None = (1, 0, 0, 1, 10)
        self._epoch = 0
        self._closed = False
        self._block: Pow5OrderedBlock | None = None
        self._clip: tuple[int, int, int, MatrixEntries] | None = None
        self._arenas: tuple[LedgerSLPArena, LedgerSLPArena] | None = None
        if not spatial and not reciprocal:
            prefix = f"mahler-cf-block-{ledger.owner_count}"
            first = LedgerSLPArena(ledger, prefix + "-a", "ordered-cf")
            with cleanup_on_error(first.dispose):
                second = LedgerSLPArena(ledger, prefix + "-b", "ordered-cf")
            self._arenas = (first, second)
        self._active = 0
        self._root = 0
        self._values: dict[int, Matrix2] = {}
        self._arena_binding: tuple[LedgerSLPArena, int, int, SLPNode] | None = None
        self._reservation: LedgerReservation | None = None
        self._pending_reservation: LedgerReservation | None = None
        self._spatial_trace: Pow5SpatialTrace | None = None
        self._spatial_value = False
        self._word: bytes | None = None
        self._word_product: Matrix2 | None = None
        if spatial:
            from number_compiler.arithmetic.automata.carry_spacetime_trace import (
                Pow5SpatialTrace,
            )

            with cleanup_on_error(self.close):
                self._spatial_trace = Pow5SpatialTrace(
                    ledger, shared_cache=shared_cache
                )

    def __enter__(self) -> Self:
        if self._closed:
            raise RuntimeError("ordered CF source is closed")
        return self

    def __exit__(
        self,
        _exc_type: type[BaseException] | None,
        _exc: BaseException | None,
        _traceback: TracebackType | None,
    ) -> None:
        self.close()

    def close(self) -> None:
        self._closed = True
        self._block = None
        self._clip = None
        self._values.clear()
        self._arena_binding = None
        self._value = 0
        self._word = None
        self._word_product = None
        self._tile = None
        self._tile_binding = None
        self._source_binding = None
        arenas = self._arenas
        cleanups = [] if arenas is None else [arenas[0].dispose, arenas[1].dispose]
        if self._spatial_trace is not None:
            cleanups.append(self._spatial_trace.close)
        if self._reservation is not None:
            cleanups.append(self._reservation.close)
        if self._pending_reservation is not None:
            cleanups.append(self._pending_reservation.close)
        cleanup_all(cleanups)
        self._reservation = None
        self._pending_reservation = None

    def _authenticate(self, block: Pow5OrderedBlock, epoch: int) -> None:
        if self._closed:
            raise RuntimeError("ordered CF source is closed")
        if block is not self._block or epoch != self._epoch:
            raise ValueError("ordered CF block is stale or foreign")
        if self._arena_binding is not None:
            arena, generation, root, root_node = self._arena_binding
            if (
                self._arenas is None
                or self._arenas[self._active] is not arena
                or self._root != root
                or arena.node_id_generation != generation
                or arena.node_storage_poisoned
                or not 0 <= root < len(arena.nodes)
                or arena.nodes[root] is not root_node
            ):
                raise ValueError("ordered CF block source arena is stale")
        if self._tile is not None or self._tile_binding is not None or self._reciprocal:
            tile = self._tile
            binding = self._tile_binding
            if (
                tile is None
                or binding is None
                or tile is not binding[0]
                or not tile.sealed
                or (
                    tile,
                    tile.quotient,
                    tile.widths,
                    tile.start,
                    tile.length,
                    tile.product.entries,
                    tile.product.modulus,
                    tile.first_exponent,
                    tile.first_row_prefix,
                    tile.index_last,
                    tile.last_prefixes,
                    tile.retain_row_prefixes,
                    tile.row_prefixes,
                )
                != binding
            ):
                raise ValueError("reciprocal CF block source binding changed")

    def checked_count(self, block: Pow5OrderedBlock, epoch: int) -> int:
        self._authenticate(block, epoch)
        if self._tile is not None:
            return self._tile.length
        if self._word is not None:
            return len(self._word)
        assert self._arenas is not None
        return self._arenas[self._active].nodes[self._root].length

    def checked_product(self, block: Pow5OrderedBlock, epoch: int) -> Matrix2:
        self._authenticate(block, epoch)
        if self._tile is not None:
            return self._tile.product
        if self._word_product is not None:
            return self._word_product
        return self._values[self._root]

    def checked_segment(
        self, block: Pow5OrderedBlock, epoch: int, start: int, length: int
    ) -> Matrix2:
        count = self.checked_count(block, epoch)
        require_integer(start, "ordered block segment start", 0, count)
        require_integer(length, "ordered block segment length", 0, count - start)
        if self._tile is not None:
            if start == 0 and length == count:
                return self._tile.product
            if self._reciprocal and self.shared_cache and 0 < length <= _CLIP_LETTERS:
                return self._reciprocal_clip(self._tile, epoch, start, length)
            return self._tile.segment(start, length)
        if self._word is not None:
            if start == 0 and length == count:
                assert self._word_product is not None
                return self._word_product
            return ordered_decimal_continuant(self._word[start : start + length])
        assert self._arenas is not None
        arena = self._arenas[self._active]
        if length == 0:
            return Matrix2.identity()
        if start == 0 and length == count:
            return self._values[self._root]
        values = self._values if self.shared_cache else {}

        def full_value(node: int, _reverse: bool) -> Matrix2:
            value = values.get(node)
            if value is None:
                # Bypass can rebuild the selected subtrees in this call.
                # The remainder of the root has no authority on this cut.
                values.update(self._compile(arena, node))
                value = values[node]
            return value

        return fold_slp_interval(
            arena,
            self._root,
            start,
            start + length,
            identity=Matrix2.identity(),
            length=lambda node: arena.nodes[node].length,
            full_value=full_value,
            compose=lambda left, right: left.multiply(right),
            repeat=lambda value, count: value if count == 1 else value.power(count),
        )

    def _reciprocal_clip(
        self, tile: ReciprocalTile, epoch: int, start: int, length: int
    ) -> Matrix2:
        # checked_segment authenticated this block and its MSD-first source.
        previous = self._clip
        if previous is not None and previous[:3] == (epoch, start, length):
            return Matrix2(previous[3])
        reservation = self._reservation
        assert reservation is not None
        if previous is None:
            try:
                reservation.reserve(nodes=_CLIP_WORDS)
            except BlockContextBudgetExceeded:
                return tile.segment(start, length)
        rollback = (
            cleanup_on_error(lambda: reservation.release(nodes=_CLIP_WORDS))
            if previous is None
            else nullcontext()
        )
        with rollback:
            result = tile.segment(start, length)
            # Keep only the exact integer entries. Returned Matrix2 objects
            # cannot retarget the retained response.
            self._clip = (epoch, start, length, result.entries)
        return result

    @staticmethod
    def _compile(arena: LedgerSLPArena, root: int) -> dict[int, Matrix2]:
        return fold_slp_dag(
            arena,
            root,
            empty_value=Matrix2.identity(),
            terminal_value=lambda digit: Matrix2.digit(digit + 1),
            concatenate=lambda left, right: left.multiply(right),
            repeat=lambda action, count: action.power(count),
        )

    @staticmethod
    def _geometric_rows(
        value: int, rows: int, lane_width: int
    ) -> Iterator[tuple[int, int]]:
        base = 10**lane_width
        factor = 5 * base
        packed = 5 * value * ((factor**rows - 1) // (factor - 1))
        for _ in range(rows):
            packed, lane = divmod(packed, base)
            yield lane, radix_width(lane, 10)
        if packed:
            raise ArithmeticError("geometric ×5 lanes did not close")

    @contextmanager
    def _reserve_candidate(
        self, node_bound: int
    ) -> Generator[LedgerReservation, None, None]:
        reservation = LedgerReservation(self.ledger, self._owner)
        self._pending_reservation = reservation

        def rollback() -> None:
            try:
                reservation.close()
            except BaseException:
                self._closed = True
                self._block = None
                raise
            self._pending_reservation = None

        with cleanup_on_error(rollback):
            try:
                reservation.reserve(nodes=node_bound)
            except BlockContextBudgetExceeded:
                if self._clip is None:
                    raise
                # Optional reuse may not crowd out an exact successor block.
                active = self._reservation
                assert active is not None
                with cleanup_on_error(self.close):
                    self._clip = None
                    active.release(nodes=_CLIP_WORDS)
                reservation.reserve(nodes=node_bound)
            yield reservation

    def _next_reciprocal(
        self, max_rows: int, max_coefficients: int
    ) -> Pow5OrderedBlock:
        from number_compiler.sequences.antihydra.mahler_cf_reciprocal_tile import (
            ReciprocalTile,
            native_prefix_available,
            reciprocal_indexed_columns,
        )

        if (
            type(self._value) is not int
            or type(self._exponent) is not int
            or type(self._offset) is not int
            or (self._value, self._exponent, self._offset, self._width, self._threshold)
            != self._source_binding
        ):
            raise ValueError("reciprocal CF source cursor binding changed")
        first = self._exponent if self._offset else self._exponent + 1
        source = self._value
        if self._spatial_trace is not None:
            if self._spatial_value or source != 5**self._exponent:
                raise ValueError("settled spatial source cursor binding changed")
            rows = min(max_rows, 5, _SETTLED_SPATIAL_END + 1 - first)
            estimated = min(
                max_coefficients, max_rows * (self._exponent + max_rows + 1)
            )
            bits = 4 * (self._exponent + max_rows + 1) * max_rows
            node_bound = 128 + estimated + 8 * (bits + 63) // 64
        else:
            rows = min(max_rows, 4, _MAX_EXPONENT - first + 1)
            estimated = min(max_coefficients, rows * (first + rows + 1))
            bits = 4 * (first + rows) + 64 * estimated
            node_bound = 128 + 8 * ((bits + 63) // 64)

        # Predict only a complete two-row window near the measured width.
        # Capped ledgers retain their existing admission and optional fallback.
        staged_index = (
            self.ledger.max_nodes is None
            and self._offset == 0
            and max_rows == 2
            and 26 <= self._width <= 32
            and max_coefficients >= 2 * (self._width + 2)
            and native_prefix_available()
        )
        if staged_index:
            node_bound += _PREFIX_INDEX_WORDS
        with self._reserve_candidate(node_bound) as reservation:
            start = self._offset
            quotient = source if start else 5 * source
            value = quotient
            width = self._width
            threshold = self._threshold
            if value >= threshold:
                width += 1
                threshold *= 10
            widths, length, offset = _reciprocal_window(
                quotient, width, threshold, start, rows, max_coefficients
            )
            ticks = len(widths) - 1
            last = first + ticks
            value = quotient * (1, 5, 25, 125, 625)[ticks] if ticks else quotient
            threshold *= 10 ** (widths[-1] - width)
            width = widths[-1]
            index_last = (
                len(widths) == 2
                and reciprocal_indexed_columns(widths[-1]) > 0
                and length == sum(widths) - start
                and (staged_index or native_prefix_available())
            )
            if staged_index and not index_last:
                reservation.release(nodes=_PREFIX_INDEX_WORDS)
            elif index_last and not staged_index:
                try:
                    reservation.reserve(nodes=_PREFIX_INDEX_WORDS)
                except BlockContextBudgetExceeded:
                    index_last = False
            retain_rows = (
                len(widths) >= 3
                and start == 0
                and length == sum(widths)
                and 19 <= widths[0] <= widths[-1] <= 32
                and native_prefix_available()
            )
            if retain_rows:
                try:
                    reservation.reserve(nodes=_row_prefix_words(len(widths), length))
                except BlockContextBudgetExceeded:
                    retain_rows = False
            tile = ReciprocalTile(
                quotient, widths, start, length, first, index_last, retain_rows
            )
            block = Pow5OrderedBlock(self, self._epoch + 1)

            def revoke() -> None:
                self._closed = True
                self._block = None
                self._tile = None
                self._tile_binding = None
                self._source_binding = None
                self._value = 0

            with cleanup_on_error(revoke):
                self._block = None
                self._clip = None
                if self._reservation is not None:
                    self._reservation.close()
                self._reservation = reservation
                self._pending_reservation = None
                self._tile = tile
                self._tile_binding = (
                    tile,
                    tile.quotient,
                    tile.widths,
                    tile.start,
                    tile.length,
                    tile.product.entries,
                    tile.product.modulus,
                    tile.first_exponent,
                    tile.first_row_prefix,
                    tile.index_last,
                    tile.last_prefixes,
                    tile.retain_row_prefixes,
                    tile.row_prefixes,
                )
                self._block = block
                self._spatial_value = (
                    self._spatial_trace is not None
                    and last == _SETTLED_SPATIAL_END
                    and offset == 0
                )
                self._value = (
                    _pack_settled_decimal(value) if self._spatial_value else value
                )
                self._exponent = last
                self._offset = offset
                self._width = width
                self._threshold = threshold
                self._source_binding = (self._value, last, offset, width, threshold)
                self._epoch += 1
        return block

    def next_block(self, max_rows: int, max_coefficients: int) -> Pow5OrderedBlock:
        """Issue a bounded block, preserving the prior source on admission failure."""
        if self._closed:
            raise RuntimeError("ordered CF source is closed")
        if self._block is not None and self._arena_binding is not None:
            self._authenticate(self._block, self._epoch)
        require_integer(max_rows, "ordered block row bound", 1, _MAX_BLOCK_ROWS)
        require_integer(max_coefficients, "ordered coefficient bound", 1, 100000)
        if self._exponent >= _MAX_EXPONENT and self._offset == 0:
            raise StopIteration("power-of-five source exponent exceeds 4096")

        if self._reciprocal:
            return self._next_reciprocal(max_rows, max_coefficients)
        if self._spatial_trace is not None and (
            self._exponent < _SETTLED_SPATIAL_END
            or self._offset
            and self._exponent == _SETTLED_SPATIAL_END
        ):
            return self._next_reciprocal(max_rows, max_coefficients)

        # The same reservation covers the packed lanes, content-action map,
        # and the transient interval traversal for any prefix of this block.
        estimated = min(max_coefficients, max_rows * (self._exponent + max_rows + 1))
        bits = 4 * (self._exponent + max_rows + 1) * max_rows
        arenas = self._arenas
        if arenas is None:
            # Reserve one 64-bit unit per coefficient for the staged byte
            # word, a selected slice, and the simultaneous continuant limbs.
            # Each positive digit action grows an entry by a factor at most 11.
            node_bound = 128 + estimated
        else:
            node_bound = 128 + 12 * estimated
            node_bound += 2 * estimated * estimated.bit_length() // 64
        node_bound += 8 * (bits + 63) // 64

        with self._reserve_candidate(node_bound) as reservation:
            spare = 1 - self._active
            arena = arenas[spare] if arenas is not None else None

            def rollback_candidate() -> None:
                if arena is None:
                    return
                try:
                    arena.rollback_unpublished_suffix(1)
                except BaseException:
                    self._closed = True
                    self._block = None
                    raise

            with cleanup_on_error(rollback_candidate):
                value = self._value
                exponent = self._exponent
                offset = self._offset
                remaining = max_coefficients
                slots = max_rows
                forest: list[tuple[int, int]] = []
                digit_bytes = bytearray()
                spatial_value = self._spatial_value
                if spatial_value:
                    width = (
                        value.bit_length() + _SPATIAL_DIGIT_BITS - 1
                    ) // _SPATIAL_DIGIT_BITS
                    if width > _MAX_SPATIAL_WIDTH:
                        numeric_digits = value.to_bytes(3 * width, "big")[2::3]
                        value = int(numeric_digits.translate(_NUMERIC_TO_ASCII))
                        spatial_value = False
                else:
                    width = radix_width(value, 10)

                def push_digit(digit: int) -> None:
                    assert arena is not None
                    node = arena.terminal(digit)
                    level = 0
                    while forest and forest[-1][0] == level:
                        _, left = forest.pop()
                        node = arena.concat(left, node)
                        level += 1
                    forest.append((level, node))

                def emit(row: int, start: int, count: int, width: int) -> None:
                    if spatial_value:
                        if count < width:
                            row >>= _SPATIAL_DIGIT_BITS * (width - start - count)
                            row &= (1 << (_SPATIAL_DIGIT_BITS * count)) - 1
                        digits = row.to_bytes(3 * count, "big")[2::3]
                        digit_bytes.extend(digits)
                        return
                    place = 10 ** (width - start - 1)
                    row %= 10 ** (width - start)
                    for _ in range(count):
                        digit, row = divmod(row, place)
                        if arena is None:
                            digit_bytes.append(digit)
                        else:
                            push_digit(digit)
                        place //= 10

                if offset:
                    size = min(width - offset, remaining)
                    emit(value, offset, size, width)
                    remaining -= size
                    slots -= 1
                    offset += size
                    if offset == width:
                        offset = 0

                if remaining and slots and offset == 0 and exponent < _MAX_EXPONENT:
                    rows = min(slots, _MAX_EXPONENT - exponent)
                    if spatial_value:
                        rows = min(rows, 4)
                    # Each lane is at most one decimal digit wider per tick.
                    lane_width = width + rows
                    if remaining < rows * lane_width:
                        rows = max(1, min(rows, remaining // lane_width))
                        lane_width = width + rows
                    outputs: Iterable[tuple[int, int]]
                    if spatial_value:
                        assert self._spatial_trace is not None
                        outputs = self._spatial_trace.issue(value, width, rows)
                    else:
                        outputs = self._geometric_rows(value, rows, lane_width)
                    for lane, width in outputs:
                        size = min(width, remaining)
                        emit(lane, 0, size, width)
                        remaining -= size
                        exponent += 1
                        value = lane
                        offset = 0 if size == width else size
                        if remaining == 0:
                            break

                if not forest and not digit_bytes:
                    raise StopIteration("power-of-five source exponent exceeds 4096")
                word = None
                word_product = None
                values: dict[int, Matrix2] = {}
                if arena is None:
                    root = 0
                    word = bytes(digit_bytes)
                    word_product = ordered_decimal_continuant(word)
                else:
                    _, root = forest[0]
                    for _, node in forest[1:]:
                        root = arena.concat(root, node)
                    values = self._compile(arena, root)
                block = Pow5OrderedBlock(self, self._epoch + 1)
                old_arena, old_reservation = (
                    arenas[self._active] if arenas is not None else None,
                    self._reservation,
                )

                def revoke_failed_publication() -> None:
                    self._closed = True
                    self._block = None
                    self._word = None
                    self._word_product = None
                    self._values.clear()
                    self._arena_binding = None
                    self._value = 0

                with cleanup_on_error(revoke_failed_publication):
                    self._block = None
                    self._values.clear()
                    if old_reservation is not None:
                        if old_arena is None:
                            old_reservation.close()
                        else:
                            cleanup_all(
                                (
                                    lambda: old_arena.rollback_unpublished_suffix(1),
                                    old_reservation.close,
                                )
                            )
                    self._active = spare
                    self._reservation = reservation
                    self._root = root
                    self._arena_binding = (
                        None
                        if arena is None
                        else (arena, arena.node_id_generation, root, arena.nodes[root])
                    )
                    self._values = (
                        values
                        if self.shared_cache or arena is None
                        else {root: values[root]}
                    )
                    self._tile = None
                    self._tile_binding = None
                    self._word = word
                    self._word_product = word_product
                    self._block = block
                    self._exponent = exponent
                    self._value = value
                    self._spatial_value = spatial_value
                    self._offset = offset
                    self._epoch += 1
                    self._pending_reservation = None
        return block
