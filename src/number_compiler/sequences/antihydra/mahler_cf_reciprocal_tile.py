"""Source-bound reciprocal row intervals and ordered decimal actions."""

import os
from dataclasses import dataclass, field
from struct import Struct
from typing import Protocol, cast

from number_compiler.arithmetic.fields.ordered_matrix import (
    Matrix2,
    MatrixEntries,
    append_decimal_value,
    multiply_entries,
)
from number_compiler.kernels import native_continuant_module
from number_compiler.sequences.antihydra.mahler_cf_low_period import (
    SETTLED_TENS_ACTION,
    settled_low_action,
)


class _NativeContinuant(Protocol):
    def ordered_product(self, value: int, width: int) -> tuple[int, int, int, int]: ...

    def indexed_pair(
        self, upper: int, lower: int, width: int, next_width: int, phase: int
    ) -> tuple[MatrixEntries, MatrixEntries, bytes] | None: ...

    def settled_four(
        self, value: int, widths: tuple[int, ...], phase: int
    ) -> tuple[MatrixEntries, MatrixEntries] | None: ...

    def ordered_prefix_bank(self, value: int, width: int) -> bytes: ...


_PREFIX = Struct("=4Q")
_SETTLED_COLUMNS = 6


def reciprocal_indexed_columns(width: int) -> int:
    """Number of prefix columns retained by the bounded reciprocal bank."""
    if 14 <= width <= 22:
        return width - _SETTLED_COLUMNS
    if 28 <= width <= 32:
        return width // 2
    return 0


def _adjugate(entries: MatrixEntries, length: int) -> MatrixEntries:
    a, b, c, d = entries
    return (-d, b, c, -a) if length & 1 else (d, -b, -c, a)


def _indexed_interval(prefixes: bytes, start: int, length: int) -> MatrixEntries:
    end = _PREFIX.unpack_from(prefixes, (start + length) * _PREFIX.size)
    if start == 0:
        return end
    first = _PREFIX.unpack_from(prefixes, start * _PREFIX.size)
    return multiply_entries(_adjugate(first, start), end)


def _native_continuant() -> _NativeContinuant | None:
    return cast(_NativeContinuant | None, native_continuant_module())


def native_prefix_available() -> bool:
    """Check the optional immutable native prefix bank before admission."""
    if os.environ.get("NUMBER_COMPILER_ENABLE_CF_CONTINUANT") != "1":
        return False
    native = _native_continuant()
    return callable(getattr(native, "ordered_prefix_bank", None))


def reciprocal_row_interval(q: int, t: int, width: int, start: int, count: int) -> int:
    """Restrict the lifted source at its moving cut before digit decoding."""
    skip = width - start - count
    if skip >= t:
        # Cancel 5**t against the discarded decimal places before multiplying.
        # The binary cut keeps the carry into the requested upper band.
        upper: int = (q >> t) // 10 ** (skip - t)
    else:
        upper = (q * 5 ** (t - skip)) >> skip
    # 2**83 < 10**25. This conservative bit bound proves that the
    # leading cut already fits, including zero-padded physical heads.
    if start == 0 and upper >= 0 and upper.bit_length() <= (83 * count) // 25:
        return upper
    modulus: int = 10**count
    return upper % modulus


@dataclass(frozen=True, slots=True)
class ReciprocalTile:
    """One original source and a demanded row-major interval."""

    quotient: int
    widths: tuple[int, ...]
    start: int
    length: int
    first_exponent: int | None = None
    index_last: bool = False
    retain_row_prefixes: bool = False
    product: Matrix2 = field(init=False)
    # This bounded response belongs to the issued tile, never to a shared
    # semantic key. The owner's staging reservation covers its integer limbs.
    first_row_prefix: tuple[int, MatrixEntries] | None = field(init=False)
    last_prefixes: bytes | None = field(init=False, default=None)
    row_prefixes: tuple[MatrixEntries, ...] = field(init=False, default=())
    _building: bool = field(init=False, default=True, repr=False)

    def __post_init__(self) -> None:
        object.__setattr__(self, "first_row_prefix", None)
        object.__setattr__(
            self, "_building", len(self.widths) == 2 or self.retain_row_prefixes
        )
        if (
            self.index_last
            and len(self.widths) == 2
            and 28 <= self.widths[1] <= 32
            and self.widths[1] - 1 <= self.widths[0] <= self.widths[1]
            and self.start == 0
            and self.length == sum(self.widths)
            and self.first_exponent is not None
            and self.first_exponent >= 6
            and os.environ.get("NUMBER_COMPILER_ENABLE_CF_CONTINUANT") == "1"
        ):
            indexed_emit = getattr(_native_continuant(), "indexed_pair", None)
            if indexed_emit is not None:
                width, next_width = self.widths
                indexed = next_width // 2
                upper, lower = divmod(self.quotient, 10 ** (next_width - indexed))
                response = indexed_emit(
                    upper, lower, width, next_width, (self.first_exponent - 6) % 16
                )
                if response is not None:
                    first, second, prefixes = response
                    if (
                        type(prefixes) is not bytes
                        or len(prefixes) != (indexed + 1) * _PREFIX.size
                    ):
                        raise RuntimeError("native CF prefix bank has invalid bounds")
                    object.__setattr__(self, "first_row_prefix", (width, first))
                    object.__setattr__(self, "last_prefixes", prefixes)
                    object.__setattr__(
                        self, "product", Matrix2(multiply_entries(first, second))
                    )
                    object.__setattr__(self, "_building", False)
                    return
        if (
            len(self.widths) == 4
            and 7 <= self.widths[0] <= self.widths[-1] <= 18
            and self.start == 0
            and self.length == sum(self.widths)
            and self.first_exponent is not None
            and self.first_exponent >= 6
            and os.environ.get("NUMBER_COMPILER_ENABLE_CF_CONTINUANT") == "1"
        ):
            emit = getattr(_native_continuant(), "settled_four", None)
            if emit is not None:
                pairs = emit(self.quotient, self.widths, (self.first_exponent - 6) % 16)
                if pairs is not None:
                    object.__setattr__(
                        self, "product", Matrix2(multiply_entries(pairs[0], pairs[1]))
                    )
                    return
        object.__setattr__(self, "product", self.segment(0, self.length))
        object.__setattr__(self, "_building", False)

    @property
    def sealed(self) -> bool:
        return not self._building

    def _whole_rows(self, row: int, remaining: int) -> tuple[int, int]:
        end = row + 1
        count = self.widths[row]
        while end < len(self.widths) and count + self.widths[end] <= remaining:
            count += self.widths[end]
            end += 1
        return end, count

    def segment(self, begin: int, length: int) -> Matrix2:
        if length == 0:
            return Matrix2.identity()
        if (
            not self._building
            and self.last_prefixes is not None
            and begin >= self.widths[0] - self.start
        ):
            position = begin - self.widths[0] + self.start
            end = position + length
            indexed = len(self.last_prefixes) // _PREFIX.size - 1
            if end <= indexed:
                return Matrix2(_indexed_interval(self.last_prefixes, position, length))
            width = self.widths[1]
            cut = width - _SETTLED_COLUMNS
            if indexed >= cut and self.first_exponent is not None and end <= width:
                # The retained irregular head and the settled suffix cover
                # this clip. Remove the right tail in physical matrix order.
                right = width - end
                successor = self.first_exponent + 1
                tail = settled_low_action(successor, width - max(position, cut))
                if right:
                    trailing = settled_low_action(successor, right)
                    tail = multiply_entries(tail, _adjugate(trailing, right))
                if position < cut:
                    head = _indexed_interval(
                        self.last_prefixes, position, cut - position
                    )
                    tail = multiply_entries(head, tail)
                return Matrix2(tail)
        if not self._building and begin == 0:
            prefix = self.first_row_prefix
            if prefix is not None and prefix[0] == length:
                return Matrix2(prefix[1])
        start = begin + self.start
        row = 0
        while start >= self.widths[row]:
            start -= self.widths[row]
            row += 1
        entries = (1, 0, 0, 1)
        remaining = length
        while row < len(self.widths):
            width = self.widths[row]
            count = min(remaining, width - start)
            if (
                not self._building
                and self.row_prefixes
                and start == 0
                and count == width
            ):
                end, consumed = self._whole_rows(row, remaining)
                whole = self.row_prefixes[end - 1]
                if row:
                    # Cancel the already-issued left boundary in matrix order.
                    offset = begin + length - remaining
                    whole = multiply_entries(
                        _adjugate(self.row_prefixes[row - 1], offset), whole
                    )
                entries = (
                    whole if remaining == length else multiply_entries(entries, whole)
                )
                remaining -= consumed
                if not remaining:
                    return Matrix2(entries)
                row = end
                continue
            exponent = (
                None if self.first_exponent is None else self.first_exponent + row
            )
            # Only an interval ending at the physical low edge admits the
            # settled suffix action directly; a moving cut uses the exact path.
            suffix_count = (
                min(_SETTLED_COLUMNS, count, width, exponent)
                if exponent is not None and start + count == width
                else 0
            )
            action = (
                settled_low_action(exponent, suffix_count)
                if exponent is not None and suffix_count
                else None
            )
            if (
                exponent is not None
                and exponent >= 2
                and width >= 2
                and start + count == width - 1
            ):
                # A clipped prefix ending on the settled tens digit of 25.
                suffix_count = 1
                action = SETTLED_TENS_ACTION
            prefix_count = count - suffix_count
            if (
                self._building
                and self.index_last
                and row == 1
                and start == 0
                and count == width
                and prefix_count > 0
            ):
                value = reciprocal_row_interval(
                    self.quotient, row, width, 0, prefix_count
                )
                indexed = min(
                    reciprocal_indexed_columns(width) or width // 2, prefix_count
                )
                remainder_count = prefix_count - indexed
                value, remainder = divmod(value, 10**remainder_count)
                native = _native_continuant()
                if native is None:
                    raise RuntimeError("native CF prefix owner disappeared")
                prefixes = native.ordered_prefix_bank(value, indexed)
                if (
                    type(prefixes) is not bytes
                    or len(prefixes) != (indexed + 1) * _PREFIX.size
                ):
                    raise RuntimeError("native CF prefix bank has invalid bounds")
                object.__setattr__(self, "last_prefixes", prefixes)
                entries = multiply_entries(
                    entries, _PREFIX.unpack_from(prefixes, indexed * _PREFIX.size)
                )
                if remainder_count:
                    entries = multiply_entries(
                        entries, native.ordered_product(remainder, remainder_count)
                    )
                if action is not None:
                    entries = multiply_entries(entries, action)
                remaining -= count
                if remaining == 0:
                    return Matrix2(entries)
                raise ArithmeticError("unexpected reciprocal tile tail")
            if prefix_count:
                value = reciprocal_row_interval(
                    self.quotient, row, width, start, prefix_count
                )
                native = (
                    _native_continuant()
                    if 4 <= prefix_count <= 32
                    and os.environ.get("NUMBER_COMPILER_ENABLE_CF_CONTINUANT") == "1"
                    else None
                )
                if native is not None and prefix_count > 16:
                    # Split at an exact decimal place and append the first
                    # complete source-free ordered word before its remainder.
                    head, value = divmod(value, 10 ** (prefix_count - 16))
                    head_action = native.ordered_product(head, 16)
                    if entries == (1, 0, 0, 1):
                        entries = head_action
                    else:
                        entries = multiply_entries(entries, head_action)
                    prefix_count -= 16
                if native is None or prefix_count < 4:
                    entries = append_decimal_value(
                        value, 10 ** (prefix_count - 1), entries
                    )
                else:
                    native_action = native.ordered_product(value, prefix_count)
                    if entries == (1, 0, 0, 1):
                        entries = native_action
                    else:
                        entries = multiply_entries(entries, native_action)
            if action is not None:
                entries = multiply_entries(entries, action)
            remaining -= count
            if self._building and start + count == width:
                if self.retain_row_prefixes:
                    object.__setattr__(
                        self, "row_prefixes", (*self.row_prefixes, entries)
                    )
                elif row == 0:
                    object.__setattr__(self, "first_row_prefix", (count, entries))
            if remaining == 0:
                return Matrix2(entries)
            start = 0
            row += 1
        raise ArithmeticError("ordered segment exceeded the authenticated tile")
