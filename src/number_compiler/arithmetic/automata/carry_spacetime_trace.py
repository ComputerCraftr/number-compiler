"""Bounded ordered ×5 space-time traces over exact decimal cell content.

The caller authenticates the physical inlet. This owner checks its complete
packed contents, computes all selected times, and keeps their ledger charge
until replacement or close; it does not issue physical-source authority.
"""

from __future__ import annotations

from types import TracebackType
from typing import Self

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.owned_memo import LedgerReservation

_LANE_BITS = 24
_STRIDE = 24
_LEAF_WIDTH = 16
_MAX_WIDTH = 32
_MAX_SPAN = 4


def _fixed_program(span: int) -> tuple[int, int]:
    kernel = sum(
        (pow(10, tick - j, 10 << tick) << (span - tick))
        << (_LANE_BITS * ((tick - 1) * _STRIDE + j))
        for tick in range(1, span + 1)
        for j in range(tick + 1)
    )
    mask = sum(1023 << (_LANE_BITS * j) for j in range(_STRIDE * span))
    return kernel, mask


_PROGRAMS = tuple(_fixed_program(span) for span in range(1, _MAX_SPAN + 1))
# Immutable mathematical masks; these are independent of any admitted source.
_LOW_MASKS = tuple(
    (1 << (_LANE_BITS * n)) - 1 for n in range(_MAX_WIDTH + _MAX_SPAN + 1)
)
_LANE_ONES = tuple(mask // ((1 << _LANE_BITS) - 1) for mask in _LOW_MASKS)


def _trace_leaf(
    inlet: int, output_width: int, below: int, span: int
) -> tuple[int, ...]:
    kernel, mask = _PROGRAMS[span - 1]
    values = ((inlet * kernel) >> span) & mask
    quotient = ((410 * values) >> 12) & mask
    remainder = values - 10 * quotient
    output_mask = _LOW_MASKS[output_width]
    return tuple(
        (remainder >> (_LANE_BITS * (tick * _STRIDE + below))) & output_mask
        for tick in range(span)
    )


class Pow5SpatialTrace:
    """Issue finite source-free response rows for a checked packed inlet."""

    def __init__(self, ledger: ResourceLedger, *, shared_cache: bool = True) -> None:
        if type(ledger) is not ResourceLedger or type(shared_cache) is not bool:
            raise TypeError("spatial trace requires a ledger and Boolean cache policy")
        self._ledger = ledger
        self._shared_cache = shared_cache
        self._key: tuple[int, int, int] | None = None
        self._owner = ledger.register(
            f"pow5-spatial-trace-{ledger.owner_count}", "pow5-spatial-trace"
        )
        self._memo: dict[tuple[int, int, int, int], tuple[int, ...]] = {}
        self._closed = False
        self._workspace: LedgerReservation | None = None
        self._rows: tuple[tuple[int, int], ...] = ()

    def __enter__(self) -> Self:
        if self._closed:
            raise RuntimeError("spatial trace is closed")
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
        self._rows = ()
        self._key = None
        self._memo.clear()
        if self._workspace is not None:
            self._workspace.close()
            self._workspace = None

    def issue(
        self, source24: int, width: int, span: int
    ) -> tuple[tuple[int, int], ...]:
        """Return chronological decimal digit lanes with complete lower halos."""
        if self._closed:
            raise RuntimeError("spatial trace is closed")
        require_integer(width, "spatial source width", 1, _MAX_WIDTH)
        require_integer(span, "spatial trace span", 1, _MAX_SPAN)
        if type(source24) is not int or source24 < 0:
            raise ValueError("spatial source must be a nonnegative packed integer")
        # Bound every input before allocating the fixed lane masks.
        if source24.bit_length() > _LANE_BITS * width:
            raise ValueError("spatial source exceeds its width")
        key = (source24, width, span)
        if self._shared_cache and key == self._key:
            self._ledger.check_capacity(nodes=0, entries=0)
            return self._rows

        created = self._workspace is None
        if created:
            reservation = LedgerReservation(self._ledger, self._owner)
            self._workspace = reservation
            try:
                # Previous and candidate actions each get 256 nodes/five
                # entries; construction gets 768 nodes/twelve entries.
                reservation.reserve(nodes=1280, entries=22)
            except BaseException:
                try:
                    reservation.close()
                except BaseException:
                    self._closed = True
                    raise
                self._workspace = None
                raise
        publishing = False
        try:
            self._ledger.check_capacity(nodes=0, entries=0)
            lane_ones = _LANE_ONES[width]
            if source24 & ~(15 * lane_ones) or (source24 + 6 * lane_ones) & (
                16 * lane_ones
            ):
                raise ValueError("spatial source has an invalid decimal lane")
            if width > 1 and not source24 >> (_LANE_BITS * (width - 1)):
                raise ValueError("spatial source width is not significant")
            next_memo: dict[tuple[int, int, int, int], tuple[int, ...]] = {}
            if width + span <= _LEAF_WIDTH:
                packed = _trace_leaf(source24, width + span, 0, span)
            else:

                def visit(lo: int, hi: int) -> tuple[int, ...]:
                    if hi - lo > _LEAF_WIDTH:
                        mid = (lo + hi) // 2
                        left, right = visit(lo, mid), visit(mid, hi)
                        return tuple(
                            a | (b << (_LANE_BITS * (mid - lo)))
                            for a, b in zip(left, right, strict=True)
                        )
                    below = min(lo, span)
                    inlet_width = hi - lo + below
                    inlet = (source24 >> (_LANE_BITS * (lo - below))) & _LOW_MASKS[
                        inlet_width
                    ]
                    leaf_key = (inlet, hi - lo, below, span)
                    found = next_memo.get(leaf_key)
                    if found is None and self._shared_cache:
                        found = self._memo.get(leaf_key)
                    if found is None:
                        found = _trace_leaf(*leaf_key)
                    if self._shared_cache:
                        next_memo[leaf_key] = found
                    return found

                packed = visit(0, width + span)
            rows = tuple(
                (row, max(1, (row.bit_length() + _LANE_BITS - 1) // _LANE_BITS))
                for row in packed
            )
            publishing = True
            self._rows = rows
            self._memo = next_memo
            self._key = key if self._shared_cache else None
            return rows
        except BaseException:
            if created and not publishing and self._workspace is not None:
                try:
                    self._workspace.close()
                except BaseException:
                    self._closed = True
                    raise
                self._workspace = None
            if publishing:
                self._closed = True
                self._rows = ()
                self._key = None
                self._memo.clear()
            raise
