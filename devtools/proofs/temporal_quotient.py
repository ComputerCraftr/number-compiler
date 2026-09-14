"""Proof-only lossless encoding of exact reverse/add carry histories.

The packed cells preserve every carry and activity bit. This is a reference
certificate, not a bounded extensional action or production temporal quotient.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass

from devtools.proofs import require_exact_oracle
from devtools.proofs.reverse_action import linear_span
from number_compiler.arithmetic.carry.event_memory import event_memory_horizon
from number_compiler.arithmetic.fields.dyadic_tile import (
    DyadicChunk,
    DyadicSpan,
    DyadicTile,
    concat,
    iter_symbols,
    join,
    uniform,
    uniform_span,
)


def _pack_row(row: DyadicSpan, index: int, horizon: int) -> DyadicSpan:
    """Map each distinct binary tile once to its carry/activity channel."""
    require_exact_oracle()
    built: dict[DyadicTile, DyadicTile] = {}
    for chunk in row.chunks:
        stack = [(chunk.tile, False)]
        while stack:
            node, ready = stack.pop()
            if node in built:
                continue
            if node.symbol is not None:
                if node.symbol not in (0, 1):
                    raise ValueError("reverse/add carry rows must be binary")
                packed = (node.symbol << index) | (1 << (horizon + index))
                built[node] = uniform(packed, node.level)
                continue
            if node.left is None or node.right is None:
                raise ValueError("malformed carry tile")
            if not ready:
                stack.extend(((node, True), (node.right, False), (node.left, False)))
                continue
            built[node] = join(built[node.left], built[node.right])
    return DyadicSpan(
        row.start,
        row.length,
        tuple(DyadicChunk(chunk.start, built[chunk.tile]) for chunk in row.chunks),
    )


def _validate_cut(tape: DyadicSpan, horizon: int) -> None:
    """Validate binary channels and prefix activity on distinct tile summaries."""
    require_exact_oracle()
    mask = (1 << horizon) - 1
    edges: dict[DyadicTile, tuple[int, int]] = {}
    previous = mask
    for chunk in tape.chunks:
        stack = [(chunk.tile, False)]
        while stack:
            node, ready = stack.pop()
            if node in edges:
                continue
            if node.symbol is not None:
                packed = node.symbol
                if packed < 0 or packed >> (2 * horizon):
                    raise ValueError((packed, horizon))
                active = (packed >> horizon) & mask
                if (packed & mask) & ~active:
                    raise ValueError("inactive reverse/add rows may not carry")
                edges[node] = (active, active)
                continue
            if node.left is None or node.right is None:
                raise ValueError("malformed carry cut")
            if not ready:
                stack.extend(((node, True), (node.right, False), (node.left, False)))
                continue
            left, right = edges[node.left], edges[node.right]
            if right[0] & ~left[1]:
                raise ValueError("row activity must be a spatial prefix")
            edges[node] = left[0], right[1]
        first, last = edges[chunk.tile]
        if first & ~previous:
            raise ValueError("row activity must be a spatial prefix")
        previous = last


@dataclass(frozen=True, slots=True)
class ReverseAddCarryCutState:
    """One exact vertical reverse/add carry cut over the fixed H-row horizon.

    A spatial cell packs two H-bit masks::

        low H bits      = carry value in each temporal row
        next H bits     = whether that row is active at this spatial position

    Therefore the local semantic alphabet is bounded by ``2**(2H)`` for a
    fixed radix, while arbitrarily long integers remain ordinary dyadic spatial
    geometry.  Row lengths are reconstructed from active masks and are not
    stored in temporal identity.
    """

    base: int
    horizon: int
    tape: DyadicSpan

    def __post_init__(self) -> None:
        require_exact_oracle()
        base = int(self.base)
        horizon = int(self.horizon)
        if base < 3 or horizon != event_memory_horizon(base):
            raise ValueError((base, horizon))
        if self.tape.start != 0 or self.tape.length <= 0:
            raise ValueError((self.tape.start, self.tape.length))
        _validate_cut(self.tape, horizon)

    @classmethod
    def from_rows(
        cls,
        rows: Sequence[DyadicSpan],
        *,
        base: int = 10,
    ) -> ReverseAddCarryCutState:
        require_exact_oracle()
        base = int(base)
        horizon = event_memory_horizon(base)
        rows = tuple(rows)
        if len(rows) != horizon:
            raise ValueError((len(rows), horizon))
        for row in rows:
            if row.start != 0 or row.length <= 0:
                raise ValueError((row.start, row.length))
        width = max(row.length for row in rows)
        tape = uniform_span(0, width, 0)
        for row_index, row in enumerate(rows):
            packed = _pack_row(row, row_index, horizon)
            if row.length < width:
                packed = concat(packed, uniform_span(row.length, width - row.length, 0))
            tape = linear_span(tape, packed, 1, 1 << (2 * horizon))
        return cls(base, horizon, tape)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        # Chunk widths are intrinsic to canonical tiles.  No scalar source
        # length or row-width vector is retained by temporal identity.
        require_exact_oracle()
        return (
            "reverse-add-carry-cut",
            self.base,
            self.horizon,
            tuple(chunk.tile for chunk in self.tape.chunks),
        )

    @property
    def cell_payload_bits(self) -> int:
        require_exact_oracle()
        return 2 * self.horizon

    @property
    def spatial_cells(self) -> int:
        require_exact_oracle()
        return int(self.tape.length)

    @property
    def distinct_cell_symbols(self) -> int:
        require_exact_oracle()
        symbols: set[int] = set()
        seen: set[DyadicTile] = set()
        stack = [chunk.tile for chunk in self.tape.chunks]
        while stack:
            node = stack.pop()
            if node in seen:
                continue
            seen.add(node)
            if node.symbol is not None:
                symbols.add(node.symbol)
            elif node.left is not None and node.right is not None:
                stack.extend((node.left, node.right))
        return len(symbols)

    def row_values(self) -> tuple[tuple[int, ...], ...]:
        require_exact_oracle()
        mask = (1 << self.horizon) - 1
        rows: list[list[int]] = [[] for _ in range(self.horizon)]
        ended = [False] * self.horizon
        for packed in map(int, iter_symbols(self.tape)):
            carry = packed & mask
            active = (packed >> self.horizon) & mask
            for row_index in range(self.horizon):
                bit = 1 << row_index
                if active & bit:
                    if ended[row_index]:
                        raise AssertionError("non-prefix active row")
                    rows[row_index].append(1 if carry & bit else 0)
                else:
                    ended[row_index] = True
        return tuple(tuple(row) for row in rows)


__all__ = ["ReverseAddCarryCutState"]
