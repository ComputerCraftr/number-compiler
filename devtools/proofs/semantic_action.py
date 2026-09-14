"""Proof-only exact reverse/add forcing operators and event tapes."""

from __future__ import annotations

from dataclasses import dataclass

from devtools.proofs import require_exact_oracle
from number_compiler.arithmetic.fields.dyadic_tile import (
    DyadicChunk,
    DyadicSpan,
    DyadicTile,
    align_span,
    append_symbol,
    concat,
    first_symbol,
    join,
    last_symbol,
    leaf,
    mirror_span,
    prepend_symbol,
    rebase,
    retile_like,
    slice_span,
    symbol_at,
)


@dataclass(frozen=True, slots=True)
class ReverseAddAffineAction:
    """One exact local reverse/add affine forcing operator."""

    action_id: int
    base: int
    growth: int
    event_span: DyadicSpan

    def __post_init__(self) -> None:
        require_exact_oracle()
        if self.base < 2 or self.growth not in (0, 1):
            raise ValueError(self)
        if self.event_span.start != 0 or self.event_span.length <= 0:
            raise ValueError(self.event_span)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        require_exact_oracle()
        return (
            "reverse-add-affine-action",
            self.base,
            self.growth,
            tuple(chunk.tile for chunk in self.event_span.chunks),
        )


@dataclass(frozen=True, slots=True)
class ReverseAddAffineActionMetrics:
    requests: int
    hits: int
    actions: int
    aliases: int
    event_stencil_entries: int
    event_stencil_hits: int
    affine_entries: int
    affine_hits: int

    def __post_init__(self) -> None:
        require_exact_oracle()


class _ReverseAddEventStencilArena:
    """Derive the signed event row from one forward carry row dyadically."""

    __slots__ = (
        "_growth",
        "_no_growth",
        "base",
        "hits",
        "requests",
    )

    def __init__(self, base: int) -> None:
        require_exact_oracle()
        self.base = int(base)
        if self.base < 2:
            raise ValueError(base)
        self._no_growth: dict[tuple[object, object, int, int], DyadicTile] = {}
        self._growth: dict[tuple[object, object, int, int], DyadicTile] = {}
        self.requests = 0
        self.hits = 0

    def no_growth_tile(
        self,
        carry: DyadicTile,
        reflected: DyadicTile,
        previous_carry: int,
        next_reflected: int,
    ) -> DyadicTile:
        """Return ``E`` for a no-growth block.

        With ``K_i=C_(i+1)`` and ``R_i=C_(d-i)``,

            E_i = K_(i-1) + R_(i+1) - b*(K_i + R_i).
        """
        require_exact_oracle()
        previous_carry = int(previous_carry)
        next_reflected = int(next_reflected)
        key = (
            carry,
            reflected,
            previous_carry,
            next_reflected,
        )
        self.requests += 1
        found = self._no_growth.get(key)
        if found is not None:
            self.hits += 1
            return found
        built: dict[tuple[object, object, int, int], DyadicTile] = {}
        stack: list[tuple[DyadicTile, DyadicTile, int, int, bool]] = [
            (carry, reflected, previous_carry, next_reflected, False),
        ]
        while stack:
            k_tile, r_tile, prev_k, next_r, ready = stack.pop()
            local_key = (k_tile, r_tile, prev_k, next_r)
            cached = self._no_growth.get(local_key)
            if cached is not None:
                built[local_key] = cached
                continue
            if k_tile.level == 0:
                if k_tile.symbol is None or r_tile.symbol is None:
                    raise AssertionError((k_tile, r_tile))
                value = (
                    prev_k
                    + next_r
                    - self.base * (int(k_tile.symbol) + int(r_tile.symbol))
                )
                out = leaf(value)
                self._no_growth[local_key] = out
                built[local_key] = out
                continue
            if (
                k_tile.left is None
                or k_tile.right is None
                or r_tile.left is None
                or r_tile.right is None
            ):
                raise AssertionError((k_tile, r_tile))
            if not ready:
                stack.append((k_tile, r_tile, prev_k, next_r, True))
                right_prev = last_symbol(k_tile.left)
                left_next = first_symbol(r_tile.right)
                right_key = (
                    k_tile.right,
                    r_tile.right,
                    right_prev,
                    next_r,
                )
                left_key = (
                    k_tile.left,
                    r_tile.left,
                    prev_k,
                    left_next,
                )
                if right_key not in built and right_key not in self._no_growth:
                    stack.append(
                        (
                            k_tile.right,
                            r_tile.right,
                            right_prev,
                            next_r,
                            False,
                        )
                    )
                if left_key not in built and left_key not in self._no_growth:
                    stack.append(
                        (
                            k_tile.left,
                            r_tile.left,
                            prev_k,
                            left_next,
                            False,
                        )
                    )
                continue
            right_prev = last_symbol(k_tile.left)
            left_next = first_symbol(r_tile.right)
            left_key = (
                k_tile.left,
                r_tile.left,
                prev_k,
                left_next,
            )
            right_key = (
                k_tile.right,
                r_tile.right,
                right_prev,
                next_r,
            )
            left = self._no_growth.get(left_key, built.get(left_key))
            right = self._no_growth.get(right_key, built.get(right_key))
            if left is None or right is None:
                raise AssertionError(local_key)
            out = join(left, right)
            self._no_growth[local_key] = out
            built[local_key] = out
        return self._no_growth[key]

    def growth_tile(
        self,
        carry: DyadicTile,
        reflected: DyadicTile,
        next_carry: int,
        next_reflected: int,
    ) -> DyadicTile:
        """Return growth-interior events for source-indexed positions.

        For event position ``i=j+1``:

            E_i = K_j + R_(j+1) - b*(K_(j+1) + R_j).
        """
        require_exact_oracle()
        next_carry = int(next_carry)
        next_reflected = int(next_reflected)
        key = (
            carry,
            reflected,
            next_carry,
            next_reflected,
        )
        self.requests += 1
        found = self._growth.get(key)
        if found is not None:
            self.hits += 1
            return found
        built: dict[tuple[object, object, int, int], DyadicTile] = {}
        stack: list[tuple[DyadicTile, DyadicTile, int, int, bool]] = [
            (carry, reflected, next_carry, next_reflected, False),
        ]
        while stack:
            k_tile, r_tile, next_k, next_r, ready = stack.pop()
            local_key = (k_tile, r_tile, next_k, next_r)
            cached = self._growth.get(local_key)
            if cached is not None:
                built[local_key] = cached
                continue
            if k_tile.level == 0:
                if k_tile.symbol is None or r_tile.symbol is None:
                    raise AssertionError((k_tile, r_tile))
                value = (
                    int(k_tile.symbol)
                    + next_r
                    - self.base * (next_k + int(r_tile.symbol))
                )
                out = leaf(value)
                self._growth[local_key] = out
                built[local_key] = out
                continue
            if (
                k_tile.left is None
                or k_tile.right is None
                or r_tile.left is None
                or r_tile.right is None
            ):
                raise AssertionError((k_tile, r_tile))
            if not ready:
                stack.append((k_tile, r_tile, next_k, next_r, True))
                left_next_k = first_symbol(k_tile.right)
                left_next_r = first_symbol(r_tile.right)
                right_key = (
                    k_tile.right,
                    r_tile.right,
                    next_k,
                    next_r,
                )
                left_key = (
                    k_tile.left,
                    r_tile.left,
                    left_next_k,
                    left_next_r,
                )
                if right_key not in built and right_key not in self._growth:
                    stack.append(
                        (
                            k_tile.right,
                            r_tile.right,
                            next_k,
                            next_r,
                            False,
                        )
                    )
                if left_key not in built and left_key not in self._growth:
                    stack.append(
                        (
                            k_tile.left,
                            r_tile.left,
                            left_next_k,
                            left_next_r,
                            False,
                        )
                    )
                continue
            left_next_k = first_symbol(k_tile.right)
            left_next_r = first_symbol(r_tile.right)
            left_key = (
                k_tile.left,
                r_tile.left,
                left_next_k,
                left_next_r,
            )
            right_key = (
                k_tile.right,
                r_tile.right,
                next_k,
                next_r,
            )
            left = self._growth.get(left_key, built.get(left_key))
            right = self._growth.get(right_key, built.get(right_key))
            if left is None or right is None:
                raise AssertionError(local_key)
            out = join(left, right)
            self._growth[local_key] = out
            built[local_key] = out
        return self._growth[key]

    def event_span(self, carry: DyadicSpan, growth: int) -> DyadicSpan:
        """Return exact ``E`` without constructing the pair successor."""
        require_exact_oracle()
        growth = int(growth)
        if growth not in (0, 1) or carry.start != 0 or carry.length <= 0:
            raise ValueError((carry.start, carry.length, growth))
        reflected = mirror_span(carry, rebase_to_zero=True)
        reflected = retile_like(carry, reflected)
        if not growth:
            chunks: list[DyadicChunk] = []
            previous = 0
            for k_chunk, r_chunk in zip(carry.chunks, reflected.chunks, strict=True):
                next_r = (
                    0 if k_chunk.end == carry.end else symbol_at(reflected, k_chunk.end)
                )
                out = self.no_growth_tile(
                    k_chunk.tile,
                    r_chunk.tile,
                    previous,
                    next_r,
                )
                chunks.append(DyadicChunk(k_chunk.start, out))
                previous = last_symbol(k_chunk.tile)
            return DyadicSpan(0, carry.length, tuple(chunks))

        edge = 1 - self.base * first_symbol(carry.chunks[0].tile)
        if carry.length == 1:
            return DyadicSpan(
                0,
                2,
                (DyadicChunk(0, leaf(edge)), DyadicChunk(1, leaf(edge))),
            )
        interior_k = slice_span(carry, 0, carry.length - 1)
        interior_r = slice_span(reflected, 0, reflected.length - 1)
        interior_r = retile_like(interior_k, interior_r)
        chunks = []
        for k_chunk, r_chunk in zip(
            interior_k.chunks,
            interior_r.chunks,
            strict=True,
        ):
            next_k = symbol_at(carry, k_chunk.end)
            next_r = symbol_at(reflected, k_chunk.end)
            out = self.growth_tile(
                k_chunk.tile,
                r_chunk.tile,
                next_k,
                next_r,
            )
            chunks.append(DyadicChunk(k_chunk.start, out))
        interior = DyadicSpan(0, carry.length - 1, tuple(chunks))
        body = rebase(interior, 1)
        head = DyadicSpan(0, 1, (DyadicChunk(0, leaf(edge)),))
        return append_symbol(concat(head, body), edge)

    @property
    def retained_entries(self) -> int:
        require_exact_oracle()
        return len(self._no_growth) + len(self._growth)


class _ReverseAddAffineApplyArena:
    """Apply cached affine actions to exact pair payloads with dyadic zips."""

    __slots__ = ("_binary", "_ternary", "base", "hits", "requests")

    def __init__(self, base: int) -> None:
        require_exact_oracle()
        self.base = int(base)
        self._binary: dict[tuple[object, object], DyadicTile] = {}
        self._ternary: dict[tuple[object, object, object], DyadicTile] = {}
        self.requests = 0
        self.hits = 0

    def _binary_tile(self, source: DyadicTile, event: DyadicTile) -> DyadicTile:
        require_exact_oracle()
        key = (source, event)
        self.requests += 1
        found = self._binary.get(key)
        if found is not None:
            self.hits += 1
            return found
        built: dict[tuple[object, object], DyadicTile] = {}
        stack: list[tuple[DyadicTile, DyadicTile, bool]] = [(source, event, False)]
        while stack:
            a, e, ready = stack.pop()
            local_key = (a, e)
            cached = self._binary.get(local_key)
            if cached is not None:
                built[local_key] = cached
                continue
            if a.level == 0:
                if a.symbol is None or e.symbol is None:
                    raise AssertionError((a, e))
                value = 2 * int(a.symbol) + int(e.symbol)
                if not 0 <= value <= 2 * (self.base - 1):
                    raise AssertionError(("affine-no-growth", value))
                out = leaf(value)
                self._binary[local_key] = out
                built[local_key] = out
                continue
            if a.left is None or a.right is None or e.left is None or e.right is None:
                raise AssertionError((a, e))
            if not ready:
                stack.append((a, e, True))
                lk = (a.left, e.left)
                rk = (a.right, e.right)
                if rk not in built and rk not in self._binary:
                    stack.append((a.right, e.right, False))
                if lk not in built and lk not in self._binary:
                    stack.append((a.left, e.left, False))
                continue
            lk = (a.left, e.left)
            rk = (a.right, e.right)
            left = self._binary.get(lk, built.get(lk))
            right = self._binary.get(rk, built.get(rk))
            if left is None or right is None:
                raise AssertionError(local_key)
            out = join(left, right)
            self._binary[local_key] = out
            built[local_key] = out
        return self._binary[key]

    def _ternary_tile(
        self,
        direct: DyadicTile,
        shifted: DyadicTile,
        event: DyadicTile,
    ) -> DyadicTile:
        require_exact_oracle()
        key = (direct, shifted, event)
        self.requests += 1
        found = self._ternary.get(key)
        if found is not None:
            self.hits += 1
            return found
        built: dict[tuple[object, object, object], DyadicTile] = {}
        stack: list[tuple[DyadicTile, DyadicTile, DyadicTile, bool]] = [
            (direct, shifted, event, False),
        ]
        while stack:
            a, z, e, ready = stack.pop()
            local_key = (a, z, e)
            cached = self._ternary.get(local_key)
            if cached is not None:
                built[local_key] = cached
                continue
            if a.level == 0:
                if a.symbol is None or z.symbol is None or e.symbol is None:
                    raise AssertionError((a, z, e))
                value = int(a.symbol) + int(z.symbol) + int(e.symbol)
                if not 0 <= value <= 2 * (self.base - 1):
                    raise AssertionError(("affine-growth", value))
                out = leaf(value)
                self._ternary[local_key] = out
                built[local_key] = out
                continue
            if (
                a.left is None
                or a.right is None
                or z.left is None
                or z.right is None
                or e.left is None
                or e.right is None
            ):
                raise AssertionError((a, z, e))
            if not ready:
                stack.append((a, z, e, True))
                lk = (a.left, z.left, e.left)
                rk = (a.right, z.right, e.right)
                if rk not in built and rk not in self._ternary:
                    stack.append((a.right, z.right, e.right, False))
                if lk not in built and lk not in self._ternary:
                    stack.append((a.left, z.left, e.left, False))
                continue
            lk = (a.left, z.left, e.left)
            rk = (a.right, z.right, e.right)
            left = self._ternary.get(lk, built.get(lk))
            right = self._ternary.get(rk, built.get(rk))
            if left is None or right is None:
                raise AssertionError(local_key)
            out = join(left, right)
            self._ternary[local_key] = out
            built[local_key] = out
        return self._ternary[key]

    def apply(self, action: ReverseAddAffineAction, source: DyadicSpan) -> DyadicSpan:
        require_exact_oracle()
        if source.start != 0:
            raise ValueError(source.start)
        event = action.event_span
        if not action.growth:
            if event.length != source.length:
                raise ValueError((event.length, source.length))
            aligned_source = retile_like(event, source)
            chunks = tuple(
                DyadicChunk(
                    e_chunk.start,
                    self._binary_tile(s_chunk.tile, e_chunk.tile),
                )
                for s_chunk, e_chunk in zip(
                    aligned_source.chunks,
                    event.chunks,
                    strict=True,
                )
            )
            return DyadicSpan(0, event.length, chunks)

        if event.length != source.length + 1:
            raise ValueError((event.length, source.length))
        direct = append_symbol(source, 0)
        shifted = prepend_symbol(source, 0)
        direct = retile_like(event, direct)
        shifted = retile_like(event, shifted)
        chunks = tuple(
            DyadicChunk(
                e_chunk.start,
                self._ternary_tile(a_chunk.tile, z_chunk.tile, e_chunk.tile),
            )
            for a_chunk, z_chunk, e_chunk in zip(
                direct.chunks,
                shifted.chunks,
                event.chunks,
                strict=True,
            )
        )
        return DyadicSpan(0, event.length, chunks)

    @property
    def retained_entries(self) -> int:
        require_exact_oracle()
        return len(self._binary) + len(self._ternary)


class ReverseAddAffineActionArena:
    """Intern/apply exact reverse/add operators independently of source payload."""

    __slots__ = (
        "_actions",
        "aliases",
        "apply_arena",
        "base",
        "events",
        "hits",
        "requests",
    )

    def __init__(self, base: int = 10) -> None:
        require_exact_oracle()
        self.base = int(base)
        if self.base < 2:
            raise ValueError(base)
        self.events = _ReverseAddEventStencilArena(self.base)
        self.apply_arena = _ReverseAddAffineApplyArena(self.base)
        self._actions: dict[tuple[object, ...], ReverseAddAffineAction] = {}
        self.requests = 0
        self.hits = 0
        self.aliases = 0

    def from_carry(self, carry: DyadicSpan, growth: int) -> ReverseAddAffineAction:
        require_exact_oracle()
        self.requests += 1
        event = align_span(self.events.event_span(carry, int(growth)), 0)
        key = (
            "reverse-add-affine-action",
            self.base,
            int(growth),
            tuple(chunk.tile for chunk in event.chunks),
        )
        found = self._actions.get(key)
        if found is not None:
            self.hits += 1
            self.aliases += 1
            return found
        out = ReverseAddAffineAction(
            len(self._actions),
            self.base,
            int(growth),
            event,
        )
        self._actions[key] = out
        return out

    def apply(
        self,
        action: ReverseAddAffineAction,
        source: DyadicSpan,
    ) -> DyadicSpan:
        require_exact_oracle()
        if action.base != self.base:
            raise ValueError((action.base, self.base))
        return align_span(self.apply_arena.apply(action, source), 0)

    def retained_event_spans(self) -> tuple[DyadicSpan, ...]:
        """Spatial event stencils retained by canonical affine actions."""
        require_exact_oracle()
        return tuple(action.event_span for action in self._actions.values())

    def metrics(self) -> ReverseAddAffineActionMetrics:
        require_exact_oracle()
        return ReverseAddAffineActionMetrics(
            self.requests,
            self.hits,
            len(self._actions),
            self.aliases,
            self.events.retained_entries,
            self.events.hits,
            self.apply_arena.retained_entries,
            self.apply_arena.hits,
        )


__all__ = [
    "ReverseAddAffineAction",
    "ReverseAddAffineActionArena",
    "ReverseAddAffineActionMetrics",
]
