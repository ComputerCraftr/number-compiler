"""Proof-only exact reverse/add affine actions and numeric offset tapes.

Action IDs here intern exact dyadic coefficient payloads. They are an oracle
for symbolic program correctness, not the production transfer quotient.
"""

from __future__ import annotations

from dataclasses import dataclass

from devtools.verification import require_exact_oracle
from devtools.verification.carry_action_quotient import CarryActionQuotientArena
from devtools.verification.semantic_action import (
    ReverseAddAffineAction,
    ReverseAddAffineActionArena,
)
from number_compiler.arithmetic.carry.event_memory import (
    event_memory_horizon,
    pair_plane_bits,
)
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
)
from number_compiler.arithmetic.fields.dyadic_tile import (
    DyadicChunk,
    DyadicSpan,
    DyadicTile,
    align_span,
    append_symbol,
    join,
    last_symbol,
    mirror_span,
    prepend_symbol,
    retile_like,
    slice_span,
    uniform,
    uniform_span,
)


def _linear_tile(a: DyadicTile, b: DyadicTile, scale: int, modulus: int) -> DyadicTile:
    require_exact_oracle()
    if a.level != b.level:
        raise ValueError("unaligned coefficient tiles")
    key = a.node_id, b.node_id, scale, modulus
    # Explicit lowering only: this temporary memo dies with the operation.
    # No module-global exact coefficient/output cache survives the request.
    cache: dict[tuple[int, int, int, int], DyadicTile] = {}
    stack = [(a, b, False)]
    while stack:
        x, y, ready = stack.pop()
        local = x.node_id, y.node_id, scale, modulus
        if local in cache:
            continue
        if x.symbol is not None and y.symbol is not None:
            cache[local] = uniform((scale * x.symbol + y.symbol) % modulus, x.level)
            continue
        if x.left is None or x.right is None or y.left is None or y.right is None:
            raise AssertionError("malformed coefficient tile")
        if not ready:
            stack.extend(
                ((x, y, True), (x.right, y.right, False), (x.left, y.left, False))
            )
            continue
        cache[local] = join(
            cache[x.left.node_id, y.left.node_id, scale, modulus],
            cache[x.right.node_id, y.right.node_id, scale, modulus],
        )
    return cache[key]


def linear_effect_cache_entries() -> int:
    """Compatibility metric: modular zip lowering retains no global memo."""
    require_exact_oracle()
    return 0


def linear_span(a: DyadicSpan, b: DyadicSpan, scale: int, modulus: int) -> DyadicSpan:
    """Return ``scale*a+b (mod modulus)`` by structurally shared tile zips."""
    require_exact_oracle()
    if a.length != b.length:
        raise ValueError((a.length, b.length))
    a = retile_like(b, a)
    return align_span(
        DyadicSpan(
            0,
            b.length,
            tuple(
                DyadicChunk(y.start, _linear_tile(x.tile, y.tile, scale, modulus))
                for x, y in zip(a.chunks, b.chunks, strict=True)
            ),
        ),
        0,
    )


def transport_span(source: DyadicSpan, q: int, r: int, bits: int) -> DyadicSpan:
    """Apply ``2**q * (1+z)**r`` without expanding a polynomial or field."""
    require_exact_oracle()
    modulus = 1 << bits
    if q >= bits:
        return uniform_span(0, source.length + r, 0)
    out = source
    for _ in range(r):
        out = linear_span(append_symbol(out, 0), prepend_symbol(out, 0), 1, modulus)
    return linear_span(out, uniform_span(0, out.length, 0), 1 << q, modulus)


@dataclass(frozen=True, slots=True)
class ReverseAddMacroAction:
    action_id: int
    q: int
    r: int
    event: DyadicSpan

    @property
    def input_width(self) -> int:
        require_exact_oracle()
        return self.event.length - self.r

    def __post_init__(self) -> None:
        require_exact_oracle()


class ReverseAddMacroActionArena:
    """Integer-ID monoid of complete affine maps, including their exact offset.

    Coefficients are computed modulo the pair plane.  A valid pair coefficient
    is smaller than that modulus, so applying an action along its certified
    branch itinerary recovers the exact endpoint.  Matching actions do not
    certify that their sources have matching *future* branch itineraries.
    """

    def __init__(self, base: int) -> None:
        require_exact_oracle()
        if base < 2:
            raise ValueError(base)
        self.base = base
        self.bits = (2 * (base - 1)).bit_length()
        self._owner = ArenaToken("reverse-macro-program")
        self._actions: list[ReverseAddMacroAction] = []
        self._keys: dict[tuple[int, int, tuple[int, ...]], int] = {}
        self._compose: dict[tuple[int, int], int] = {}
        self.compose_requests = 0
        self.compose_hits = 0
        self.applications = 0

    def intern_record(self, q: int, r: int, event: DyadicSpan) -> int:
        require_exact_oracle()
        q = min(q, self.bits)
        event = align_span(event, 0)
        event = linear_span(event, uniform_span(0, event.length, 0), 1, 1 << self.bits)
        key = q, r, event.tile_ids
        found = self._keys.get(key)
        if found is not None:
            return found
        index = len(self._actions)
        self._actions.append(ReverseAddMacroAction(index, q, r, event))
        self._keys[key] = index
        return index

    def scoped_handle(self, local_id: int) -> ActionProgramID:
        require_exact_oracle()
        return ActionProgramID(self._owner, "reverse-macro-program", local_id)

    def validate(self, handle: object) -> int:
        require_exact_oracle()
        if not isinstance(handle, ActionProgramID):
            raise TypeError("reverse macro action requires a scoped program ID")
        return handle.validate(
            self._owner, "reverse-macro-program", size=len(self._actions)
        ).local_id

    def primitive(self, action: ReverseAddAffineAction) -> ActionProgramID:
        require_exact_oracle()
        if action.base != self.base:
            raise ValueError("reverse macro action has a different radix")
        return self.scoped_handle(
            self.intern_record(1 - action.growth, action.growth, action.event_span)
        )

    def compose(
        self, before: ActionProgramID, after: ActionProgramID
    ) -> ActionProgramID:
        require_exact_oracle()
        before_id, after_id = self.validate(before), self.validate(after)
        self.compose_requests += 1
        key = before_id, after_id
        cached = self._compose.get(key)
        if cached is not None:
            self.compose_hits += 1
            return self.scoped_handle(cached)
        a, b = self._actions[before_id], self._actions[after_id]
        if a.event.length != b.input_width:
            raise ValueError("affine action interfaces do not match")
        transported = transport_span(a.event, b.q, b.r, self.bits)
        event = linear_span(transported, b.event, 1, 1 << self.bits)
        out = self.intern_record(a.q + b.q, a.r + b.r, event)
        self._compose[key] = out
        return self.scoped_handle(out)

    def apply(self, action_id: ActionProgramID, source: DyadicSpan) -> DyadicSpan:
        require_exact_oracle()
        local_id = self.validate(action_id)
        self.applications += 1
        action = self._actions[local_id]
        if action.input_width != source.length:
            raise ValueError((action.input_width, source.length))
        return linear_span(
            transport_span(source, action.q, action.r, self.bits),
            action.event,
            1,
            1 << self.bits,
        )

    def carry_projection(
        self,
        action_id: ActionProgramID,
        source: DyadicSpan,
        quotient: CarryActionQuotientArena,
        *,
        base: int,
    ) -> tuple[DyadicSpan, int]:
        """Evaluate only bounded carry ports of the symbolic action result."""
        require_exact_oracle()
        action = self._actions[self.validate(action_id)]
        if base != self.base:
            raise ValueError("reverse carry projection has a different radix")
        return quotient.project_affine_span(
            transport_span(source, action.q, action.r, self.bits),
            action.event,
            base=base,
            modulus=1 << self.bits,
        )

    def retained_effect_spans(self) -> tuple[DyadicSpan, ...]:
        """All exact offsets retained by canonical symbolic affine actions."""
        require_exact_oracle()
        return tuple(action.event for action in self._actions)

    @property
    def action_count(self) -> int:
        require_exact_oracle()
        return len(self._actions)

    @property
    def composition_count(self) -> int:
        require_exact_oracle()
        return len(self._compose)


def reconstruct_slab_span(carries: tuple[DyadicSpan, ...], base: int) -> DyadicSpan:
    """Apply the H-row event-memory theorem entirely over dyadic summaries."""
    require_exact_oracle()
    if len(carries) != event_memory_horizon(base):
        raise ValueError(len(carries))
    actions = ReverseAddAffineActionArena(base)
    bits = pair_plane_bits(base)
    out = uniform_span(0, carries[0].length - 1, 0)
    for row in carries:
        carry = slice_span(row, 1, row.length, rebase_to_zero=True)
        growth = last_symbol(row.chunks[-1].tile)
        if carry.length != out.length:
            raise ValueError("carry slab width itinerary does not match")
        action = actions.from_carry(carry, growth)
        out = linear_span(
            transport_span(out, 1 - growth, growth, bits),
            action.event_span,
            1,
            1 << bits,
        )
    stack = [chunk.tile for chunk in out.chunks]
    seen: set[int] = set()
    while stack:
        node = stack.pop()
        if node.node_id in seen:
            continue
        seen.add(node.node_id)
        if node.symbol is not None:
            if not 0 <= node.symbol <= 2 * (base - 1):
                raise ValueError("carry window is not a canonical pair trajectory")
        elif node.left is not None and node.right is not None:
            stack.extend((node.left, node.right))
    reflected = align_span(mirror_span(out, rebase_to_zero=True), 0)
    if reflected.tile_ids != out.tile_ids:
        raise ValueError("carry window reconstructed a nonsymmetric pair field")
    return out
