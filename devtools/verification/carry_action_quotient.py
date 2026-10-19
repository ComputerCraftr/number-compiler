"""Proof-only exact carry-word aliases and arithmetic diagnostics.

CarryPortAction retains both complete emitted carry tapes. It is deliberately
excluded from production; finite boundary effects have a separate arena.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from itertools import pairwise

from devtools.verification import require_exact_oracle
from number_compiler.arithmetic.carry.carry_itinerary import LiveCarryItinerary
from number_compiler.arithmetic.carry.event_memory import (
    carry_field,
    event_memory_horizon,
    pair_plane_bits,
)
from number_compiler.arithmetic.fields.dyadic_tile import (
    DyadicChunk,
    DyadicSpan,
    DyadicTile,
    join,
    last_symbol,
    retile_like,
    uniform,
)
from number_compiler.arithmetic.fields.radix import bit_width, reverse_pair_sums
from number_compiler.arithmetic.polynomials.primary_jet import primary_jet_from_digits


def _row_mask(row: Sequence[int]) -> tuple[int, int]:
    require_exact_oracle()
    values = tuple(map(int, row))
    if not values or values[0] != 0 or any(v not in (0, 1) for v in values):
        raise ValueError(values)
    return len(values), sum(bit << i for i, bit in enumerate(values))


def _growth_bits(carries: Sequence[Sequence[int]]) -> tuple[int, ...]:
    require_exact_oracle()
    rows = tuple(tuple(map(int, row)) for row in carries)
    out = tuple(len(b) - len(a) for a, b in pairwise(rows))
    if any(g not in (0, 1) for g in out):
        raise ValueError("carry suffix has invalid width itinerary")
    return out


def _cyclotomic_valuations(
    growths: Sequence[int], *, bits: int
) -> tuple[tuple[int, int], ...]:
    require_exact_oracle()
    q = sum(1 - int(g) for g in growths)
    r = sum(map(int, growths))
    return tuple((m, min(bits, q + r // m)) for m in (1, 2, 4, 8))


@dataclass(frozen=True, slots=True)
class CarryTheoremInterface:
    primary_jet: tuple[int, ...]
    primary_nilpotent_age: tuple[int, int]
    cyclotomic_valuations: tuple[tuple[int, int], ...]
    width: int

    @property
    def canonical_key(self) -> tuple[object, ...]:
        require_exact_oracle()
        return (
            "carry-theorem-interface",
            self.primary_jet,
            self.primary_nilpotent_age,
            self.cyclotomic_valuations,
            self.width,
        )

    def __post_init__(self) -> None:
        require_exact_oracle()


@dataclass(frozen=True, slots=True)
class CarryActionInterface:
    """Exact source identity plus one derived theorem interface."""

    base: int
    live_rows: tuple[tuple[int, int], ...]
    theorem: CarryTheoremInterface

    @property
    def canonical_key(self) -> tuple[object, ...]:
        # The theorem is deterministically derived from the live suffix and is
        # intentionally not duplicated in source identity.
        require_exact_oracle()
        return ("carry-action-source", self.base, self.live_rows)

    @property
    def primary_jet(self) -> tuple[int, ...]:
        require_exact_oracle()
        return self.theorem.primary_jet

    @property
    def primary_nilpotent_age(self) -> tuple[int, int]:
        require_exact_oracle()
        return self.theorem.primary_nilpotent_age

    @property
    def cyclotomic_valuations(self) -> tuple[tuple[int, int], ...]:
        require_exact_oracle()
        return self.theorem.cyclotomic_valuations

    @property
    def width(self) -> int:
        require_exact_oracle()
        return self.theorem.width

    def __post_init__(self) -> None:
        require_exact_oracle()


@dataclass(frozen=True, slots=True)
class CarryThresholdSignature:
    """Exact threshold key with symmetry-aware canonical storage.

    Production reverse-add pair fields are palindromic, so their two threshold
    masks are stored only on the low half and mirrored on demand.  The public
    theorem helper also accepts arbitrary coefficient rows; those use a tagged
    full-mask fallback rather than pretending symmetry that is not present.
    """

    base: int
    width: int
    low_payload: int
    high_payload: int
    symmetric: bool

    def __post_init__(self) -> None:
        require_exact_oracle()
        stored_width = (self.width + 1) // 2 if self.symmetric else self.width
        if self.base < 2 or self.width <= 0:
            raise ValueError((self.base, self.width))
        limit = (1 << stored_width) - 1
        if (self.low_payload | self.high_payload) & ~limit:
            raise ValueError("threshold mask exceeds canonical storage width")
        if self.low_payload & self.high_payload:
            raise ValueError("threshold masks overlap")

    @classmethod
    def from_pair(cls, pair: Sequence[int], *, base: int) -> CarryThresholdSignature:
        require_exact_oracle()
        values = tuple(map(int, pair))
        base = int(base)
        if (
            not values
            or base < 2
            or any(not 0 <= value <= 2 * (base - 1) for value in values)
        ):
            raise ValueError((values, base))
        symmetric = values == values[::-1]
        take = (len(values) + 1) // 2 if symmetric else len(values)
        low = high = 0
        threshold = base - 1
        for index, value in enumerate(values[:take]):
            if value < threshold:
                low |= 1 << index
            elif value > threshold:
                high |= 1 << index
        return cls(base, len(values), low, high, symmetric)

    @staticmethod
    def _mirror(mask: int, width: int) -> int:
        require_exact_oracle()
        half = (width + 1) // 2
        out = 0
        for i in range(half):
            if (mask >> i) & 1:
                out |= 1 << i
                out |= 1 << (width - 1 - i)
        return out

    @property
    def low_mask(self) -> int:
        require_exact_oracle()
        return (
            self._mirror(self.low_payload, self.width)
            if self.symmetric
            else self.low_payload
        )

    @property
    def high_mask(self) -> int:
        require_exact_oracle()
        return (
            self._mirror(self.high_payload, self.width)
            if self.symmetric
            else self.high_payload
        )

    @property
    def canonical_key(self) -> tuple[object, ...]:
        require_exact_oracle()
        return (
            "carry-threshold",
            self.base,
            self.width,
            self.symmetric,
            self.low_payload,
            self.high_payload,
        )

    @property
    def symmetry_growth(self) -> int:
        """Terminal carry from the first low-edge symmetry break.

        For a palindromic reverse-add pair, the threshold word is mirrored.
        Its last non-identity reset is therefore the mirror of its first one,
        so with incoming carry zero the growth bit is exactly the sign of the
        first non-neutral low-half symbol.  No far-edge carry bit is state.
        """
        require_exact_oracle()
        if not self.symmetric:
            raise ValueError("symmetry growth requires a palindromic threshold word")
        occupied = self.low_payload | self.high_payload
        if not occupied:
            return 0
        first = (occupied & -occupied).bit_length() - 1
        return int(bool((self.high_payload >> first) & 1))

    @property
    def behavior_key(self) -> tuple[object, ...]:
        require_exact_oracle()
        return CarryResetSignature.from_threshold(self).canonical_key

    @property
    def description_bits(self) -> int:
        require_exact_oracle()
        stored_width = (self.width + 1) // 2 if self.symmetric else self.width
        return bit_width(self.base) + bit_width(self.width) + 1 + 2 * stored_width


@dataclass(frozen=True, slots=True)
class CarryResetSignature:
    """Minimal extensional carry-boundary itinerary.

    Before the first constant reset every boundary equals the incoming carry.
    Afterwards only positions where the constant reset value *changes* affect
    any boundary output.  Neutral symbols and repeated resets to the current
    constant are observationally redundant and are removed.
    """

    base: int
    width: int
    resets: tuple[tuple[int, int], ...]

    def __post_init__(self) -> None:
        require_exact_oracle()
        last_pos = -1
        last_value = None
        for pos, value in self.resets:
            if not 0 <= pos < self.width or value not in (0, 1) or pos <= last_pos:
                raise ValueError(self.resets)
            if last_value is not None and value == last_value:
                raise ValueError("redundant equal reset is noncanonical")
            last_pos, last_value = pos, value

    @classmethod
    def from_threshold(cls, threshold: CarryThresholdSignature) -> CarryResetSignature:
        require_exact_oracle()
        resets: list[tuple[int, int]] = []
        current: int | None = None
        low, high = threshold.low_mask, threshold.high_mask
        for pos in range(threshold.width):
            value = 0 if ((low >> pos) & 1) else 1 if ((high >> pos) & 1) else None
            if value is not None and value != current:
                resets.append((pos, value))
                current = value
        return cls(threshold.base, threshold.width, tuple(resets))

    @classmethod
    def from_pair(cls, pair: Sequence[int], *, base: int) -> CarryResetSignature:
        require_exact_oracle()
        return cls.from_threshold(CarryThresholdSignature.from_pair(pair, base=base))

    @property
    def canonical_key(self) -> tuple[object, ...]:
        require_exact_oracle()
        return ("carry-reset", self.base, self.width, self.resets)

    @property
    def behavior_key(self) -> tuple[object, ...]:
        require_exact_oracle()
        return self.canonical_key

    @property
    def description_bits(self) -> int:
        require_exact_oracle()
        pos_bits = bit_width(max(1, self.width - 1))
        return (
            bit_width(self.base)
            + bit_width(self.width)
            + bit_width(len(self.resets))
            + len(self.resets) * (pos_bits + 1)
        )

    def final_carry(self, incoming: int = 0) -> int:
        """Return the terminal carry directly from the reset observer."""
        require_exact_oracle()
        incoming = int(incoming)
        if incoming not in (0, 1):
            raise ValueError(incoming)
        return self.resets[-1][1] if self.resets else incoming

    def boundary_mask(self, incoming: int = 0) -> tuple[int, int]:
        """Return ``(boundary_count, bitmask)`` without materializing a carry vector.

        A reset at digit position ``p`` changes boundary ``C_(p+1)``.  Runs of
        equal carry values are therefore emitted as integer range masks.  Work
        is proportional to the number of *changes*, not the digit width.
        """
        require_exact_oracle()
        incoming = int(incoming)
        if incoming not in (0, 1):
            raise ValueError(incoming)
        mask = 0
        current = incoming
        start = 0
        for pos, value in self.resets:
            end = pos
            if current and end >= start:
                mask |= ((1 << (end - start + 1)) - 1) << start
            current = value
            start = pos + 1
        if current and self.width >= start:
            mask |= ((1 << (self.width - start + 1)) - 1) << start
        return self.width + 1, mask

    def boundaries(self, incoming: int = 0) -> tuple[int, ...]:
        """Materialize boundaries only for proof/differential callers."""
        require_exact_oracle()
        width, mask = self.boundary_mask(incoming)
        return tuple((mask >> i) & 1 for i in range(width))

    def boundary_runs(self, incoming: int = 0) -> tuple[tuple[int, int], ...]:
        """Return run-length encoded carry boundaries without a carry vector."""
        require_exact_oracle()
        incoming = int(incoming)
        if incoming not in (0, 1):
            raise ValueError(incoming)
        runs: list[tuple[int, int]] = []
        current = incoming
        start = 0
        for pos, value in self.resets:
            end = pos + 1  # reset at digit p first affects boundary C_(p+1)
            if end > start:
                runs.append((current, end - start))
            current = value
            start = end
        end = self.width + 1
        if end > start:
            runs.append((current, end - start))
        return tuple((value, count) for value, count in runs if count)


CarryScanSignature = CarryThresholdSignature | CarryResetSignature


@dataclass(frozen=True, slots=True)
class CarryNonlinearAction:
    signature: CarryScanSignature
    carry_row: tuple[int, int]
    growth: int

    @property
    def base(self) -> int:
        require_exact_oracle()
        return self.signature.base

    @property
    def canonical_key(self) -> tuple[object, ...]:
        # The reset itinerary is the complete extensional boundary behavior.
        require_exact_oracle()
        return ("carry-nonlinear-action",) + self.signature.behavior_key[1:]

    def __post_init__(self) -> None:
        require_exact_oracle()


@dataclass(frozen=True, slots=True)
class CarryActionQuotientMetrics:
    seed: int
    base: int
    transitions: int
    unique_source_interfaces: int
    unique_nonlinear_actions: int
    nonlinear_action_reuses: int
    carry_scan_evaluations: int
    unique_theorem_interfaces: int
    live_rows_average: float
    live_rows_max: int
    threshold_bits_average: float
    threshold_bits_max: int
    reset_bits_average: float = 0.0
    reset_bits_max: int = 0
    selected_signature_bits_average: float = 0.0
    selected_signature_bits_max: int = 0

    def __post_init__(self) -> None:
        require_exact_oracle()


@dataclass(frozen=True, slots=True)
class CarryPortAction:
    """Complete carry output for both input ports, held as dyadic summaries."""

    action_id: int
    outputs: tuple[DyadicTile, DyadicTile]

    def __post_init__(self) -> None:
        require_exact_oracle()


class CarryActionQuotientArena:
    """Interner for exact source, theorem, and pre-scan nonlinear action keys."""

    __slots__ = (
        "_actions",
        "_affine_tile_actions",
        "_port_actions",
        "_port_compositions",
        "_port_keys",
        "_scan_evaluations",
        "_sources",
        "_theorems",
        "_tile_actions",
        "port_aliases",
        "port_requests",
    )

    def __init__(self) -> None:
        require_exact_oracle()
        self._sources: dict[tuple[object, ...], CarryActionInterface] = {}
        self._actions: dict[tuple[object, ...], CarryNonlinearAction] = {}
        self._theorems: set[tuple[object, ...]] = set()
        self._scan_evaluations = 0
        self._affine_tile_actions: dict[tuple[int, int, int, int], int] = {}
        self._port_actions: list[CarryPortAction] = []
        self._port_keys: dict[tuple[int, int], int] = {}
        self._tile_actions: dict[tuple[int, int], int] = {}
        self._port_compositions: dict[tuple[int, int], int] = {}
        self.port_aliases = 0
        self.port_requests = 0

    def _intern_port(self, zero: DyadicTile, one: DyadicTile) -> int:
        require_exact_oracle()
        key = zero.node_id, one.node_id
        found = self._port_keys.get(key)
        if found is not None:
            self.port_aliases += 1
            return found
        action_id = len(self._port_actions)
        self._port_actions.append(CarryPortAction(action_id, (zero, one)))
        self._port_keys[key] = action_id
        return action_id

    def compose_ports(self, before: int, after: int) -> int:
        """Compose complete emitted carry behavior using only ActionIDs."""
        require_exact_oracle()
        key = before, after
        found = self._port_compositions.get(key)
        if found is not None:
            return found
        a, b = self._port_actions[before], self._port_actions[after]
        zero = join(a.outputs[0], b.outputs[last_symbol(a.outputs[0])])
        one = join(a.outputs[1], b.outputs[last_symbol(a.outputs[1])])
        out = self._intern_port(zero, one)
        self._port_compositions[key] = out
        return out

    def port_action(self, tile: DyadicTile, *, base: int) -> int:
        """Epimorphism from exact spatial tiles to full carry port effects."""
        require_exact_oracle()
        self.port_requests += 1
        stack = [(tile, False)]
        while stack:
            node, ready = stack.pop()
            key = base, node.node_id
            if key in self._tile_actions:
                continue
            if node.symbol is not None:
                if not 0 <= node.symbol <= 2 * (base - 1):
                    raise ValueError(node.symbol)
                out = self._intern_port(
                    uniform(int(node.symbol >= base), node.level),
                    uniform(int(node.symbol + 1 >= base), node.level),
                )
            else:
                if node.left is None or node.right is None:
                    raise AssertionError(node)
                if not ready:
                    stack.extend(
                        ((node, True), (node.right, False), (node.left, False))
                    )
                    continue
                out = self.compose_ports(
                    self._tile_actions[base, node.left.node_id],
                    self._tile_actions[base, node.right.node_id],
                )
            self._tile_actions[key] = out
        return self._tile_actions[base, tile.node_id]

    def project_span(
        self, source: DyadicSpan, incoming: int, *, base: int
    ) -> tuple[DyadicSpan, int]:
        require_exact_oracle()
        if incoming not in (0, 1):
            raise ValueError(incoming)
        carry = incoming
        chunks: list[DyadicChunk] = []
        for chunk in source.chunks:
            action = self._port_actions[self.port_action(chunk.tile, base=base)]
            output = action.outputs[carry]
            chunks.append(DyadicChunk(chunk.start, output))
            carry = last_symbol(output)
        return DyadicSpan(source.start, source.length, tuple(chunks)), carry

    def _affine_port_action(
        self, a: DyadicTile, b: DyadicTile, base: int, modulus: int
    ) -> int:
        require_exact_oracle()
        stack = [(a, b, False)]
        while stack:
            x, y, ready = stack.pop()
            key = base, modulus, x.node_id, y.node_id
            if key in self._affine_tile_actions:
                continue
            if x.symbol is not None and y.symbol is not None:
                value = (x.symbol + y.symbol) % modulus
                if not 0 <= value <= 2 * (base - 1):
                    raise AssertionError(
                        "affine action is outside its certified pair domain"
                    )
                out = self._intern_port(
                    uniform(int(value >= base), x.level),
                    uniform(int(value + 1 >= base), x.level),
                )
            else:
                if (
                    x.left is None
                    or x.right is None
                    or y.left is None
                    or y.right is None
                ):
                    raise AssertionError("unaligned affine interface")
                if not ready:
                    stack.extend(
                        (
                            (x, y, True),
                            (x.right, y.right, False),
                            (x.left, y.left, False),
                        )
                    )
                    continue
                out = self.compose_ports(
                    self._affine_tile_actions[
                        base, modulus, x.left.node_id, y.left.node_id
                    ],
                    self._affine_tile_actions[
                        base, modulus, x.right.node_id, y.right.node_id
                    ],
                )
            self._affine_tile_actions[key] = out
        return self._affine_tile_actions[base, modulus, a.node_id, b.node_id]

    def project_affine_span(
        self, source: DyadicSpan, event: DyadicSpan, *, base: int, modulus: int
    ) -> tuple[DyadicSpan, int]:
        """Fuse affine evaluation and carry projection; never emit pair digits."""
        require_exact_oracle()
        if source.length != event.length:
            raise ValueError("affine projection width mismatch")
        source = retile_like(event, source)
        carry = 0
        chunks: list[DyadicChunk] = []
        for a, b in zip(source.chunks, event.chunks, strict=True):
            action_id = self._affine_port_action(a.tile, b.tile, base, modulus)
            output = self._port_actions[action_id].outputs[carry]
            carry = last_symbol(output)
            chunks.append(DyadicChunk(b.start, output))
        return DyadicSpan(event.start, event.length, tuple(chunks)), carry

    def retained_port_spans(self) -> tuple[DyadicSpan, ...]:
        """Both port outputs retained by each complete nonlinear action."""
        require_exact_oracle()
        return tuple(
            DyadicSpan(0, output.width, (DyadicChunk(0, output),))
            for action in self._port_actions
            for output in action.outputs
        )

    @property
    def retained_port_entries(self) -> int:
        """Charge action records and every spatial/compose memo reference."""
        require_exact_oracle()
        return (
            len(self._port_actions)
            + len(self._port_keys)
            + len(self._tile_actions)
            + len(self._port_compositions)
            + len(self._affine_tile_actions)
        )

    @property
    def port_action_count(self) -> int:
        require_exact_oracle()
        return len(self._port_actions)

    @staticmethod
    def interface(live: LiveCarryItinerary) -> CarryActionInterface:
        require_exact_oracle()
        pair = live.pair
        bits = pair_plane_bits(live.base)
        growths = _growth_bits(live.carries)
        q = sum(1 - g for g in growths)
        r = sum(growths)
        theorem = CarryTheoremInterface(
            primary_jet_from_digits(pair, degree=4, modulus=1 << bits).jet,
            (min(bits, q), min(4, r)),
            _cyclotomic_valuations(growths, bits=bits),
            len(pair),
        )
        return CarryActionInterface(
            live.base, tuple(_row_mask(row) for row in live.carries), theorem
        )

    def intern_source(self, live: LiveCarryItinerary) -> CarryActionInterface:
        require_exact_oracle()
        interface = self.interface(live)
        return self._sources.setdefault(interface.canonical_key, interface)

    def intern_action(self, live: LiveCarryItinerary) -> CarryNonlinearAction:
        require_exact_oracle()
        interface = self.intern_source(live)
        pair = live.pair
        threshold = CarryThresholdSignature.from_pair(pair, base=live.base)
        reset = CarryResetSignature.from_threshold(threshold)
        signature: CarryScanSignature = (
            reset if reset.description_bits < threshold.description_bits else threshold
        )
        key = ("carry-nonlinear-action",) + reset.canonical_key[1:]
        action = self._actions.get(key)
        if action is None:
            # The reset itinerary is already the complete extensional carry
            # observer.  Synthesize the packed boundary row and growth bit from
            # it directly; do not compile/materialize a second carry prefix.
            row_mask = reset.boundary_mask(0)
            growth = (
                threshold.symmetry_growth
                if threshold.symmetric
                else reset.final_carry(0)
            )
            if threshold.symmetric and growth != reset.final_carry(0):
                raise AssertionError(
                    "symmetry boundary germ disagrees with carry action"
                )
            action = CarryNonlinearAction(signature, row_mask, growth)
            self._actions[key] = action
        theorem_key = (interface.theorem.canonical_key, action.growth)
        self._theorems.add(theorem_key)
        return action

    @property
    def source_count(self) -> int:
        require_exact_oracle()
        return len(self._sources)

    @property
    def action_count(self) -> int:
        require_exact_oracle()
        return len(self._actions)

    @property
    def theorem_count(self) -> int:
        require_exact_oracle()
        return len(self._theorems)

    @property
    def scan_evaluations(self) -> int:
        require_exact_oracle()
        return self._scan_evaluations


def analyze_carry_action_quotient(
    seed: int, *, base: int = 10, transitions: int = 512
) -> CarryActionQuotientMetrics:
    require_exact_oracle()
    seed, base, transitions = int(seed), int(base), int(transitions)
    if seed < 0 or base < 3 or transitions < 0:
        raise ValueError((seed, base, transitions))
    horizon = event_memory_horizon(base)
    pair = reverse_pair_sums(seed, base)
    rows: list[tuple[int, ...]] = []
    from number_compiler.arithmetic.carry.event_memory import pair_step

    for _ in range(horizon):
        rows.append(carry_field(pair, base=base))
        pair, _ = pair_step(pair, base)
    live = LiveCarryItinerary.seed(rows, base=base)
    arena = CarryActionQuotientArena()
    counts: list[int] = []
    signature_bits: list[int] = []
    reset_bits: list[int] = []
    selected_bits: list[int] = []
    for __2 in range(transitions):
        threshold = CarryThresholdSignature.from_pair(live.pair, base=base)
        reset = CarryResetSignature.from_threshold(threshold)
        signature_bits.append(threshold.description_bits)
        reset_bits.append(reset.description_bits)
        selected_bits.append(min(threshold.description_bits, reset.description_bits))
        arena.intern_action(live)
        counts.append(live.row_count)
        live = live.advance()
    return CarryActionQuotientMetrics(
        seed,
        base,
        transitions,
        arena.source_count,
        arena.action_count,
        transitions - arena.action_count,
        arena.scan_evaluations,
        arena.theorem_count,
        (sum(counts) / len(counts)) if counts else 0.0,
        max(counts, default=0),
        (sum(signature_bits) / len(signature_bits)) if signature_bits else 0.0,
        max(signature_bits, default=0),
        (sum(reset_bits) / len(reset_bits)) if reset_bits else 0.0,
        max(reset_bits, default=0),
        (sum(selected_bits) / len(selected_bits)) if selected_bits else 0.0,
        max(selected_bits, default=0),
    )


__all__ = [
    "CarryActionInterface",
    "CarryActionQuotientArena",
    "CarryActionQuotientMetrics",
    "CarryNonlinearAction",
    "CarryResetSignature",
    "CarryScanSignature",
    "CarryTheoremInterface",
    "CarryThresholdSignature",
    "analyze_carry_action_quotient",
]
