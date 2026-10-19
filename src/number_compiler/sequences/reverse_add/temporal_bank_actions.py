"""Binary-squared, output-complete actions for guarded reverse/add interior banks.

These are *temporal* action programs, not sequential output generators.  Each
operator owns a transition on the complete certified finite bank and an SLP
of the synchronized F5, LT/EQ/GT, carry and conditional innovation-borrow
ports it emits.  Composition substitutes the earlier operator's exit state
into the later operator; binary squaring never reconstructs an intermediate
pair word or carry slab.

The uniform core requires the existing protected homogeneous-border theorem;
the alternating quiet bank additionally requires an authenticated no-growth
interval.  EQ-producing growth exits are exposed as guarded branches rather
than guessed future carries.  None of these guards is a whole-root theorem.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import Generic, TypeVar

from number_compiler.arithmetic.automata.temporal_slp import concatenate_temporal_slp
from number_compiler.arithmetic.fields.decimal_pair_partition import (
    DECIMAL_PAIR_BAND_NAMES,
    decimal_pair_word_projection,
)

from .temporal_bulk_moore import (
    AlternatingCore,
    UniformCarryCell,
    alternating_moore_certificate,
    future_uniform_cells,
)

S = TypeVar("S")
CHANNELS = (
    *DECIMAL_PAIR_BAND_NAMES,
    "carry",
    "borrow_identity",
    "borrow_reset",
)


@dataclass(frozen=True, slots=True)
class TemporalPortFrame:
    """One synchronized source phase, with derived (not guessed) borrow ports.

    `borrow_identity` / `borrow_reset` apply **only if the next innovation
    comparison is nongrowth**.  A growth comparison needs its shifted-width
    seam transducer and is not silently identified with these ports.
    """

    coefficients: tuple[int, ...]
    f5: tuple[int, ...]
    lt_low: tuple[int, ...]
    lt_high: tuple[int, ...]
    eq: tuple[int, ...]
    gt_low: tuple[int, ...]
    gt_high: tuple[int, ...]
    carry: tuple[int, ...]
    reflected_carries: tuple[int, int]
    reflected_xor: int
    reflected_digits: tuple[int, int]
    normalized_digits: tuple[int, ...]
    borrow_identity: tuple[int, ...]
    borrow_reset: tuple[int, ...]
    reflected_borrow_identity: tuple[int, int]
    reflected_borrow_reset: tuple[int, int]

    def __post_init__(self) -> None:
        n = len(self.coefficients)
        if n not in (1, 2):
            raise ValueError("only certified homogeneous or alternating bank phases")
        ports = (
            self.f5,
            self.lt_low,
            self.lt_high,
            self.eq,
            self.gt_low,
            self.gt_high,
            self.carry,
            self.normalized_digits,
            self.borrow_identity,
            self.borrow_reset,
        )
        if any(len(p) != n for p in ports):
            raise ValueError("misaligned bank mask and borrow outputs")
        projection = decimal_pair_word_projection(self.coefficients)
        if (
            self.f5 != projection.f5
            or (
                self.lt_low,
                self.lt_high,
                self.eq,
                self.gt_low,
                self.gt_high,
            )
            != projection.bands
        ):
            raise ValueError("pair ports disagree with exact five-band projection")
        for i, _coefficient in enumerate(self.coefficients):
            if not (0 <= self.normalized_digits[i] <= 9):
                raise ValueError("invalid decimal output digit")
            if any(
                x not in (0, 1)
                for x in (self.carry[i], self.borrow_identity[i], self.borrow_reset[i])
            ):
                raise ValueError("invalid carry/borrow port")
        if self.reflected_xor != (
            self.reflected_carries[0] ^ self.reflected_carries[1]
        ):
            raise ValueError("reflected carry XOR is not derived")

        for port in (
            self.reflected_carries,
            self.reflected_digits,
            self.reflected_borrow_identity,
            self.reflected_borrow_reset,
        ):
            if len(port) != 2:
                raise ValueError("two physical reflected ports required")

    def bits(self, name: str) -> tuple[int, ...]:
        if name not in CHANNELS:
            raise ValueError(f"unknown bank output channel: {name}")
        ports = {
            "lt_low": self.lt_low,
            "lt_high": self.lt_high,
            "eq": self.eq,
            "gt_low": self.gt_low,
            "gt_high": self.gt_high,
            "carry": self.carry,
            "borrow_identity": self.borrow_identity,
            "borrow_reset": self.borrow_reset,
        }
        return ports[name]


def _frame(
    s: tuple[int, ...],
    c: tuple[int, ...],
    digits: tuple[int, ...],
    identity: tuple[int, ...],
    reset: tuple[int, ...],
    *,
    reflected_carries: tuple[int, int],
    reflected_digits: tuple[int, int],
    reflected_identity: tuple[int, int],
    reflected_reset: tuple[int, int],
) -> TemporalPortFrame:
    projection = decimal_pair_word_projection(s)
    return TemporalPortFrame(
        s,
        projection.f5,
        *projection.bands,
        c,
        reflected_carries,
        reflected_carries[0] ^ reflected_carries[1],
        reflected_digits,
        digits,
        identity,
        reset,
        reflected_identity,
        reflected_reset,
    )


def uniform_frame(state: UniformCarryCell) -> TemporalPortFrame:
    next_state = state.successor()
    digits = state.emitted_digits
    rho = (next_state.left, next_state.right)
    identity = (
        int(
            (digits[0] == 0 and rho[0] == 0 and next_state.left == next_state.right)
            or (digits[0] == 9 and rho[0] == 1 and next_state.left == next_state.right)
        ),
        int(
            (digits[1] == 0 and rho[1] == 0 and next_state.left == next_state.right)
            or (digits[1] == 9 and rho[1] == 1 and next_state.left == next_state.right)
        ),
    )
    # A homogeneous phase has one source pair symbol. Retain each actual
    # oriented reflected port in the frame via carry and XOR; the two emitted
    # physical digits can differ for EQ. A mixed EQ phase is never silently
    # promoted to a persistent border-free action.
    return _frame(
        (state.coefficient,),
        (state.left,),
        (digits[0],),
        (identity[0],),
        (rho[0],),
        reflected_carries=(state.left, state.right),
        reflected_digits=digits,
        reflected_identity=identity,
        reflected_reset=rho,
    )


def alternating_frame(state: AlternatingCore) -> TemporalPortFrame:
    a, b = state.even_position, state.odd_position
    ka, kb = int(a > 9), int(b > 9)
    digits = (a + kb - 10 * ka, b + ka - 10 * kb)
    reset, identity = state.quiet_borrow_ports(digits)
    return _frame(
        (a, b),
        (ka, kb),
        digits,
        identity,
        reset,
        reflected_carries=(ka, kb),
        reflected_digits=digits,
        reflected_identity=identity,
        reflected_reset=reset,
    )


@dataclass(frozen=True, slots=True)
class _Node:
    """Hash-consed temporal SLP node; length measures generations, not digits."""

    tag: str
    length: int
    frame: TemporalPortFrame | None
    left: int
    right: int
    repeat: int
    counts: tuple[int, ...]
    digit_sums: tuple[int, int]
    digit_weighted_sums: tuple[int, int]


class _TemporalArena:
    def __init__(self) -> None:
        self.nodes = [
            _Node("empty", 0, None, -1, -1, 0, (0,) * len(CHANNELS), (0, 0), (0, 0))
        ]
        self.keys: dict[tuple[object, ...], int] = {}

    def _intern(self, key: tuple[object, ...], node: _Node) -> int:
        found = self.keys.get(key)
        if found is not None:
            return found
        idx = len(self.nodes)
        self.nodes.append(node)
        self.keys[key] = idx
        return idx

    def emit(self, frame: TemporalPortFrame) -> int:
        counts = tuple(sum(frame.bits(name)) for name in CHANNELS)
        return self._intern(
            ("emit", frame),
            _Node("emit", 1, frame, -1, -1, 1, counts, frame.reflected_digits, (0, 0)),
        )

    def repeat(self, child: int, times: int) -> int:
        if times <= 0 or child == 0:
            return 0
        if times == 1:
            return child
        q = self.nodes[child]
        copies = times
        while q.tag == "repeat":
            copies *= q.repeat
            child = q.left
            q = self.nodes[child]
        weighted_sums = (
            copies * q.digit_weighted_sums[0]
            + q.length * q.digit_sums[0] * copies * (copies - 1) // 2,
            copies * q.digit_weighted_sums[1]
            + q.length * q.digit_sums[1] * copies * (copies - 1) // 2,
        )
        return self._intern(
            ("repeat", child, copies),
            _Node(
                "repeat",
                q.length * copies,
                None,
                child,
                -1,
                copies,
                tuple(v * copies for v in q.counts),
                (q.digit_sums[0] * copies, q.digit_sums[1] * copies),
                weighted_sums,
            ),
        )

    def concat(self, a: int, b: int) -> int:
        return concatenate_temporal_slp(
            a,
            b,
            nodes=self.nodes,
            repeat=self.repeat,
            copies=lambda node: node.repeat,
            intern=self._intern,
            make_concat=lambda left, right, x, y: _Node(
                "concat",
                x.length + y.length,
                None,
                left,
                right,
                1,
                tuple(p + q for p, q in zip(x.counts, y.counts, strict=True)),
                (x.digit_sums[0] + y.digit_sums[0], x.digit_sums[1] + y.digit_sums[1]),
                (
                    x.digit_weighted_sums[0]
                    + y.digit_weighted_sums[0]
                    + x.length * y.digit_sums[0],
                    x.digit_weighted_sums[1]
                    + y.digit_weighted_sums[1]
                    + x.length * y.digit_sums[1],
                ),
            ),
        )

    def at(self, root: int, index: int) -> TemporalPortFrame:
        if type(index) is not int or not 0 <= index < self.nodes[root].length:
            raise IndexError(index)
        i = root
        while True:
            node = self.nodes[i]
            if node.tag == "emit":
                assert node.frame is not None
                return node.frame
            if node.tag == "repeat":
                i = node.left
                index %= self.nodes[i].length
            elif node.tag == "concat":
                left = self.nodes[node.left]
                if index < left.length:
                    i = node.left
                else:
                    index -= left.length
                    i = node.right
            else:
                raise AssertionError("invalid temporal SLP node")


@dataclass(frozen=True, slots=True)
class TemporalBankAction(Generic[S]):
    """Complete bank exit state and compressed synchronized output, for N ticks."""

    source: S
    target: S
    steps: int
    root: int
    arena: _TemporalArena
    guard: str

    def at(self, time_index: int) -> TemporalPortFrame:
        return self.arena.at(self.root, time_index)

    def count(self, name: str) -> int:
        if name not in CHANNELS:
            raise ValueError(f"unknown bank output channel: {name}")
        return self.arena.nodes[self.root].counts[CHANNELS.index(name)]

    def digit_sum(self, port: int) -> int:
        """Sum a powered emitted decimal digit port without unfolding phases."""
        if type(port) is not int or port not in (0, 1):
            raise ValueError("expected emitted local digit port 0 or 1")
        return self.arena.nodes[self.root].digit_sums[port]

    def digit_time_weighted_sum(self, port: int) -> int:
        """Sum t*digit[t] over t=0..steps-1 in the emitted temporal program."""
        if type(port) is not int or port not in (0, 1):
            raise ValueError("expected emitted local digit port 0 or 1")
        return self.arena.nodes[self.root].digit_weighted_sums[port]

    def then(self, later: TemporalBankAction[S]) -> TemporalBankAction[S]:
        if (
            self.arena is not later.arena
            or self.target != later.source
            or self.guard != later.guard
        ):
            raise ValueError("incompatible temporal-bank actions or output guards")
        return TemporalBankAction(
            self.source,
            later.target,
            self.steps + later.steps,
            self.arena.concat(self.root, later.root),
            self.arena,
            self.guard,
        )

    @property
    def compiled_nodes(self) -> int:
        return len(self.arena.nodes)


class _FiniteFutureBank(Generic[S]):
    """Full-table binary squaring, with intermediate ports pulled back by ID."""

    def __init__(
        self,
        states: tuple[S, ...],
        successor: Callable[[S], S],
        emission: Callable[[S], TemporalPortFrame],
        guard: str,
    ) -> None:
        self.states = states
        self.indices = {v: i for i, v in enumerate(states)}
        self.successor = successor
        self.emission = emission
        self.guard = guard
        self.arena = _TemporalArena()
        first: list[tuple[int, int]] = []
        for state in states:
            t = successor(state)
            if t not in self.indices:
                raise AssertionError("future bank not successor-closed")
            first.append((self.indices[t], self.arena.emit(emission(state))))
        self.layers = [tuple(first)]

    def square(self) -> int:
        old = self.layers[-1]
        new: list[tuple[int, int]] = []
        for mid, emitted in old:
            end, continuation = old[mid]
            new.append((end, self.arena.concat(emitted, continuation)))
        self.layers.append(tuple(new))
        return len(self.layers) - 1

    def _ensure(self, depth: int) -> None:
        while len(self.layers) < depth.bit_length():
            self.square()

    def power(self, source: S, steps: int) -> TemporalBankAction[S]:
        if type(steps) is not int or steps < 0:
            raise ValueError("temporal exponent must be a nonnegative integer")
        if not steps:
            return TemporalBankAction(source, source, 0, 0, self.arena, self.guard)
        # The entry map may have more representatives than the minimal
        # successor-closed future machine (22->12 or 324->100). Perform one
        # symbolic entry emission, then use ONLY minimal future states.
        first = self.arena.emit(self.emission(source))
        state = self.successor(source)
        remaining = steps - 1
        self._ensure(remaining)
        root = first
        shift = 0
        while remaining:
            if remaining & 1:
                end, program = self.layers[shift][self.indices[state]]
                root = self.arena.concat(root, program)
                state = self.states[end]
            remaining >>= 1
            shift += 1
        return TemporalBankAction(source, state, steps, root, self.arena, self.guard)


def uniform_future_bank() -> _FiniteFutureBank[UniformCarryCell]:
    return _FiniteFutureBank(
        future_uniform_cells(),
        lambda s: s.successor(),
        uniform_frame,
        "protected_homogeneous_reflected_ports",
    )


def alternating_quiet_bank() -> _FiniteFutureBank[AlternatingCore]:
    alternating_moore_certificate()
    alphabet = tuple(range(9)) + tuple(range(10, 19))
    states = tuple(
        sorted({AlternatingCore(a, b).quiet_step() for a in alphabet for b in alphabet})
    )
    return _FiniteFutureBank(
        states,
        lambda s: s.quiet_step(),
        alternating_frame,
        "protected_alternating_and_every_tick_nongrowth",
    )


def power_uniform_outputs(
    source: UniformCarryCell, steps: int
) -> TemporalBankAction[UniformCarryCell]:
    if source.coefficient == 9 and source.left != source.right and steps > 1:
        # A boolean 'trust me' is NOT an authenticated future port tape.
        # No caller may silently turn a conditional fixed-point hypothesis
        # into an unconditional indefinitely powered output.
        raise ValueError("asymmetric EQ needs certified future border ports")
    return uniform_future_bank().power(source, steps)


def power_alternating_outputs(
    source: AlternatingCore, steps: int, *, quiet_guarded: bool = False
) -> TemporalBankAction[AlternatingCore]:
    if steps > 0 and not quiet_guarded:
        raise ValueError(
            "alternating temporal power needs a no-growth border certificate"
        )
    return alternating_quiet_bank().power(source, steps)


@dataclass(frozen=True, slots=True)
class ConditionalEQGrowthExit:
    """Exact EQ birth after alternating growth, with FOUR guarded port branches.

    A supplied `(left,right)` pair authenticates only the following local
    stencil. It cannot be reused across later steps without new border guards.
    """

    from_state: AlternatingCore
    coefficient: int
    alternatives: tuple[tuple[tuple[int, int], int], ...]

    def next_with_ports(self, left: int, right: int) -> UniformCarryCell:
        if (left, right) not in tuple(item[0] for item in self.alternatives):
            raise ValueError("both authenticated reflected carry ports are required")
        return UniformCarryCell(9, left, right).successor()


def conditional_first_growth_exit(
    source: AlternatingCore, quiet_steps: int, *, quiet_guarded: bool = False
) -> UniformCarryCell | ConditionalEQGrowthExit:
    if quiet_steps > 0 and not quiet_guarded:
        raise ValueError("first-growth index needs an authenticated quiet border")
    state = power_alternating_outputs(source, quiet_steps, quiet_guarded=True).target
    t = (
        state.even_position
        + state.odd_position
        - 9 * (int(state.even_position > 9) + int(state.odd_position > 9))
    )
    if t != 9:
        k = int(t > 9)
        return UniformCarryCell(t, k, k)
    branches = tuple(
        (
            (left_carry, right_carry),
            UniformCarryCell(9, left_carry, right_carry).successor().coefficient,
        )
        for left_carry in (0, 1)
        for right_carry in (0, 1)
    )
    return ConditionalEQGrowthExit(state, 9, branches)


__all__ = [
    "CHANNELS",
    "ConditionalEQGrowthExit",
    "TemporalBankAction",
    "TemporalPortFrame",
    "alternating_frame",
    "alternating_quiet_bank",
    "conditional_first_growth_exit",
    "power_alternating_outputs",
    "power_uniform_outputs",
    "uniform_frame",
    "uniform_future_bank",
]
