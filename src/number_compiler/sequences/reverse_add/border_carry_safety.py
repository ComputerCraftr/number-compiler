"""Carry-safety ports for *every* finite decimal reverse/add border tile.

This is a complete finite edge *relation*, not a false future-carry oracle.
The incoming carry from the unseen middle is an input port.  A first non-9
symmetric coefficient in the protected edge tiles may puncture that port for
leading carry/growth observations.  Unresolved ingress remains conditional.

The one-digit specialization has the universal 26-state post-step image.  Its
simple cycles are discoverable without any seed or previously generated tape;
conditional cycles can be powered as output summaries but cannot authorize a
physical trajectory unless their entire ingress word is source-certified.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    apply_carry_fn,
)

_MAX_BORDER_WIDTH = 64


def reverse_k(value: int, k: int) -> int:
    """Reverse exactly k decimal positions, retaining leading zero cells."""
    if type(k) is not int or not 1 <= k <= _MAX_BORDER_WIDTH or type(value) is not int:
        raise ValueError("invalid fixed-width reversal")
    if not 0 <= value < 10**k:
        raise ValueError("word outside fixed-width window")
    out = 0
    for _ in range(k):
        out = 10 * out + value % 10
        value //= 10
    return out


@dataclass(frozen=True, slots=True)
class BorderTile:
    """Exact k-digit high/low windows of a source of width >=2k+1."""

    k: int
    high: int
    low: int

    def __post_init__(self) -> None:
        if type(self.k) is not int or not 1 <= self.k <= _MAX_BORDER_WIDTH:
            raise ValueError("invalid border width")
        base = 10**self.k
        if (
            type(self.high) is not int
            or type(self.low) is not int
            or not base // 10 <= self.high < base
            or not 0 <= self.low < base
        ):
            raise ValueError("invalid active border tile")

    @property
    def pairs(self) -> tuple[int, ...]:
        """Symmetric pair coefficients, outside in (LSD and MSD inward)."""
        k, high, low = self.k, self.high, self.low
        high_digits = tuple(int(x) for x in f"{high:0{k}d}")
        low_digits = tuple(int(x) for x in f"{low:0{k}d}"[::-1])
        return tuple(high_digits[i] + low_digits[i] for i in range(k))


@dataclass(frozen=True, slots=True)
class BilateralCarryAlternative:
    """One internally consistent low-to-high transfer, never two free bits."""

    middle_transfer: CarryFn
    high_carry: int
    target: BorderTile
    growth: int


@dataclass(frozen=True, slots=True)
class BilateralCarryPort:
    """Source-border relation retaining the lower overflow and middle map.

    For a width >= 2*K+1 source with K-cell low/high windows, the true
    high-window carry is ``F_middle(low_carry)``. The unknown future
    middle carries are *functions*, not independently chosen Booleans.
    """

    source: BorderTile
    low_sum: int
    low_digits: int
    low_carry: int
    alternatives: tuple[BilateralCarryAlternative, ...]

    def require_target(
        self, target: BorderTile, *, growth: int | None = None
    ) -> tuple[CarryFn, ...]:
        """Backwards-refine the admissible middle carry functions."""
        if type(target) is not BorderTile or target.k != self.source.k:
            raise ValueError("target has a different border window")
        if growth is not None and (type(growth) is not int or growth not in (0, 1)):
            raise ValueError("growth must be Boolean")
        return tuple(
            a.middle_transfer
            for a in self.alternatives
            if a.target == target and (growth is None or a.growth == growth)
        )

    def for_middle(self, transfer: CarryFn) -> BilateralCarryAlternative:
        """Apply one source-certified Q19 carry transfer to the forced low carry."""
        if type(transfer) is not CarryFn:
            raise TypeError("middle transfer must be an authenticated CarryFn")
        return next(a for a in self.alternatives if a.middle_transfer is transfer)

    def admissible_high_carries(self, target: BorderTile) -> tuple[int, ...]:
        return tuple(
            sorted({a.high_carry for a in self.alternatives if a.target == target})
        )


def border_bilateral_port(
    source: BorderTile,
    admitted_middle: tuple[CarryFn, ...] = (
        CarryFn.CONST0,
        CarryFn.ID,
        CarryFn.CONST1,
    ),
) -> BilateralCarryPort:
    """The exact K-digit border relation for specified middle carry maps.

    Low-side addition generates one carry into the middle. It is propagated
    through the *same* Q19 middle transfer before entering the high tile.
    No independent high-ingress choice is introduced.

    Admitting all three functions is conservative for an unknown future
    middle. A bank/SLP must certify the actual transfer at each time step
    before the relation can authorize a complete temporal return.
    """
    if type(source) is not BorderTile:
        raise TypeError("source must be a canonical border tile")
    if (
        type(admitted_middle) is not tuple
        or not admitted_middle
        or any(type(fn) is not CarryFn for fn in admitted_middle)
    ):
        raise ValueError("admitted middle transfers must be CarryFn values")
    base = 10**source.k
    low_sum = source.low + reverse_k(source.high, source.k)
    low_digits = low_sum % base
    low_carry = low_sum // base
    high_without_carry = source.high + reverse_k(source.low, source.k)
    alternatives = []
    for fn in dict.fromkeys(admitted_middle):
        ingress = apply_carry_fn(fn, low_carry)
        high_sum = high_without_carry + ingress
        growth = int(high_sum >= base)
        high_digits = high_sum // 10 if growth else high_sum
        if not base // 10 <= high_digits < base:
            raise ValueError("leading border loses its canonical width")
        alternatives.append(
            BilateralCarryAlternative(
                fn,
                ingress,
                BorderTile(source.k, high_digits, low_digits),
                growth,
            )
        )
    return BilateralCarryPort(
        source, low_sum, low_digits, low_carry, tuple(alternatives)
    )


@dataclass(frozen=True, slots=True)
class BilateralCyclePort:
    """One border-cycle letter with both coupled carry ends retained."""

    source: BorderTile
    target: BorderTile
    growth: int
    low_carry: int
    admitted_middle: tuple[CarryFn, ...]

    def admits(self, middle: CarryFn) -> bool:
        return middle in self.admitted_middle


def bilateral_cycle_letter(
    source: BorderTile, target: BorderTile, growth: int
) -> BilateralCyclePort:
    """Derive the middle-map constraint of one certified or candidate edge."""
    if type(growth) is not int or growth not in (0, 1):
        raise ValueError("growth must be Boolean")
    port = border_bilateral_port(source)
    permitted = port.require_target(target, growth=growth)
    if not permitted:
        raise ValueError("target contradicts the two-sided border relation")
    return BilateralCyclePort(source, target, growth, port.low_carry, permitted)


@dataclass(frozen=True, slots=True)
class CarrySafetyEdge:
    carry_in: int
    target: BorderTile
    growth: int


@dataclass(frozen=True, slots=True)
class CarrySafetyPort:
    """All two ingress responses and their *proved* punctured projections."""

    source: BorderTile
    edges: tuple[CarrySafetyEdge, ...]
    first_inner_non9: int | None
    forced_msd_ingress: int | None
    forced_growth: int | None
    common_prefix: str
    common_suffix: str

    @property
    def outgoing_low_carry(self) -> int:
        """Carry emitted by the *known* low tile into the middle Q19 bank."""
        return border_bilateral_port(self.source).low_carry

    def bilateral(self) -> BilateralCarryPort:
        """Full two-ended conditional relation, not merely a high carry."""
        return border_bilateral_port(self.source)

    @property
    def punctured_growth(self) -> bool:
        return self.forced_growth is not None

    def require_growth(self, bit: int) -> tuple[int, ...]:
        """Only ingresses compatible with a proposed growth control symbol."""
        if type(bit) is not int or bit not in (0, 1):
            raise ValueError("growth port must be Boolean")
        return tuple(edge.carry_in for edge in self.edges if edge.growth == bit)

    def require_target(self, target: BorderTile) -> tuple[int, ...]:
        """Backwards-puncture the carry needed by one exact border transition."""
        if type(target) is not BorderTile:
            raise TypeError("target must be a canonical border tile")
        return tuple(edge.carry_in for edge in self.edges if edge.target == target)


def _common_start(values: tuple[str, ...]) -> str:
    if not values:
        return ""
    size = min(map(len, values))
    for i in range(size):
        if any(word[i] != values[0][i] for word in values[1:]):
            return values[0][:i]
    return values[0][:size]


def _common_end(values: tuple[str, ...]) -> str:
    if not values:
        return ""
    reversed_words = tuple(word[::-1] for word in values)
    return _common_start(reversed_words)[::-1]


def border_carry_port(
    source: BorderTile, admitted_inner: tuple[int, ...] = (0, 1)
) -> CarrySafetyPort:
    """Compute a sound carry-labelled border relation at any window width.

    The carry starts at the *inner edge of the high tile*, not the MSD.
    The first non-EQ pair looking inward FROM the MSD is the last reset
    before its leading cell; it overrides any deeper carry resets. It can
    therefore force the MSD ingress while the next K-digit high tile still
    retains alternative lower digits.
    """
    if type(source) is not BorderTile:
        raise TypeError("source must be a canonical border tile")
    if (
        type(admitted_inner) is not tuple
        or not admitted_inner
        or any(type(c) is not int or c not in (0, 1) for c in admitted_inner)
    ):
        raise ValueError("incoming carry letters must be Boolean")
    bilateral = border_bilateral_port(source)
    # Every high ingress is obtained from an actual middle transfer.  This
    # legacy high-bit projection keeps backwards-compatible (0,1) order;
    # use .bilateral() when a temporal action needs the correlated ports.
    edges = []
    for incoming in dict.fromkeys(admitted_inner):
        candidates = tuple(
            a for a in bilateral.alternatives if a.high_carry == incoming
        )
        if not candidates:
            continue
        candidate = candidates[0]
        edges.append(CarrySafetyEdge(incoming, candidate.target, candidate.growth))

    # Scan s_1,s_2,...: the first non-EQ when looking inward from the
    # MSD overrides any deeper carry reset, so it determines ingress to s_0.
    first = None
    msd_ingress = None
    for i in range(1, source.k):
        coefficient = source.pairs[i]
        if coefficient != 9:
            first, msd_ingress = i, int(coefficient > 9)
            break
    growths = {edge.growth for edge in edges}
    return CarrySafetyPort(
        source,
        tuple(edges),
        first,
        msd_ingress,
        next(iter(growths)) if len(growths) == 1 else None,
        _common_start(tuple(f"{edge.target.high:0{source.k}d}" for edge in edges)),
        _common_end(tuple(f"{edge.target.low:0{source.k}d}" for edge in edges)),
    )


Border1 = tuple[int, int]


def universal_one_digit_states() -> tuple[Border1, ...]:
    """All and only the 26 reachable one-step outer-digit states."""
    result: set[Border1] = set()
    for a in range(1, 10):
        for b in range(10):
            for edge in border_carry_port(BorderTile(1, a, b)).edges:
                result.add((edge.target.high, edge.target.low))
    return tuple(sorted(result))


@dataclass(frozen=True, slots=True)
class ConditionalBorderCycle:
    """A geometrically closed border word with unproved future carry inputs.

    An ingress letter None means *both* physical carry values give exactly
    the same next one-digit border and growth bit: that port was genuinely
    punctured. A 0/1 letter is a REQUIRED FUTURE INPUT, not an assertion that
    this input is produced indefinitely by a given source.
    """

    states: tuple[Border1, ...]
    incoming: tuple[int | None, ...]
    growth: tuple[int, ...]
    source_universal: Literal[False] = False
    simple: bool = True

    def __post_init__(self) -> None:
        if not self.states or not (
            len(self.states) == len(self.incoming) == len(self.growth)
        ):
            raise ValueError("cycle must have aligned states/ports/growth")
        if self.simple and len(set(self.states)) != len(self.states):
            raise ValueError("candidate must be a simple cycle")
        if self.source_universal is not False:
            raise ValueError("border return is conditional on future carry ports")
        for i, (source, port, grow) in enumerate(
            zip(self.states, self.incoming, self.growth, strict=True)
        ):
            target = self.states[(i + 1) % len(self.states)]
            safety = border_carry_port(BorderTile(1, *source))
            allowed = safety.require_target(BorderTile(1, *target))
            if (
                (port is None and allowed != (0, 1))
                or (port is not None and (type(port) is not int or port not in allowed))
                or (type(grow) is not int or grow not in (0, 1))
                or any(
                    edge.growth != grow
                    for edge in safety.edges
                    if edge.carry_in in (allowed if port is None else (port,))
                )
            ):
                raise ValueError("invalid conditional border-cycle port")

    @property
    def steps(self) -> int:
        return len(self.states)

    @property
    def width_growth(self) -> int:
        return sum(self.growth)

    @property
    def skew_moment(self) -> int:
        return sum((self.steps - 1 - i) * g for i, g in enumerate(self.growth))

    @property
    def has_trailing_zero(self) -> bool:
        return (1, 0) in self.states

    @property
    def needs_future_carry_certificate(self) -> bool:
        return any(port is not None for port in self.incoming)

    def bilateral_ports(self) -> tuple[BilateralCyclePort, ...]:
        """Return all low-to-high middle transfer guards around this cycle."""
        return tuple(
            bilateral_cycle_letter(
                BorderTile(1, *state),
                BorderTile(1, *self.states[(i + 1) % self.steps]),
                bit,
            )
            for i, (state, bit) in enumerate(zip(self.states, self.growth, strict=True))
        )

    def conditional_repeat(self, count: int) -> tuple[int, int, int]:
        """(duration, growth, quadratic skew) assuming repeated port witness."""
        if type(count) is not int or count < 0:
            raise ValueError("nonnegative cycle repeat expected")
        duration = self.steps * count
        growth = self.width_growth * count
        skew = self.skew_moment * count + self.steps * self.width_growth * (
            count * (count - 1) // 2
        )
        return duration, growth, skew


def conditional_return_from_trace(
    outer_pairs: tuple[Border1, ...], growth: tuple[int, ...]
) -> ConditionalBorderCycle:
    """Convert a fully authenticated finite outer return to a port-labelled word.

    A certificate may prove one *finite* return without proving another: the
    inner Q19 root can change while the outer pair and growth word repeat.
    Hence the returned ``conditional_repeat`` is algebra, not admission.
    """
    if (
        type(outer_pairs) is not tuple
        or len(outer_pairs) < 2
        or outer_pairs[0] != outer_pairs[-1]
        or type(growth) is not tuple
        or len(growth) != len(outer_pairs) - 1
    ):
        raise ValueError("a complete finite outer-border return is required")
    ports: list[int | None] = []
    for source, target, bit in zip(
        outer_pairs[:-1], outer_pairs[1:], growth, strict=True
    ):
        allowed = border_carry_port(BorderTile(1, *source)).require_target(
            BorderTile(1, *target)
        )
        if not allowed:
            raise ValueError("outer trace contains an impossible border edge")
        matching = border_carry_port(BorderTile(1, *source)).require_growth(bit)
        if any(h not in matching for h in allowed):
            raise ValueError("outer trace growth bit disagrees with carry output")
        ports.append(None if allowed == (0, 1) else allowed[0])
    return ConditionalBorderCycle(
        outer_pairs[:-1],
        tuple(ports),
        growth,
        simple=len(set(outer_pairs[:-1])) == len(outer_pairs) - 1,
    )


@dataclass(frozen=True, slots=True)
class ConditionalWindowReturn:
    """Any K-digit finite border return with exact conditional carry ports.

    The return can be compiled and its growth/skew outputs repeated without
    repeating numeric states. Nothing here certifies that a real middle Q19
    grammar satisfies the port program again after the first return.
    """

    states: tuple[BorderTile, ...]
    incoming: tuple[int | None, ...]
    growth: tuple[int, ...]
    source_universal: Literal[False] = False

    def __post_init__(self) -> None:
        if (
            not self.states
            or len(self.states) != len(self.incoming)
            or len(self.states) != len(self.growth)
            or self.source_universal is not False
        ):
            raise ValueError("invalid conditional border-window return")
        k = self.states[0].k
        if any(state.k != k for state in self.states):
            raise ValueError("border window return changed its active K")
        for i, (state, port, bit) in enumerate(
            zip(self.states, self.incoming, self.growth, strict=True)
        ):
            nxt = self.states[(i + 1) % len(self.states)]
            carry = border_carry_port(state)
            permitted = carry.require_target(nxt)
            if (
                not permitted
                or (port is None and permitted != (0, 1))
                or (
                    port is not None
                    and (type(port) is not int or port not in permitted)
                )
                or type(bit) is not int
                or bit not in (0, 1)
                or any(
                    edge.growth != bit
                    for edge in carry.edges
                    if edge.carry_in in (permitted if port is None else (port,))
                )
            ):
                raise ValueError("invalid conditional carry or growth edge")

    @property
    def steps(self) -> int:
        return len(self.states)

    @property
    def width_growth(self) -> int:
        return sum(self.growth)

    @property
    def skew_moment(self) -> int:
        return sum((self.steps - 1 - i) * g for i, g in enumerate(self.growth))

    @property
    def needs_future_carry_certificate(self) -> bool:
        return any(x is not None for x in self.incoming)

    def bilateral_ports(self) -> tuple[BilateralCyclePort, ...]:
        """Preserve the forced bottom carry for every K-digit edge."""
        return tuple(
            bilateral_cycle_letter(
                state,
                self.states[(i + 1) % self.steps],
                bit,
            )
            for i, (state, bit) in enumerate(zip(self.states, self.growth, strict=True))
        )

    def conditional_repeat(self, count: int) -> tuple[int, int, int]:
        if type(count) is not int or count < 0:
            raise ValueError("nonnegative conditional border repeat expected")
        return (
            self.steps * count,
            self.width_growth * count,
            count * self.skew_moment
            + self.steps * self.width_growth * (count * (count - 1) // 2),
        )


def conditional_window_return_from_trace(
    tiles: tuple[BorderTile, ...], growth: tuple[int, ...]
) -> ConditionalWindowReturn:
    """Derive the minimal required ingress word for any *given* K-cycle.

    Caller-supplied tiles are hypothetical until a Q19 boundary certificate
    proves them. Even certified finite tiles do NOT certify future repeats.
    """
    if (
        type(tiles) is not tuple
        or len(tiles) < 2
        or tiles[0] != tiles[-1]
        or type(growth) is not tuple
        or len(growth) != len(tiles) - 1
    ):
        raise ValueError("a full closed K-digit tile path is required")
    ports: list[int | None] = []
    for old, new, bit in zip(tiles[:-1], tiles[1:], growth, strict=True):
        port = border_carry_port(old)
        admitted = port.require_target(new)
        if not admitted or any(
            edge.growth != bit for edge in port.edges if edge.carry_in in admitted
        ):
            raise ValueError("border return contains an impossible edge")
        ports.append(None if admitted == (0, 1) else admitted[0])
    return ConditionalWindowReturn(tiles[:-1], tuple(ports), growth)


def enumerate_one_digit_cycles() -> tuple[ConditionalBorderCycle, ...]:
    """Discover all simple cycles of the 26-state core with carry requirements.

    The canonical minimum state on a cycle is its first state. A merged
    source/target edge represents h=both only if that is an exact one-digit
    output equivalence, not a claimed identity of the inner digit strings.
    """
    states = universal_one_digit_states()
    lookup = {state: i for i, state in enumerate(states)}
    adjacency: list[list[tuple[int, int | None, int]]] = []
    for state in states:
        safety = border_carry_port(BorderTile(1, *state))
        by_target: dict[Border1, list[CarrySafetyEdge]] = {}
        for edge in safety.edges:
            by_target.setdefault((edge.target.high, edge.target.low), []).append(edge)
        row = []
        for dst, edges in by_target.items():
            row.append(
                (
                    lookup[dst],
                    None if len(edges) == 2 else edges[0].carry_in,
                    edges[0].growth,
                )
            )
        adjacency.append(sorted(row))
    cycles: list[ConditionalBorderCycle] = []
    for start in range(len(states)):
        stack: list[
            tuple[int, tuple[int, ...], tuple[int | None, ...], tuple[int, ...]]
        ] = [(start, (start,), (), ())]
        while stack:
            current, path, ports, growths = stack.pop()
            for target, port, grow in adjacency[current]:
                if target == start:
                    cycles.append(
                        ConditionalBorderCycle(
                            tuple(states[i] for i in path),
                            ports + (port,),
                            growths + (grow,),
                        )
                    )
                elif target > start and target not in path:
                    stack.append(
                        (target, path + (target,), ports + (port,), growths + (grow,))
                    )
    return tuple(sorted(cycles, key=lambda x: (x.steps, x.states, x.incoming)))


__all__ = [
    "BilateralCarryAlternative",
    "BilateralCarryPort",
    "BilateralCyclePort",
    "BorderTile",
    "CarrySafetyEdge",
    "CarrySafetyPort",
    "ConditionalBorderCycle",
    "ConditionalWindowReturn",
    "bilateral_cycle_letter",
    "border_bilateral_port",
    "border_carry_port",
    "conditional_return_from_trace",
    "conditional_window_return_from_trace",
    "enumerate_one_digit_cycles",
    "reverse_k",
    "universal_one_digit_states",
]
