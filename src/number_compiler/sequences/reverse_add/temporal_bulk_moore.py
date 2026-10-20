"""An exact future-Moore clock for *guarded homogeneous interior* carry cells.

This module is deliberately separate from the whole-word temporal successor.
On an interior interval where a symmetric pair coefficient and its reflected
carry ports are homogeneous, both growth and nongrowth stencils reduce to

    t = 2*s - 9*(left + right).

A non-EQ coefficient resets both ports, while s=9 transports them.  The
resulting 22 admissible entry configurations have only twelve different
one-step-and-future behaviors.  The ten even coefficients and two oriented
asymmetric EQ wires form a closed, completely Moore-minimal twelve-state
future controller; its cycles have periods 1, 2 and 6.

This is a source-independent proof for admitted *interior* regions, NOT a
certificate for the global reverse-add map: finite boundary fronts and
external EQ carry ingress remain separate guards.  In particular, an
unprotected asymmetric EQ run cannot be pumped through an unknown future
border change.  No original-source slab, generation number, or seed occurs
in any action identity.
"""

from __future__ import annotations

from dataclasses import dataclass
from hashlib import sha256
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from .temporal_bank_actions import ConditionalEQGrowthExit, TemporalBankAction


def punctured_non_eq_interior_step(
    left: int,
    center: int,
    right: int,
    *,
    growth: int,
) -> int:
    """Exact source-only radius-one interior stencil if no input is EQ=9.

    The palindrome plus RESET0/RESET1 gives each physical carry directly
    from its immediately preceding pair coefficient, in BOTH reflected
    halves. The future pair coefficient is then:

        nongrowth: 2*s + K(left) + K(right) - 20*K(s)
        growth:    left + s - 9*(K(left) + K(s))

    The former's EQ birth requires `center in {4,14}` and XOR of
    neighboring carry domains. A growth EQ birth is a normalized adjacent
    digit-pair event. This formula is NOT admissible if any tested input is 9.
    """
    if growth not in (0, 1) or type(growth) is not int:
        raise ValueError("growth is one Boolean bit")
    for value in (left, center, right):
        if type(value) is not int or not 0 <= value <= 18 or value == 9:
            raise ValueError("local no-EQ stencil requires three non-9 coefficients")
    a, b, c = int(left > 9), int(center > 9), int(right > 9)
    t = left + center - 9 * (a + b) if growth else 2 * center + a + c - 20 * b
    if not 0 <= t <= 18:
        raise AssertionError("local source-only stencil left decimal coefficient range")
    return t


@dataclass(frozen=True, slots=True, order=True)
class UniformCarryCell:
    """Interior coefficient and its two *actual* reflected carry ports."""

    coefficient: int
    left: int
    right: int

    def __post_init__(self) -> None:
        s, a, b = self.coefficient, self.left, self.right
        if type(s) is not int or not 0 <= s <= 18:
            raise ValueError("decimal pair coefficient must be 0..18")
        if (
            type(a) is not int
            or type(b) is not int
            or a not in (0, 1)
            or b not in (0, 1)
        ):
            raise ValueError("carry ports must be Boolean")
        if s != 9 and (a != b or a != int(s > 9)):
            raise ValueError("homogeneous non-EQ core must have reset carries")

    @property
    def next_coefficient(self) -> int:
        return 2 * self.coefficient - 9 * (self.left + self.right)

    def successor(self) -> UniformCarryCell:
        """Exact common growth/nongrowth *interior* polynomial stencil."""
        t = self.next_coefficient
        if t == 9:
            # Only the asymmetric EQ case can have t=9; identity transports
            # the oriented two-sided ports, rather than inventing a reset.
            return UniformCarryCell(9, self.left, self.right)
        k = int(t > 9)
        return UniformCarryCell(t, k, k)

    @property
    def emitted_digits(self) -> tuple[int, int]:
        """Two reflected normalized digits emitted at this time."""
        s = self.coefficient
        return (
            s + self.left - 10 * (self.left if s == 9 else int(s > 9)),
            s + self.right - 10 * (self.right if s == 9 else int(s > 9)),
        )

    @property
    def next_innovation_identity_gate(self) -> bool:
        """Exact nongrowth *bulk* 0/9 identity-borrow exception.

        Output digits from this phase are input digits for the following
        innovation-borrow comparison.  The next reflected carry ports are
        those of the successor; no independent future borrow port is read.
        """
        t = self.successor()
        a, _ = self.emitted_digits
        return (a == 0 and t.left == t.right == 0) or (
            a == 9 and t.left == t.right == 1
        )


def source_uniform_cells() -> tuple[UniformCarryCell, ...]:
    out = [UniformCarryCell(s, int(s > 9), int(s > 9)) for s in range(19) if s != 9]
    out.extend(UniformCarryCell(9, a, b) for a in (0, 1) for b in (0, 1))
    return tuple(sorted(out))


def future_uniform_cells() -> tuple[UniformCarryCell, ...]:
    return tuple(sorted({cell.successor() for cell in source_uniform_cells()}))


@dataclass(frozen=True, slots=True)
class UniformBulkMooreCertificate:
    """Complete Myhill-Nerode quotient for the declared future-output port."""

    entry_states: int
    minimal_future_states: int
    unconditional_reset_states: int
    conditional_eq_wire_states: int
    classes: tuple[int, ...]
    future_states: tuple[UniformCarryCell, ...]
    transition: tuple[int, ...]
    cycle_lengths: tuple[int, ...]
    digest: str


def _part(signatures: tuple[object, ...]) -> tuple[int, ...]:
    seen: dict[object, int] = {}
    ids: list[int] = []
    for sig in signatures:
        if sig not in seen:
            seen[sig] = len(seen)
        ids.append(seen[sig])
    return tuple(ids)


def uniform_bulk_moore_certificate() -> UniformBulkMooreCertificate:
    """Minimize the successor-output machine over *all* coherent bulk ports.

    Initial emission is (next coefficient, next reflected carry ports,
    next delayed innovation identity gate). Future outputs are observed for
    every depth >=1; current unnormalized entry digits are entry data, not
    future-control identity.  Equal successors are hence Moore-equivalent.
    All non-equivalent image states have a one-step separating output.
    """
    sources = source_uniform_cells()
    images = future_uniform_cells()
    ids: dict[UniformCarryCell, int] = {q: i for i, q in enumerate(images)}
    classes = _part(
        tuple(
            (
                s.successor().coefficient,
                s.successor().left,
                s.successor().right,
                s.successor().next_innovation_identity_gate,
            )
            for s in sources
        )
    )
    while True:
        nxt = _part(
            tuple(
                (classes[i], classes[sources.index(s.successor())])
                for i, s in enumerate(sources)
            )
        )
        if nxt == classes:
            break
        classes = nxt
    if len(set(classes)) != len(images):
        raise AssertionError("future controller is not image-minimal")
    # Verify the entire 22-state table, including the admission split at 9.
    for a, s in enumerate(sources):
        for b in range(a):
            if classes[a] == classes[b]:
                t = sources[b]
                if (
                    s.successor() != t.successor()
                    or classes[sources.index(s.successor())]
                    != classes[sources.index(t.successor())]
                ):
                    raise AssertionError("merged distinct future output/transition")
    transition = tuple(ids[s.successor()] for s in images)
    cycle_lengths: list[int] = []
    for q in images:
        seen: dict[UniformCarryCell, int] = {}
        x = q
        while x not in seen:
            seen[x] = len(seen)
            x = x.successor()
        cycle_lengths.append(len(seen) - seen[x])
    h = sha256()
    for x in sources:
        y = x.successor()
        h.update(
            bytes(
                (
                    x.coefficient,
                    x.left,
                    x.right,
                    y.coefficient,
                    y.left,
                    y.right,
                    int(x.next_innovation_identity_gate),
                )
            )
        )
    unconditional = sum(q.coefficient != 9 for q in images)
    conditional = len(images) - unconditional
    if (unconditional, conditional) != (10, 2):
        raise AssertionError("conditional EQ-wire states merged into resetting states")
    return UniformBulkMooreCertificate(
        len(sources),
        len(images),
        unconditional,
        conditional,
        classes,
        images,
        transition,
        tuple(cycle_lengths),
        h.hexdigest(),
    )


@dataclass(frozen=True, slots=True)
class UniformBulkPower:
    """A genuinely powered, occurrence-independent homogeneous-core action.

    Prefix and period are bounded by 1 and 6 for this complete finite
    controller; the caller supplies the time exponent as structural geometry.
    """

    source: UniformCarryCell
    preperiod: tuple[UniformCarryCell, ...]
    period: tuple[UniformCarryCell, ...]

    @classmethod
    def compile(cls, source: UniformCarryCell) -> UniformBulkPower:
        uniform_bulk_moore_certificate()
        seen: dict[UniformCarryCell, int] = {}
        order: list[UniformCarryCell] = []
        q = source
        while q not in seen:
            seen[q] = len(order)
            order.append(q)
            q = q.successor()
        n = seen[q]
        if len(order) - n not in (1, 2, 6):
            raise AssertionError("unknown homogeneous temporal orbit")
        return cls(source, tuple(order[:n]), tuple(order[n:]))

    def at(self, depth: int) -> UniformCarryCell:
        """Direct T^depth query with no chronological transitions."""
        if type(depth) is not int or depth < 0:
            raise ValueError("nonnegative generation displacement required")
        if depth < len(self.preperiod):
            return self.preperiod[depth]
        return self.period[(depth - len(self.preperiod)) % len(self.period)]

    def temporal_action(self, steps: int) -> TemporalBankAction[UniformCarryCell]:
        """Binary-square the synchronized future mask/carry/borrow grammar.

        A missing asymmetric-EQ future border certificate is a hard refusal.
        Output programs and complete local phase state evolve together.
        """
        from .temporal_bank_actions import power_uniform_outputs

        return power_uniform_outputs(self.source, steps)

    @property
    def period_length(self) -> int:
        return len(self.period)


__all__ = [
    "UniformBulkMooreCertificate",
    "UniformBulkPower",
    "UniformCarryCell",
    "future_uniform_cells",
    "punctured_non_eq_interior_step",
    "source_uniform_cells",
    "uniform_bulk_moore_certificate",
]


@dataclass(frozen=True, slots=True, order=True)
class AlternatingCore:
    """Two spatial phases on a symmetric period-two source, neither EQ=9."""

    even_position: int
    odd_position: int

    def __post_init__(self) -> None:
        for s in (self.even_position, self.odd_position):
            if type(s) is not int or not 0 <= s <= 18 or s == 9:
                raise ValueError(
                    "alternating core requires source coefficients other than 9"
                )

    def quiet_step(self) -> AlternatingCore:
        a, b = self.even_position, self.odd_position
        return AlternatingCore(
            punctured_non_eq_interior_step(b, a, b, growth=0),
            punctured_non_eq_interior_step(a, b, a, growth=0),
        )

    def quiet_borrow_ports(
        self, digits: tuple[int, int]
    ) -> tuple[tuple[int, int], tuple[int, int]]:
        """Both next-innovation exceptional 0/9 wires, with NO borrow history.

        The source periodic pair and reset mask produce X_(n+1) digits;
        its no-growth successor produces the next pair reset mask. The
        reflected rho/eta carry ports of the *following* subtraction are
        therefore derived by the same period-two transfer, never guessed.
        This is conditional on the following step being nongrowth, where
        the unshifted innovation-borrow law applies.
        """
        future = self.quiet_step()
        next_k = (int(future.even_position > 9), int(future.odd_position > 9))
        out: list[int] = []
        for i, d in enumerate(digits):
            rho = next_k[i]
            eta = next_k[1 - i]
            out.append(
                int((d == 0 and rho == eta == 0) or (d == 9 and rho == eta == 1))
            )
        return next_k, (out[0], out[1])

    def growth_step(self) -> UniformCarryCell | None:
        """Growth collapses the entire alternating core to ONE coefficient.

        If that coefficient is EQ=9, the future ports are not determined
        by this core; returning None demands the separately authenticated
        first-non-9/border response instead of inventing one.
        """
        a, b = self.even_position, self.odd_position
        t = punctured_non_eq_interior_step(b, a, b, growth=1)
        if t != punctured_non_eq_interior_step(a, b, a, growth=1):
            raise AssertionError("growth failed to synchronize both spatial phases")
        if t == 9:
            return None
        k = int(t > 9)
        return UniformCarryCell(t, k, k)


@dataclass(frozen=True, slots=True)
class AlternatingMooreCertificate:
    entry_states: int
    quiet_future_states: int
    cycle_lengths: tuple[int, ...]
    admissible_growth_exits: int
    guarded_eq_growth_exits: int
    digest: str


def alternating_moore_certificate() -> AlternatingMooreCertificate:
    """Complete quotient of the unconditional QUIET transition for period 2.

    Its 324 input pairs produce exactly 100 distinct even-pair future states;
    every one is different under the full two-phase output. EQ=9 is never
    created by a quiet transition. Growth exits need the first-growth guard.
    """
    A = tuple(s for s in range(19) if s != 9)
    states = tuple(AlternatingCore(a, b) for a in A for b in A)
    images = tuple(sorted({s.quiet_step() for s in states}))
    if len(states) != 324 or len(images) != 100:
        raise AssertionError("period-two quiet Moore universe changed")
    assert all(s.even_position % 2 == 0 and s.odd_position % 2 == 0 for s in images)
    image_set = set(images)
    if any(s.quiet_step() not in image_set for s in images):
        raise AssertionError("period-two quiet quotient not successor-closed")
    cycle_lengths: set[int] = set()
    exits = eq = 0
    for s in images:
        seen: dict[AlternatingCore, int] = {}
        t = s
        while t not in seen:
            seen[t] = len(seen)
            t = t.quiet_step()
        cycle_lengths.add(len(seen) - seen[t])
        if s.growth_step() is None:
            eq += 1
        else:
            exits += 1
    if cycle_lengths != {1, 2, 6, 10, 30} or (exits, eq) != (90, 10):
        raise AssertionError("period-two pump and growth-port counts changed")
    h = sha256()
    for s in states:
        t = s.quiet_step()
        growth = s.growth_step()
        h.update(
            bytes(
                (
                    s.even_position,
                    s.odd_position,
                    t.even_position,
                    t.odd_position,
                    255 if growth is None else growth.coefficient,
                )
            )
        )
    return AlternatingMooreCertificate(
        len(states), len(images), tuple(sorted(cycle_lengths)), exits, eq, h.hexdigest()
    )


@dataclass(frozen=True, slots=True)
class AlternatingBulkPower:
    """Temporal first-growth rank/select action for a period-two interior.

    The first growth event is a conditional EXTERNAL port. The engine never
    claims to discover it from the interior. Quiet runs pump with periods
    dividing 30; the first growth collapses the period-two core to a uniform
    phase except for ten EQ=9 exits, which refuse without a border witness.
    After an admitted non-EQ exit, all later growth bits are irrelevant to
    the protected homogeneous core.
    """

    source: AlternatingCore
    preperiod: tuple[AlternatingCore, ...]
    period: tuple[AlternatingCore, ...]

    @classmethod
    def compile(cls, source: AlternatingCore) -> AlternatingBulkPower:
        alternating_moore_certificate()
        seen: dict[AlternatingCore, int] = {}
        path: list[AlternatingCore] = []
        state = source
        while state not in seen:
            seen[state] = len(path)
            path.append(state)
            state = state.quiet_step()
        cutoff = seen[state]
        return cls(source, tuple(path[:cutoff]), tuple(path[cutoff:]))

    def temporal_action(
        self, steps: int, *, quiet_guarded: bool = False
    ) -> TemporalBankAction[AlternatingCore]:
        """Square the full synchronized alternating output, not only its clock."""
        from .temporal_bank_actions import power_alternating_outputs

        return power_alternating_outputs(
            self.source, steps, quiet_guarded=quiet_guarded
        )

    def conditional_growth_exit(
        self, quiet_steps: int, *, quiet_guarded: bool = False
    ) -> UniformCarryCell | ConditionalEQGrowthExit:
        """Preserve all four guarded EQ=9 birth branches instead of dropping them."""
        from .temporal_bank_actions import conditional_first_growth_exit

        return conditional_first_growth_exit(
            self.source, quiet_steps, quiet_guarded=quiet_guarded
        )

    def quiet_at(self, depth: int) -> AlternatingCore:
        if type(depth) is not int or depth < 0:
            raise ValueError("nonnegative quiet depth required")
        if depth < len(self.preperiod):
            return self.preperiod[depth]
        return self.period[(depth - len(self.preperiod)) % len(self.period)]

    def at(
        self, depth: int, *, first_growth: int | None = None
    ) -> AlternatingCore | UniformCarryCell:
        """One exact guarded first-growth temporal jump, no intermediate rows."""
        if type(depth) is not int or depth < 0:
            raise ValueError("nonnegative future depth required")
        if first_growth is None or first_growth >= depth:
            return self.quiet_at(depth)
        if type(first_growth) is not int or first_growth < 0:
            raise ValueError("first-growth port must be a nonnegative index")
        source = self.quiet_at(first_growth)
        collapsed = source.growth_step()
        if collapsed is None:
            raise ValueError(
                "growth births EQ=9; future border-carry certificate required"
            )
        return UniformBulkPower.compile(collapsed).at(depth - first_growth - 1)


__all__.extend(
    [
        "AlternatingBulkPower",
        "AlternatingCore",
        "AlternatingMooreCertificate",
        "alternating_moore_certificate",
    ]
)
