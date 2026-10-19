"""Controlled, exactly squared mixed-period LT/EQ/GT interior bank.

The physical source assumption is a protected *spatially periodic* symmetric
pair-sum interior.  At least one symbol per period must differ from nine, so
both reflected cumulative carry ingresses are fixed by the nearest reset.
The border owner must independently authenticate the supplied growth-control
word and the protected spatial halo.  This is NOT an unrestricted complete
integer or global all-source temporal Moore quotient.

The finite cyclic core derives both reflected carry inputs from the complete
LT/EQ/GT period; it never receives independent carry/borrow tapes.  Its
spatial period is preserved by either growth or nongrowth interior stencil.
For a certified repeating growth-control macro, its temporal *state map and
complete output program* are binary-squared, then evaluated without visiting
the intervening generations.
"""

from __future__ import annotations

from collections.abc import Callable, Generator, Iterable
from contextlib import contextmanager
from dataclasses import dataclass
from types import MappingProxyType
from typing import TYPE_CHECKING, NamedTuple

from number_compiler.arithmetic.automata.temporal_slp import concatenate_temporal_slp
from number_compiler.arithmetic.fields.decimal_pair_partition import (
    decimal_pair_word_projection,
)

if TYPE_CHECKING:
    from number_compiler.resources.ledger import ResourceLedger


class IncompleteMixedBorder(ValueError):
    """The available reset/width/halo guard cannot certify this power."""


def _bit(s: int, ingress: int) -> int:
    return int(s > 9 or (s == 9 and ingress == 1))


def _digit(s: int, ingress: int) -> int:
    return s + ingress - 10 * _bit(s, ingress)


@dataclass(frozen=True, slots=True)
class MixedPeriodicCore:
    """One ordered period of the complete pair/F5 grammar, not an occurrence."""

    coefficients: tuple[int, ...]

    def __post_init__(self) -> None:
        if not self.coefficients or any(
            type(s) is not int or not 0 <= s <= 18 for s in self.coefficients
        ):
            raise ValueError("expected a nonempty exact decimal pair-sum period")
        if all(s == 9 for s in self.coefficients):
            raise IncompleteMixedBorder(
                "an all-EQ periodic cylinder has no decisive carry reset"
            )

    @property
    def period(self) -> int:
        return len(self.coefficients)

    def ingresses(self) -> tuple[tuple[int, int], ...]:
        """Exact two-ended carries in O(period), without materialized tapes.

        A non-EQ reset fixes each directional carry regardless of its more
        distant input.  Find the last and first reset once, then sweep the
        period in opposing directions.  The right sweep is a view of the
        original physical forward carry, **not** a reversed arithmetic scan.
        """
        s = self.coefficients
        p = len(s)
        first = next(i for i, value in enumerate(s) if value != 9)
        last = next(i for i in range(p - 1, -1, -1) if s[i] != 9)
        left = [0] * p
        right = [0] * p
        carry = int(s[last] > 9)
        for i, value in enumerate(s):
            left[i] = carry
            if value != 9:
                carry = int(value > 9)
        carry = int(s[first] > 9)
        for i in range(p - 1, -1, -1):
            right[i] = carry
            if s[i] != 9:
                carry = int(s[i] > 9)
        return tuple(zip(left, right, strict=True))

    @staticmethod
    def _require_growth_bit(growth: int) -> None:
        if type(growth) is not int or growth not in (0, 1):
            raise ValueError("growth must be a certified Boolean port")

    def conditional_eq_exit(self, growth: int) -> MixedEQExit:
        """Return the exact all-EQ output and a punctured future borrow port.

        Unlike ``advance``, this does not incorrectly reject an EQ birth as
        an unknown *current* output.  The two next-generation exterior carry
        bits stay explicit inputs to ``EQCylinderBank``; no continuation is
        manufactured without an authenticated border action.
        """
        self._require_growth_bit(growth)
        s = self.coefficients
        p = len(s)
        ports = self.ingresses()
        low = tuple(_digit(s[i], ports[i][0]) for i in range(p))
        high = tuple(
            _digit(s[(i - 1) % p], _bit(s[i], ports[i][1]))
            if growth
            else _digit(s[i], ports[i][1])
            for i in range(p)
        )
        if any(low[i] + high[i] != 9 for i in range(p)):
            raise IncompleteMixedBorder(
                "this transition does not enter an all-EQ period"
            )
        return MixedEQExit(
            growth, low, high, ports, tuple((int(d == 0), int(d == 9)) for d in low)
        )

    def advance(self, growth: int) -> tuple[MixedPeriodicCore, MixedFrame]:
        """Exact internal radius-one pair stencil, including EQ-wire births.

        New 1-digit growth/center seams are **not** falsely inserted inside
        this protected core: the caller's border action owns those seams.
        """
        self._require_growth_bit(growth)
        s = self.coefficients
        p = len(s)
        ports = self.ingresses()
        next_values: list[int] = []
        low_digits: list[int] = []
        reflected_digits: list[int] = []
        for i, (left, right) in enumerate(ports):
            low = _digit(s[i], left)
            if growth:
                # Source c[w-i] = K_(s[i])(c[w-1-i]); new width shifts
                # the opposite digit to source pair position i-1.
                high = _digit(s[(i - 1) % p], _bit(s[i], right))
            else:
                high = _digit(s[i], right)
            t = low + high
            if not 0 <= t <= 18:
                raise AssertionError("mixed pair stencil left decimal alphabet")
            next_values.append(t)
            low_digits.append(low)
            reflected_digits.append(high)
        target = MixedPeriodicCore(tuple(next_values))
        future_ports = target.ingresses()
        # These guards are for the subsequent *nongrowth* innovation borrow
        # comparison only. A growth comparison uses the shifted-width rule.
        borrow_if_next_quiet = tuple(
            int(
                _bit(target.coefficients[i], right) == right
                and low_digits[i] == 9 * right
            )
            for i, (_left, right) in enumerate(future_ports)
        )
        return target, MixedFrame(
            target=target.coefficients,
            growth=growth,
            incoming=ports,
            digits_low=tuple(low_digits),
            digits_reflected=tuple(reflected_digits),
            borrow_identity_if_next_quiet=borrow_if_next_quiet,
        )


@dataclass(frozen=True, slots=True)
class MixedEQExit:
    """Exact periodic EQ birth, with **future** borrow right-ingress punctured.

    ``borrow_by_right_port[i][r]`` equals the following nongrowth innovation
    identity gate when the next reflected exterior carry is ``r``.  An
    authenticated two-ended future border program can feed ``EQCylinderBank``
    without rebuilding the emitted EQ row.
    """

    growth: int
    digits_low: tuple[int, ...]
    digits_reflected: tuple[int, ...]
    incoming: tuple[tuple[int, int], ...]
    borrow_by_right_port: tuple[tuple[int, int], ...]

    @property
    def target(self) -> tuple[int, ...]:
        return (9,) * len(self.digits_low)


class MixedFrame(NamedTuple):
    """One complete periodic core port frame; borrow guard is conditional."""

    target: tuple[int, ...]
    growth: int
    incoming: tuple[tuple[int, int], ...]
    digits_low: tuple[int, ...]
    digits_reflected: tuple[int, ...]
    borrow_identity_if_next_quiet: tuple[int, ...]

    def masks(self) -> dict[str, tuple[int, ...]]:
        return decimal_pair_word_projection(self.target).wire_channels()


class _TemporalNode(NamedTuple):
    tag: str
    steps: int
    frame: MixedFrame | None = None
    left: int = 0
    right: int = 0
    copies: int = 1


class MixedOutputArena:
    """Hash-consed, exact synchronized temporal output SLP."""

    def __init__(self) -> None:
        self.nodes: list[_TemporalNode] = [_TemporalNode("empty", 0)]
        self.ids: dict[tuple[object, ...], int] = {}
        self._frozen = False

    def __setattr__(self, name: str, value: object) -> None:
        if getattr(self, "_frozen", False):
            raise AttributeError("published mixed output arena is immutable")
        object.__setattr__(self, name, value)

    def freeze(self) -> None:
        """Seal a completed action's output program before publication."""
        if self._frozen:
            return
        object.__setattr__(self, "nodes", tuple(self.nodes))
        object.__setattr__(self, "ids", MappingProxyType(dict(self.ids)))
        object.__setattr__(self, "_frozen", True)

    def _check_mutable(self) -> None:
        if self._frozen or type(self.nodes) is not list or type(self.ids) is not dict:
            raise RuntimeError("published mixed output arena cannot be extended")

    def _intern(self, key: tuple[object, ...], node: _TemporalNode) -> int:
        self._check_mutable()
        found = self.ids.get(key)
        if found is not None:
            return found
        idx = len(self.nodes)
        self.nodes.append(node)
        self.ids[key] = idx
        return idx

    def emit(self, frame: MixedFrame) -> int:
        return self._intern(("emit", frame), _TemporalNode("emit", 1, frame))

    def concat(self, a: int, b: int) -> int:
        return concatenate_temporal_slp(
            a,
            b,
            nodes=self.nodes,
            repeat=self.repeat,
            copies=lambda node: node.copies,
            intern=self._intern,
            make_concat=lambda left, right, x, y: _TemporalNode(
                "concat", x.steps + y.steps, left=left, right=right
            ),
        )

    def repeat(self, a: int, times: int) -> int:
        if times <= 0 or a == 0:
            return 0
        if times == 1:
            return a
        x = self.nodes[a]
        copies = times
        while x.tag == "repeat":
            copies *= x.copies
            a = x.left
            x = self.nodes[a]
        return self._intern(
            ("repeat", a, copies),
            _TemporalNode("repeat", x.steps * copies, left=a, copies=copies),
        )

    def at(self, root: int, tick: int) -> MixedFrame:
        if type(tick) is not int or not 0 <= tick < self.nodes[root].steps:
            raise IndexError(tick)
        while True:
            node = self.nodes[root]
            if node.tag == "emit":
                if node.frame is None:
                    raise AssertionError("missing frame")
                return node.frame
            if node.tag == "concat":
                n = self.nodes[node.left].steps
                if tick < n:
                    root = node.left
                else:
                    tick -= n
                    root = node.right
            elif node.tag == "repeat":
                root = node.left
                tick %= self.nodes[root].steps
            else:
                raise AssertionError("invalid temporal output node")


@dataclass(frozen=True, slots=True)
class MixedTemporalAction:
    """Exact conditional action with authenticated time length and local exit."""

    source: MixedPeriodicCore
    target: MixedPeriodicCore
    steps: int
    growth_pattern: tuple[int, ...]
    output_root: int
    arena: MixedOutputArena
    orbit_states: int
    moore_states: int

    def at(self, tick: int) -> MixedFrame:
        return self.arena.at(self.output_root, tick)

    @property
    def program_nodes(self) -> int:
        return len(self.arena.nodes)

    @property
    def proof_scope(self) -> str:
        return "CONDITIONAL_PERIODIC_MIXED_INTERIOR;NO_COMPLETE_ROOT_AUTHORITY"


@contextmanager
def _controlled_bank_workspace(
    ledger: ResourceLedger, owner: int
) -> Generator[Callable[[int, int], None], None, None]:
    """Track incremental construction capacity until output publication."""
    reserved_entries = 0
    reserved_nodes = 0
    active = True

    def reserve(entries: int, nodes: int) -> None:
        nonlocal reserved_entries, reserved_nodes
        if not active:
            raise RuntimeError("controlled-bank workspace is closed")
        if type(entries) is not int or type(nodes) is not int:
            raise TypeError("workspace reservations must be exact integers")
        if entries < 0 or nodes < 0:
            raise ValueError("workspace reservations must be nonnegative")
        ledger.reserve(owner, entries=entries, nodes=nodes)
        reserved_entries += entries
        reserved_nodes += nodes

    try:
        yield reserve
    finally:
        active = False
        if reserved_entries or reserved_nodes:
            ledger.release(owner, entries=reserved_entries, nodes=reserved_nodes)


class ControlledMixedBank:
    """Binary-squared functional future bank under a *certified* control word.

    The caller must authenticate that the supplied growth pattern repeats on
    the actual whole-integer source, plus the spatial protected-halo guard.
    This class cannot silently infer an unrestricted future growth itinerary.
    """

    def __init__(
        self,
        source: MixedPeriodicCore,
        growth_pattern: Iterable[int],
        *,
        max_states: int = 10000,
        workspace_reserve: Callable[[int, int], None] | None = None,
    ) -> None:
        self.source = source
        self.pattern = tuple(growth_pattern)
        if (
            not self.pattern
            or len(self.pattern) > 128
            or any(type(b) is not int or b not in (0, 1) for b in self.pattern)
        ):
            raise ValueError("nonempty finite Boolean growth control required")
        if not 1 <= max_states <= 10_000_000:
            raise ValueError("invalid finite bank discovery budget")
        if workspace_reserve is not None and not callable(workspace_reserve):
            raise TypeError("workspace reservation callback must be callable")
        self._workspace_reserve = workspace_reserve
        from .bank_width_clock import WidthMacro

        if not WidthMacro.from_bits(self.pattern).repeat(3).admitted():
            raise IncompleteMixedBorder("growth control violates universal width clock")
        # Charge the arena sentinel and initial owner structures before
        # allocating them. Each orbit insertion below reserves enough for
        # its state/index/output row; Moore refinement receives a separate
        # reservation before constructing its signatures and partitions.
        self._reserve(entries=4, nodes=1)
        self.arena = MixedOutputArena()
        self.states: list[MixedPeriodicCore] = []
        self.ids: dict[MixedPeriodicCore, int] = {}
        self.one: list[tuple[int, int]] = []
        next_states: list[MixedPeriodicCore] = []
        s = source
        while s not in self.ids:
            if len(self.states) >= max_states:
                raise IncompleteMixedBorder("mixed-bank orbit exceeds state budget")
            period = len(self.pattern)
            self._reserve(
                entries=7 + 3 * period,
                nodes=2 * period + 1,
            )
            current = s
            self.ids[current] = len(self.states)
            self.states.append(current)
            root = 0
            for bit in self.pattern:
                s, frame = s.advance(bit)
                root = self.arena.concat(root, self.arena.emit(frame))
            self.one.append((-1, root))
            next_states.append(s)
        for i, target in enumerate(next_states):
            self.one[i] = (self.ids[target], self.one[i][1])
        self._reserve(
            entries=len(self.states) * (2 * len(self.pattern) + 8),
            nodes=0,
        )
        self.classes = self._moore_minimize()
        self.moore_state_count = len(set(self.classes))
        reps: dict[int, int] = {}
        for i, c in enumerate(self.classes):
            reps.setdefault(c, i)
        # Moore IDs own only the complete FUTURE output action. The distinct
        # raw finite state is retained as a transient exact endpoint witness;
        # equal future actions do not assert equal current pair coefficients.
        self.representatives = tuple(reps[i] for i in range(len(reps)))
        self.raw_jumps = [tuple(nxt for nxt, _ in self.one)]
        self.semantic_layers = [
            tuple(
                (self.classes[self.one[raw][0]], self.one[raw][1])
                for raw in self.representatives
            )
        ]

    def _reserve(self, *, entries: int, nodes: int) -> None:
        """Reserve temporary capacity before growing constructor-owned arrays."""
        if entries < 0 or nodes < 0:
            raise ValueError("bank reservation quantities must be nonnegative")
        if self._workspace_reserve is None:
            return
        self._workspace_reserve(entries, nodes)

    def _moore_minimize(self) -> tuple[int, ...]:
        """Refine complete period outputs and all successor continuations."""

        def partition(values: tuple[object, ...]) -> tuple[int, ...]:
            ids: dict[object, int] = {}
            colors: list[int] = []
            for value in values:
                color = ids.get(value)
                if color is None:
                    color = len(ids)
                    ids[value] = color
                colors.append(color)
            return tuple(colors)

        # Full emitted coefficient/F5/output behavior is the specified
        # observer; equality here is exact, not modulo a sampled ray.
        def observable(frame: MixedFrame) -> tuple[object, ...]:
            # Input coefficients and internal carry ingress are NOT emitted
            # Moore coordinates. Future pair/F5 masks, oriented digits, growth
            # and guarded innovation identity bits are the exact observables.
            # The future carry response is derivable from the target period.
            return (
                frame.growth,
                frame.target,
                frame.digits_low,
                frame.digits_reflected,
                frame.borrow_identity_if_next_quiet,
            )

        signatures = tuple(
            tuple(observable(self.arena.at(root, i)) for i in range(len(self.pattern)))
            for _next, root in self.one
        )
        colors = partition(signatures)
        while True:
            new = partition(
                tuple(
                    (signatures[i], colors[self.one[i][0]])
                    for i in range(len(self.states))
                )
            )
            if new == colors:
                return colors
            colors = new

    def _ensure(self, binary_depth: int) -> None:
        while len(self.semantic_layers) <= binary_depth:
            old_raw = self.raw_jumps[-1]
            self.raw_jumps.append(
                tuple(old_raw[old_raw[i]] for i in range(len(self.states)))
            )
            old = self.semantic_layers[-1]
            self.semantic_layers.append(
                tuple(
                    (old[old[i][0]][0], self.arena.concat(old[i][1], old[old[i][0]][1]))
                    for i in range(self.moore_state_count)
                )
            )

    def power(self, steps: int) -> MixedTemporalAction:
        if type(steps) is not int or steps < 0:
            raise ValueError("nonnegative exact depth required")
        from .bank_width_clock import WidthMacro

        period = len(self.pattern)
        blocks, rem = divmod(steps, period)
        # The width clock is a proof of structural admissibility, not a
        # source-derived growth-word generator.
        width_action = WidthMacro.from_bits(self.pattern).repeat(blocks)
        for g in self.pattern[:rem]:
            width_action = width_action.then(WidthMacro.event(g))
        if not width_action.admitted():
            raise IncompleteMixedBorder("temporal growth word violates width theorem")
        binary_depth = max(0, blocks.bit_length() - 1)
        # Squaring retains one raw jump and one output transition per Moore
        # state and binary level. Reserve before growing the layer arrays or
        # adding their SLP nodes; the constructor reservation stays live too.
        self._reserve(
            entries=binary_depth * (len(self.states) + self.moore_state_count),
            nodes=binary_depth * self.moore_state_count + 2 * len(self.pattern) + 4,
        )
        self._ensure(binary_depth)
        q = self.ids[self.source]
        root = 0
        i = 0
        while blocks:
            if blocks & 1:
                next_class, emitted = self.semantic_layers[i][self.classes[q]]
                root = self.arena.concat(root, emitted)
                q = self.raw_jumps[i][q]
                if self.classes[q] != next_class:
                    raise AssertionError(
                        "Moore future quotient was not successor-closed"
                    )
            blocks >>= 1
            i += 1
        current = self.states[q]
        for bit in self.pattern[:rem]:
            current, frame = current.advance(bit)
            root = self.arena.concat(root, self.arena.emit(frame))
        if self.arena.nodes[root].steps != steps:
            raise AssertionError("binary mixed-bank square lost an output tick")
        self.arena.freeze()
        return MixedTemporalAction(
            self.source,
            current,
            steps,
            self.pattern,
            root,
            self.arena,
            len(self.states),
            self.moore_state_count,
        )


def required_protected_halo(period: int, depth: int) -> int:
    """Conservative pair-cell distance excluding influence of exterior resets.

    In one step a non-EQ reset is found at distance at most period, and the
    growth stencil uses one adjacent pair. Induction thus bounds an outside
    boundary's influence on queried cells by (period+1) per tick.
    """
    if type(period) is not int or period < 1 or type(depth) is not int or depth < 0:
        raise ValueError("invalid period or temporal depth")
    return (period + 2) * (depth + 1)


__all__ = [
    "ControlledMixedBank",
    "IncompleteMixedBorder",
    "MixedEQExit",
    "MixedFrame",
    "MixedOutputArena",
    "MixedPeriodicCore",
    "MixedTemporalAction",
    "required_protected_halo",
]


def main(argv: list[str] | None = None) -> int:
    """Query an exact *conditional* mixed periodic-bank temporal square.

    This explicitly cannot publish a complete reverse-add integer. Both a
    source-owned spatial protection proof and a future border-growth proof
    remain separate obligations; a supplied repeating word is not that proof.
    """
    import argparse
    import json

    parser = argparse.ArgumentParser(prog="number-compiler-mixed-bank-power")
    parser.add_argument(
        "--period",
        required=True,
        help="Comma-separated decimal symmetric pair sums, e.g. 0,0,1",
    )
    parser.add_argument(
        "--growth-control",
        required=True,
        help="Repeating conditional border growth bits, e.g. 01",
    )
    parser.add_argument("--steps", type=int, required=True)
    parser.add_argument("--at", type=int)
    parser.add_argument("--max-states", type=int, default=10000)
    parser.add_argument(
        "--conditional",
        action="store_true",
        required=True,
        help="Acknowledge that border admission is not a whole-root proof",
    )
    args = parser.parse_args(argv)
    try:
        period = tuple(int(x) for x in args.period.split(","))
        growth = tuple(int(x) for x in args.growth_control)
        bank = ControlledMixedBank(
            MixedPeriodicCore(period), growth, max_states=args.max_states
        )
        action = bank.power(args.steps)
        location = args.at if args.at is not None else (args.steps - 1)
        result: dict[str, object] = {
            "proof_scope": action.proof_scope,
            "source_period": list(period),
            "growth_control": "".join(map(str, growth)),
            "steps": action.steps,
            "conditional_endpoint_period": list(action.target.coefficients),
            "reachable_states": action.orbit_states,
            "moore_future_states": action.moore_states,
            "compressed_output_nodes": action.program_nodes,
            "required_spatial_halo_pairs": required_protected_halo(
                len(period), args.steps
            ),
            "complete_integer_certified": False,
        }
        if args.steps:
            frame = action.at(location)
            result["queried_tick"] = location
            result["queried_frame"] = {
                "growth": frame.growth,
                "pair_coefficients": list(frame.target),
                "mask_bits": {k: list(v) for k, v in frame.masks().items()},
                "oriented_low_digits": list(frame.digits_low),
                "oriented_reflected_digits": list(frame.digits_reflected),
                "borrow_identity_if_next_nongrowth": list(
                    frame.borrow_identity_if_next_quiet
                ),
            }
    except (ValueError, IndexError) as exc:
        parser.error(str(exc))
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
