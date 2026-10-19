"""Source-bound finite Mahler safety, not an all-time decision procedure.

A block represents every x = residue + 2**width*k + t (k natural) admitted by
one exact half-open fractional guard. Chronological composition solves the
source congruence before pulling back the next guard. No w-tree menu is input.
The worklist is a bounded research constructor, not a new production scheduler.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from operator import add, mul
from typing import Literal

from devtools.experiments.antihydra.mahler_predicate import (
    MahlerPredicateState,
    mahler_bit_action,
    mahler_odd_event_action,
)
from number_compiler.arithmetic.automata.program_word import (
    RunTraversalMetrics,
    SourceWord,
    iter_runs,
    source_word_symbol_bounds,
)
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.arithmetic.fields.branch_quotients import (
    PRIME_BANK,
    prime_lane_after,
)
from number_compiler.arithmetic.fields.consumer_pullback import (
    ExactRational as Q,
)
from number_compiler.arithmetic.fields.consumer_pullback import (
    GuardedAffineAction,
    SaturatingAffineAction,
)
from number_compiler.arithmetic.fields.consumer_pullback import (
    HalfOpenInterval as Interval,
)
from number_compiler.arithmetic.fields.morphism_core import binary_power
from number_compiler.arithmetic.fields.root_semifield import RootSemifieldElement
from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict, LedgerList
from number_compiler.sequences.antihydra.blocks import arithmetic_kernel
from number_compiler.sequences.collatz.root_germs import (
    RationalPadicRootGerm,
    RationalPadicRootMismatch,
)

__all__ = ("PRIME_BANK",)

ZERO, HALF = Q(0), Q(1, 2)


@dataclass(frozen=True, slots=True)
class SourceBlock:
    width: int
    residue: int
    endpoint: int
    guard: Interval
    ledger_delta: int
    ledger_minimum: int
    predicate_action: SaturatingAffineAction = field(
        default_factory=SaturatingAffineAction.identity
    )

    def __post_init__(self) -> None:
        if type(self.predicate_action) is not SaturatingAffineAction:
            raise TypeError("source block predicate action must be exact")

    @property
    def predicate_state(self) -> MahlerPredicateState:
        """Semantic future-predicate residual, separate from source geometry."""
        return MahlerPredicateState.initial().advance_action(self.predicate_action)

    @property
    def skew(self) -> SkewTransfer[int]:
        """Complete centered integer transport on ``D=h-1``.

        This is the same upper-triangular transfer used by the production
        Antihydra cylinder, expressed in the centered Mahler chart.  The
        fractional ceiling residual is a contravariant projection of this
        transfer, rather than a separately composed action.
        """
        p2, p3 = 1 << self.width, 3**self.width
        return SkewTransfer(p3, p2 * self.endpoint - p3 * self.residue, p2)

    @property
    def fractional(self) -> SaturatingAffineAction:
        """Transport the ceiling residual through the centered skew."""
        transfer = self.skew
        return SaturatingAffineAction(
            Q(transfer.upper, transfer.lower),
            Q(-transfer.offset, transfer.lower),
        )

    @property
    def root_shell(self) -> GuardedAffineAction:
        """The same source guard in theta=2t=r^2 coordinates, without a new scan."""
        fractional = self.fractional
        return GuardedAffineAction(
            SaturatingAffineAction(fractional.scale, Q(2) * fractional.offset),
            Interval(Q(2) * self.guard.lower, Q(2) * self.guard.upper),
        )


@dataclass(frozen=True, slots=True)
class SignedTailBoundary:
    """Current-tail sign enclosure; never a source or all-shifts certificate.

    The infinite signed tail is in [(numerator-dyadic)/ternary,
    (numerator+dyadic)/ternary]. Equality at the positive threshold is
    deliberately unresolved, even though nonempty binary words exclude it.
    """

    numerator: int
    dyadic: int
    ternary: int

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (self.numerator, self.dyadic, self.ternary)
        ):
            raise TypeError("signed-tail coordinates require exact integers")
        if self.dyadic <= 0 or self.ternary <= 0:
            raise ValueError("signed-tail scales must be positive")

    @property
    def classification(self) -> Literal["positive", "nonpositive", "boundary"]:
        if self.numerator > self.dyadic:
            return "positive"
        if self.numerator <= -self.dyadic:
            return "nonpositive"
        return "boundary"

    @property
    def cone(self) -> tuple[int, int]:
        return self.numerator + self.dyadic, self.dyadic - self.numerator

    @property
    def interval(self) -> tuple[Q, Q]:
        return (
            Q(self.numerator - self.dyadic, self.ternary),
            Q(self.numerator + self.dyadic, self.ternary),
        )


@dataclass(frozen=True, slots=True)
class SourceBlockID(ArenaHandle):
    """A finite source certificate in one research workspace."""


@dataclass(frozen=True, slots=True)
class OddZeroObserver:
    """Odd-then-zeros observation, not live source-safety event authority.

    ``source`` and ``residual`` retain authenticated radix-four occurrence
    authority. They are not coordinates of the reusable predicate action.
    This differs from ``SourceEvent``'s zero-then-one physical convention.
    """

    source: SourceWord
    exponent: int
    mismatch: RationalPadicRootMismatch
    residual: SourceWord
    predicate_action: SaturatingAffineAction


class SourceSafetyWorkspace:
    """Memoized source construction with explicit limits and ledger retention."""

    def __init__(self, ledger: ResourceLedger, *, max_width: int = 256) -> None:
        if type(max_width) is not int or max_width < 1:
            raise ValueError("max_width must be a positive integer")
        self.ledger = ledger
        self.max_width = max_width
        self.owner = ArenaToken("mahler-original-fractional-safety-v1")
        name = f"mahler-safety-{ledger.owner_count}"
        self._nodes_owner = ledger.register(name + "-nodes", "finite proof blocks")
        self._keys_owner = ledger.register(name + "-keys", "source congruences")
        self._nodes: LedgerList[SourceBlock] = ledger.make_list(self._nodes_owner)
        self._keys: LedgerDict[tuple[int, int], SourceBlockID] = ledger.make_dict(
            self._keys_owner
        )
        self._closed = False

    def _require_open(self) -> None:
        if self._closed:
            raise ValueError("closed Mahler source-safety workspace")

    def odd_zero_observer(self, source: SourceWord) -> OddZeroObserver:
        """Observe an odd-then-zeros action through the shared first-hole cursor.

        The root ``-1/3`` selects ``v2(3D+1)`` on the exact finite source.
        Prefix runs are accelerated by that existing root owner; the untouched
        suffix is a source-aligned cursor, never a reconstructed integer/tile.
        Live ``source_event`` instead selects ``v2(D)+1`` and zero-then-one
        parity. This observer cannot replace that event's intermediate guards.
        No claim about arbitrary temporal-cylinder construction follows here.
        """
        self._require_open()
        traversal = RunTraversalMetrics()
        try:
            bounds = source_word_symbol_bounds(source, metrics=traversal)
            if bounds is None or not 0 <= bounds[0] <= bounds[1] < 4:
                raise ValueError(
                    "odd-event source requires nonempty radix-four symbols"
                )
            low, _count = next(iter_runs(source, metrics=traversal))
            if not low & 1:
                raise ValueError("odd-event source must be positive and odd")
            self.ledger.bump("mahler_odd_zero_observer_first_hole_demands")
            mismatch, residual = RationalPadicRootGerm(1, 1).first_mismatch_word(
                source, metrics=traversal
            )
            exponent = mismatch.valuation_bits
            self.ledger.bump("mahler_odd_zero_observer_symbols_represented", exponent)
            if exponent > self.max_width:
                self.ledger.bump("safety_refusals")
                raise BlockContextBudgetExceeded(
                    "Mahler odd-event width budget exceeded"
                )
            action = mahler_odd_event_action(exponent)
            self.ledger.bump(
                "mahler_odd_zero_observer_operand_bits",
                sum(
                    abs(value.numerator).bit_length() + value.denominator.bit_length()
                    for value in (action.scale, action.offset, action.cap)
                    if value is not None
                ),
            )
            return OddZeroObserver(source, exponent, mismatch, residual, action)
        finally:
            # Instrument the demanded path itself, including failed/early-exit
            # work. No post-query metrics traversal reads the untouched suffix.
            self.ledger.bump(
                "mahler_odd_zero_observer_source_nodes_visited", traversal.visited_nodes
            )
            self.ledger.counters["mahler_odd_zero_observer_source_frontier_peak"] = max(
                self.ledger.counters.get(
                    "mahler_odd_zero_observer_source_frontier_peak", 0
                ),
                traversal.peak_frontier,
            )

    def view(self, handle: SourceBlockID) -> SourceBlock:
        self._require_open()
        if type(handle) is not SourceBlockID:
            raise TypeError("source block handle required")
        handle.validate(self.owner, "source-safety", size=len(self._nodes))
        return self._nodes[handle.local_id]

    def antihydra_chart(
        self, handle: SourceBlockID, centered_high_fiber: int
    ) -> tuple[int, int]:
        """Translate authenticated ``D`` coordinates to production ``h=D+1``.

        The returned pair is the canonical production residue and high fiber.
        In particular, the all-ones centered residue carries one into the high
        fiber.  This is a coordinate change only; it does not transfer Mahler
        fractional safety to the guarded physical Antihydra machine.
        """
        block = self.view(handle)
        if type(centered_high_fiber) is not int or centered_high_fiber < 0:
            raise ValueError("a natural centered high fiber is required")
        modulus = 1 << block.width
        shifted = block.residue + 1
        self.ledger.bump("safety_centered_chart_views")
        return shifted % modulus, centered_high_fiber + shifted // modulus

    def _publish(self, block: SourceBlock) -> SourceBlockID:
        key = (block.width, block.residue)
        if key in self._keys:
            result = self._keys[key]
            if self.view(result) != block:
                raise ArithmeticError(
                    "parenthesizations disagree on a complete source block"
                )
            self.ledger.bump("safety_memo_hits")
            return result
        self.ledger.reserve_many(((self._nodes_owner, 1, 1), (self._keys_owner, 1, 0)))
        result = SourceBlockID(self.owner, "source-safety", len(self._nodes))
        self._nodes.append(block)
        self._keys[key] = result
        self.ledger.bump("safety_blocks_constructed")
        integers = (
            block.residue,
            block.endpoint,
            block.width,
            block.guard.lower.numerator,
            block.guard.lower.denominator,
            block.guard.upper.numerator,
            block.guard.upper.denominator,
            block.ledger_delta,
            block.ledger_minimum,
            block.predicate_action.scale.numerator,
            block.predicate_action.scale.denominator,
            block.predicate_action.offset.numerator,
            block.predicate_action.offset.denominator,
            0
            if block.predicate_action.cap is None
            else block.predicate_action.cap.numerator,
            1
            if block.predicate_action.cap is None
            else block.predicate_action.cap.denominator,
        )
        self.ledger.bump(
            "safety_retained_integer_bits", sum(abs(v).bit_length() for v in integers)
        )
        return result

    def _leaf(self, residue: int) -> SourceBlockID:
        # Reuse the production a=D+1 return kernel, including its ledger law.
        h = residue + 1
        core = arithmetic_kernel(h % 2, 1)
        endpoint = core.output + 3 * (h // 2) - 1
        centered = SourceBlock(
            1,
            residue,
            endpoint,
            Interval(),
            core.delta,
            core.minimum,
            mahler_bit_action(residue),
        )
        action = centered.fractional
        guard = Interval().intersect(Interval().pullback(action))
        return self._publish(
            SourceBlock(
                1,
                residue,
                endpoint,
                guard,
                core.delta,
                core.minimum,
                mahler_bit_action(residue),
            )
        )

    def compose(
        self, first_id: SourceBlockID, second_id: SourceBlockID
    ) -> SourceBlockID:
        first, second = self.view(first_id), self.view(second_id)
        width = first.width + second.width
        if width > self.max_width:
            self.ledger.bump("safety_refusals")
            raise BlockContextBudgetExceeded("Mahler safety width budget exceeded")
        self.ledger.bump("safety_composition_attempts")
        first_skew, second_skew = first.skew, second.skew
        first_fractional, second_fractional = first.fractional, second.fractional
        modulus, gain = second_skew.lower, first_skew.upper
        inverse = pow(gain, -1, modulus)
        if not 0 <= inverse < modulus or gain * inverse % modulus != 1 % modulus:
            raise ArithmeticError("source composition inverse failed its check")
        lift = (
            (second.residue + modulus - first.endpoint % modulus) * inverse
        ) % modulus
        residue = first.residue + (lift << first.width)
        high = (first.endpoint + gain * lift - second.residue) // modulus
        if high < 0 or first.endpoint + gain * lift != second.residue + modulus * high:
            raise ArithmeticError("source congruence certificate failed")
        transfer = first_skew.then(second_skew, multiply=mul, add=add)
        endpoint, remainder = divmod(
            transfer.upper * residue + transfer.offset, transfer.lower
        )
        if remainder:
            raise ArithmeticError("composed centered skew is not integral")
        route_endpoint = second.endpoint + second_skew.upper * high
        if endpoint != route_endpoint:
            raise ArithmeticError("source route and centered skew disagree")
        action = SaturatingAffineAction(
            Q(transfer.upper, transfer.lower),
            Q(-transfer.offset, transfer.lower),
        )
        if action != first_fractional.then(second_fractional):
            raise ArithmeticError("fractional projection escaped the centered skew")
        guard = first.guard.intersect(second.guard.pullback(first_fractional))
        predicate_action = first.predicate_action.then(second.predicate_action)
        self.ledger.bump(
            "safety_composition_operand_bits",
            gain.bit_length() + modulus.bit_length() + abs(endpoint).bit_length(),
        )
        return self._publish(
            SourceBlock(
                width,
                residue,
                endpoint,
                guard,
                first.ledger_delta + second.ledger_delta,
                min(first.ledger_minimum, first.ledger_delta + second.ledger_minimum),
                predicate_action,
            )
        )

    def cylinder(self, width: int, residue: int) -> SourceBlockID:
        self._require_open()
        if (
            type(width) is not int
            or type(residue) is not int
            or width < 0
            or residue < 0
        ):
            raise ValueError("nonnegative integer width and residue required")
        if width > self.max_width:
            self.ledger.bump("safety_refusals")
            raise BlockContextBudgetExceeded("Mahler safety width budget exceeded")
        if residue >= 1 << width:
            raise ValueError("source residue is not canonical at this precision")
        stack = [(width, residue)]
        while stack:
            n, r = stack[-1]
            self.ledger.bump("safety_worklist_visits")
            if (n, r) in self._keys:
                self.ledger.bump("safety_memo_hits")
                stack.pop()
                continue
            if n == 0:
                self._publish(SourceBlock(0, 0, 0, Interval(), 0, 0))
                stack.pop()
                continue
            if n == 1:
                self._leaf(r)
                stack.pop()
                continue
            left = n // 2
            left_key = (left, r % (1 << left))
            if left_key not in self._keys:
                stack.append(left_key)
                continue
            first_id = self._keys[left_key]
            first = self.view(first_id)
            middle = first.endpoint + 3**left * (r >> left)
            right_key = (n - left, middle % (1 << (n - left)))
            if right_key not in self._keys:
                stack.append(right_key)
                continue
            result = self.compose(first_id, self._keys[right_key])
            if self.view(result).residue != r:
                raise ArithmeticError(
                    "source congruence solver changed the requested source"
                )
            stack.pop()
        return self._keys[(width, residue)]

    def tail_boundary(self, handle: SourceBlockID) -> SignedTailBoundary:
        """Project the existing centered skew, without a parity-word replay."""
        transfer = self.view(handle).skew
        numerator = transfer.upper - transfer.lower - 2 * transfer.offset
        self.ledger.bump("safety_tail_projections")
        self.ledger.bump(
            "safety_tail_operand_bits",
            transfer.upper.bit_length()
            + transfer.lower.bit_length()
            + abs(transfer.offset).bit_length()
            + abs(numerator).bit_length(),
        )
        return SignedTailBoundary(numerator, transfer.lower, transfer.upper)

    def root_boundary(
        self, handle: SourceBlockID
    ) -> tuple[RootSemifieldElement, RootSemifieldElement]:
        """Demand and charge the partial root chart, including failed exits."""
        tail = self.tail_boundary(handle)
        a, b = tail.cone
        denominator = 2 * tail.dyadic
        self.ledger.bump("safety_root_projections")
        self.ledger.bump(
            "safety_root_operand_bits",
            abs(a).bit_length() + abs(b).bit_length() + 2 * denominator.bit_length(),
        )
        if min(a, b) < 0:
            self.ledger.bump("safety_root_projection_failures")
        return (
            RootSemifieldElement(Q(a, denominator)),
            RootSemifieldElement(Q(b, denominator)),
        )

    def refine_tail(self, handle: SourceBlockID) -> tuple[SourceBlockID, ...]:
        """Refine only an unresolved current tail, retaining every prefix guard.

        A positive terminal stops this query, not all later shifted-tail queries.
        Existing complete source guards and ledger minima remain on each child.
        """
        block = self.view(handle)
        if block.guard.empty or self.tail_boundary(handle).classification != "boundary":
            self.ledger.bump("safety_tail_terminal_queries")
            return ()
        if block.width >= self.max_width:
            self.ledger.bump("safety_refusals")
            raise BlockContextBudgetExceeded("Mahler safety width budget exceeded")
        children: list[SourceBlockID] = []
        for bit in (0, 1):
            self.ledger.bump("safety_tail_refinements")
            child = self.compose(handle, self.cylinder(1, bit))
            if not self.view(child).guard.empty:
                children.append(child)
        return tuple(children)

    def extend_run(self, handle: SourceBlockID, bit: int, count: int) -> SourceBlockID:
        """Compose a supplied homogeneous run through the shared binary owner.

        This preserves source admission and all guards. It does not discover a
        source's next run or assert that the resulting guard is nonempty.
        """
        block = self.view(handle)
        if type(bit) is not int or bit not in (0, 1):
            raise ValueError("run bit must be zero or one")
        if type(count) is not int or count < 0:
            raise ValueError("run count must be a natural integer")
        if block.width + count > self.max_width:
            self.ledger.bump("safety_refusals")
            raise BlockContextBudgetExceeded("Mahler safety width budget exceeded")
        if not count:
            return handle
        powered = binary_power(
            self.cylinder(1, bit),
            count,
            identity=self.cylinder(0, 0),
            compose=self.compose,
        )
        self.ledger.bump("safety_tail_run_compositions", powered.compositions)
        return self.compose(handle, powered.value)

    def close(self) -> None:
        """Release retained research certificates and invalidate their handles."""
        if self._closed:
            return
        node_count, key_count = len(self._nodes), len(self._keys)
        self._nodes.rollback_unpublished(0)
        self._keys.clear()
        if node_count:
            self.ledger.release(self._nodes_owner, entries=node_count, nodes=node_count)
        if key_count:
            self.ledger.release(self._keys_owner, entries=key_count)
        self.ledger.mark_disposed(self._nodes_owner)
        self.ledger.mark_disposed(self._keys_owner)
        self.owner = ArenaToken("disposed-mahler-source-safety")
        self._closed = True


@dataclass(frozen=True, slots=True)
class SourceEvent:
    source: int
    exponent: int
    endpoint: int
    fraction: Q
    next_fraction: Q

    def validate(self) -> None:
        self.fraction.validate()
        self.next_fraction.validate()
        if type(self.source) is not int or self.source <= 0:
            raise ValueError("event requires a positive integer source")
        q = (self.source & -self.source).bit_length()
        if type(self.exponent) is not int or self.exponent != q:
            raise ValueError("event exponent is not selected by the source")
        scale = Q(3**q, 1 << q)
        scaled_w = scale * Q(4) * self.fraction
        if not Interval().contains(self.fraction) or not Q(2) <= scaled_w < Q(3):
            raise ValueError("event violates an intermediate fractional guard")
        endpoint = (3**q * self.source + (1 << (q - 1))) // (1 << q)
        if self.endpoint != endpoint or Q(4) * self.next_fraction != scaled_w - Q(2):
            raise ValueError("event endpoint lost its source binding")


def source_event(
    workspace: SourceSafetyWorkspace, source: int, fraction: Q
) -> SourceEvent:
    """Admit zeros followed by one in the *actual centered source* parity.

    This differs from the older odd-then-zeros Hensel convention. No supplied
    diamond menu or finite tree address is accepted as source authority.
    """
    if type(source) is not int or source <= 0:
        raise ValueError("an event requires a positive integer source")
    q = (source & -source).bit_length()
    if q > workspace.max_width:
        workspace.ledger.bump("safety_refusals")
        raise BlockContextBudgetExceeded("Mahler safety width budget exceeded")
    block = workspace.view(workspace.cylinder(q, source % (1 << q)))
    if not block.guard.contains(fraction):
        raise ValueError("original fractional safety guard fails")
    endpoint = block.endpoint + 3**q * (source >> q)
    value = block.fractional.apply(fraction)
    assert value is not None
    result = SourceEvent(source, q, endpoint, fraction, value)
    result.validate()
    return result


def event_prime_lanes(event: SourceEvent) -> tuple[tuple[int, int, int], ...]:
    """Conditional dyadic-w observer; never an exclusion of arbitrary real t.

    Every lane consumes the same source-selected q. Prime buckets may forget
    these exact lanes only after their safety-preserving quotient is checked.
    """
    event.validate()
    w, after = Q(4) * event.fraction, Q(4) * event.next_fraction
    if w.denominator & (w.denominator - 1):
        raise ValueError("the supplied prime-bank observer requires a dyadic w")
    scale = Q(3**event.exponent, 1 << event.exponent)
    if after != scale * w - Q(2):
        raise ValueError("event is not a diamond-compatible source transport")
    rows: list[tuple[int, int, int]] = []
    for p in PRIME_BANK:
        before_lane = w.numerator * pow(2 * w.denominator, -1, p) % p
        after_lane = prime_lane_after("mahler", p, before_lane, event.exponent)
        exact = after.numerator * pow(2 * after.denominator, -1, p) % p
        if after_lane != exact:
            raise ArithmeticError("prime lane detached from the common event")
        rows.append((p, before_lane, after_lane))
    return tuple(rows)
