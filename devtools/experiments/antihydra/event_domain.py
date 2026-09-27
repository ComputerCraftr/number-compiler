"""Exact next-event exponent domains for one admitted Mahler source block.

This module computes an admission range, not a temporal pump.  The source
block handle remains the authority for each later ``edge(q)`` construction.
If ``J`` is the exact fractional endpoint image and ``w = 4t`` ranges over
``[lower, upper)``, an event exponent ``q >= 1`` is legal precisely when

``upper > 2*(2/3)**q`` and ``lower < 3*(2/3)**q``.

Both predicates are monotone, so exponential bracketing and binary search
recover the complete contiguous integer range without scanning exponents.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from number_compiler.arithmetic.fields.consumer_pullback import (
    HalfOpenInterval as Interval,
)
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.fields.consumer_pullback import ExactRational as Q
from number_compiler.resources.ledger import ResourceLedger

from .source_safety import SourceBlockID, SourceSafetyWorkspace


@dataclass(frozen=True, slots=True)
class EventExponentDomain:
    """A possibly empty contiguous set of positive event exponents.

    ``last=None`` means unbounded only when ``first`` is present.  An empty
    domain has both fields absent.
    """

    first: int | None
    last: int | None

    def __post_init__(self) -> None:
        if self.first is None:
            if self.last is not None:
                raise ValueError("an empty event domain cannot have an upper bound")
            return
        if type(self.first) is not int or self.first < 1:
            raise ValueError("event exponents start at one")
        if self.last is not None and (
            type(self.last) is not int or self.last < self.first
        ):
            raise ValueError("event exponent bounds are reversed")

    @property
    def empty(self) -> bool:
        return self.first is None

    @property
    def unbounded(self) -> bool:
        return self.first is not None and self.last is None

    def contains(self, exponent: int) -> bool:
        return (
            type(exponent) is int
            and self.first is not None
            and exponent >= self.first
            and (self.last is None or exponent <= self.last)
        )


class _ExactSearch:
    def __init__(
        self,
        ledger: ResourceLedger,
        *,
        max_comparisons: int,
        max_operand_bits: int,
    ) -> None:
        if type(max_comparisons) is not int or max_comparisons < 1:
            raise ValueError("positive comparison budget required")
        if type(max_operand_bits) is not int or max_operand_bits < 16:
            raise ValueError("event-domain operand budget is too small")
        self.ledger = ledger
        self.max_comparisons = max_comparisons
        self.max_operand_bits = max_operand_bits
        self.comparisons = 0

    def _products(self, bound: Q, coefficient: int, q: int) -> tuple[int, int]:
        """Return cross-products for ``bound ? coefficient*(2/3)**q``."""
        if type(bound) is not Q or type(q) is not int or q < 1:
            raise TypeError("canonical rational and positive exponent required")
        bound.validate()
        if bound < Q(0) or coefficient < 1:
            raise ValueError("nonnegative bound and positive coefficient required")
        if self.comparisons >= self.max_comparisons:
            self.ledger.bump("mahler_event_domain_refusals")
            raise BlockContextBudgetExceeded(
                "Mahler event-domain comparison budget exceeded"
            )
        # This bound is checked before constructing either large power.
        estimated = (
            2 * bound.numerator.bit_length()
            + 2 * bound.denominator.bit_length()
            + coefficient.bit_length()
            + 6 * q
        )
        if estimated > self.max_operand_bits:
            self.ledger.bump("mahler_event_domain_refusals")
            raise BlockContextBudgetExceeded(
                "Mahler event-domain operand-bit budget exceeded"
            )
        power_two, power_three = 1 << q, 3**q
        left = bound.numerator * power_three
        right = coefficient * bound.denominator * power_two
        operand_bits = left.bit_length() + right.bit_length()
        if operand_bits > self.max_operand_bits:
            self.ledger.bump("mahler_event_domain_refusals")
            raise BlockContextBudgetExceeded(
                "Mahler event-domain operand-bit budget exceeded"
            )
        self.comparisons += 1
        self.ledger.bump("mahler_event_domain_comparisons")
        self.ledger.bump("mahler_event_domain_operand_bits", operand_bits)
        return left, right

    def bound_below_power(self, bound: Q, coefficient: int, q: int) -> bool:
        """Return ``bound < coefficient*(2/3)**q`` exactly."""
        left, right = self._products(bound, coefficient, q)
        return left < right

    def power_below_bound(self, coefficient: int, q: int, bound: Q) -> bool:
        """Return ``coefficient*(2/3)**q < bound`` exactly."""
        left, right = self._products(bound, coefficient, q)
        return right < left


def _first_true(predicate: Callable[[int], bool]) -> int:
    test = predicate
    if test(1):
        return 1
    low, high = 1, 2
    while not test(high):
        low, high = high, high * 2
    while high - low > 1:
        middle = (low + high) // 2
        if test(middle):
            high = middle
        else:
            low = middle
    return high


def _last_true(predicate: Callable[[int], bool]) -> int:
    test = predicate
    if not test(1):
        return 0
    low, high = 1, 2
    while test(high):
        low, high = high, high * 2
    while high - low > 1:
        middle = (low + high) // 2
        if test(middle):
            low = middle
        else:
            high = middle
    return low


def event_exponent_domain(
    w_interval: Interval,
    ledger: ResourceLedger,
    *,
    max_comparisons: int = 256,
    max_operand_bits: int = 1_000_000,
) -> EventExponentDomain:
    """Recover all legal positive exponents for exact ``w`` interval."""
    if type(w_interval) is not Interval:
        raise TypeError("event domain requires one exact half-open interval")
    if type(ledger) is not ResourceLedger:
        raise TypeError("event domain requires a resource ledger")
    w_interval.lower.validate()
    w_interval.upper.validate()
    if w_interval.empty:
        return EventExponentDomain(None, None)
    if w_interval.lower < Q(0):
        raise ValueError("event-domain interval must be nonnegative")
    search = _ExactSearch(
        ledger,
        max_comparisons=max_comparisons,
        max_operand_bits=max_operand_bits,
    )
    # upper > 2*(2/3)^q, expressed as the negation of upper <= rhs.
    first = _first_true(
        lambda q: search.power_below_bound(2, q, w_interval.upper),
    )
    if w_interval.lower == Q(0):
        result = EventExponentDomain(first, None)
    else:
        last = _last_true(
            lambda q: search.bound_below_power(w_interval.lower, 3, q),
        )
        result = (
            EventExponentDomain(first, last)
            if first <= last
            else EventExponentDomain(None, None)
        )
    ledger.bump("mahler_event_domains_constructed")
    return result


def source_event_exponent_domain(
    workspace: SourceSafetyWorkspace,
    handle: SourceBlockID,
    *,
    max_comparisons: int = 256,
    max_operand_bits: int = 1_000_000,
) -> EventExponentDomain:
    """Bind the next-event domain to an authenticated source-block handle."""
    if type(workspace) is not SourceSafetyWorkspace:
        raise TypeError("source event domain requires its source workspace")
    block = workspace.view(handle)
    if block.guard.empty:
        return EventExponentDomain(None, None)
    lower = block.fractional.apply(block.guard.lower)
    upper = block.fractional.apply(block.guard.upper)
    if lower is None or upper is None:
        raise ArithmeticError("source fractional image unexpectedly saturated")
    four = Q(4)
    return event_exponent_domain(
        Interval(four * lower, four * upper),
        workspace.ledger,
        max_comparisons=max_comparisons,
        max_operand_bits=max_operand_bits,
    )


__all__ = [
    "EventExponentDomain",
    "event_exponent_domain",
    "source_event_exponent_domain",
]
