"""Bounded prime/carry readouts of an admitted fractional-safety event.

These readouts never select a source event. The prime possibility quotient
forgets phase, but an actual observation uses one common source-selected phase
in every lane. Carry inspection is an explicitly charged bounded reference,
not a claim of sublinear temporal construction or a production scheduler.
"""

from __future__ import annotations

from dataclasses import dataclass

from devtools.experiments.antihydra.source_safety import (
    PRIME_BANK,
    SourceEvent,
    event_prime_lanes,
)
from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    apply_carry_fn,
    value_carry_fn,
)
from number_compiler.arithmetic.carry.collatz_carry_wires import (
    collatz_digit_carry_wires,
)
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.consumer_pullback import ExactRational as Q
from number_compiler.resources.ledger import ResourceLedger


def prime_buckets(prime: int, ledger: ResourceLedger) -> tuple[int, ...]:
    """Stable full-phase *possibility* buckets of the fixed research bank."""
    if type(prime) is not int or prime not in PRIME_BANK:
        raise ValueError("prime must belong to the declared finite observer bank")
    multiplier = 3 * pow(2, -1, prime) % prime
    phases = [1]
    value = multiplier
    while value != 1:
        phases.append(value)
        value = value * multiplier % prime
    labels = tuple(int(u != 0) for u in range(prime))
    while True:
        classes: dict[tuple[int, tuple[tuple[int, bool, bool], ...]], int] = {}
        result = []
        for u in range(prime):
            outcomes = set()
            for phase in phases:
                v = (phase * u - 1) % prime
                outcomes.add((labels[v], u != 0 and v == 0, u == 0 and v != 0))
                ledger.bump("mahler_prime_phase_visits")
            signature = (labels[u], tuple(sorted(outcomes)))
            result.append(classes.setdefault(signature, len(classes)))
        refined = tuple(result)
        ledger.bump("mahler_prime_refinement_rounds")
        if refined == labels:
            return refined
        labels = refined


@dataclass(frozen=True, slots=True)
class EventObservations:
    source: int
    exponent: int
    prime_buckets: tuple[tuple[int, int, int], ...]
    multiplication: tuple[tuple[tuple[int, int, int], ...], ...]
    subtraction: tuple[CarryFn, ...]
    raw_numerator: int
    denominator_exponent: int


def observe_event(
    event: SourceEvent, ledger: ResourceLedger, *, max_columns: int = 4096
) -> EventObservations:
    """Read the same admitted event through both finite observer algebras."""
    if type(max_columns) is not int or max_columns < 1:
        raise ValueError("positive column budget required")
    lanes = event_prime_lanes(
        event
    )  # Also validates source, q, guard and dyadic scope.
    w = Q(4) * event.fraction
    numerator, exponent = w.numerator, w.denominator.bit_length() - 1
    width = event.exponent
    # Refuse before constructing a large future numeral or iterating over digits.
    conservative_columns = width * (
        (abs(numerator).bit_length() + 2 * width + 5) // 6 + 1
    )
    conservative_columns += (
        max(abs(numerator).bit_length() + 2 * width, exponent + width + 2) + 5
    ) // 6 + 1
    if conservative_columns > max_columns:
        ledger.bump("mahler_observer_refusals")
        raise BlockContextBudgetExceeded(
            "Mahler carry observation exceeds column budget"
        )
    stages = []
    for _ in range(width):
        current, carry, place, emitted = numerator, 0, 1, 0
        actions = []
        while current:
            current, digit = divmod(current, 64)
            action = collatz_digit_carry_wires(digit, base=64)
            actions.append(action.outputs)
            emitted += ((3 * digit + carry) % 64) * place
            carry = action.apply(carry)
            place *= 64
            ledger.bump("mahler_carry_columns")
        emitted += carry * place
        if emitted != 3 * numerator:
            raise ArithmeticError("multiplication carry lost its emitted value")
        numerator = emitted
        stages.append(tuple(actions))
    subtrahend = 1 << (exponent + width + 1)
    if numerator < subtrahend:
        raise ValueError("fractional safety event has a negative endpoint")
    columns = max(1, (max(numerator, subtrahend).bit_length() + 5) // 6)
    n, m, carry, emitted, place = numerator, subtrahend, 1, 0, 1
    subtraction = []
    for _ in range(columns):
        n, digit = divmod(n, 64)
        m, other = divmod(m, 64)
        coefficient = digit + 63 - other
        borrow_action = value_carry_fn(coefficient, base=64)
        subtraction.append(borrow_action)
        emitted += ((coefficient + carry) % 64) * place
        carry = apply_carry_fn(borrow_action, carry)
        place *= 64
        ledger.bump("mahler_carry_columns")
    emitted += (carry - 1) * place
    if (
        emitted != numerator - subtrahend
        or Q(emitted, 1 << (exponent + width)) != Q(4) * event.next_fraction
    ):
        raise ArithmeticError("subtraction carry lost the source endpoint")
    buckets = []
    for p, before, after in lanes:
        partition = prime_buckets(p, ledger)
        buckets.append((p, partition[before], partition[after]))
    return EventObservations(
        event.source,
        width,
        tuple(buckets),
        tuple(stages),
        tuple(subtraction),
        emitted,
        exponent + width,
    )
