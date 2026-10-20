"""Sparse common-growth integer sign isolation; not source/temporal admission.

The elimination chain uses packet count, not degree/span. Exact sign probes
normalize by a positive binomial packet. Their ratio products are separately
budgeted: no claim of polynomial bit complexity in binary span is made.
Mixed growth is rejected rather than treated as a Chebyshev system.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import pairwise
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from devtools.experiments.reverse_add.radial_modular_sign import ModularSignOracle


@dataclass(frozen=True, slots=True)
class SignLimits:
    max_packets: int = 128
    max_sign_queries: int = 10000
    max_factor_steps: int = 100000
    max_integer_bits: int = 65536
    max_integer_work_bits: int = 10000000
    max_retained_items: int = 20000
    max_operator_terms: int = 20000

    def __post_init__(self) -> None:
        for value in (
            self.max_packets,
            self.max_sign_queries,
            self.max_factor_steps,
            self.max_integer_bits,
            self.max_integer_work_bits,
            self.max_retained_items,
            self.max_operator_terms,
        ):
            if type(value) is not int or value <= 0:
                raise ValueError("sign limits must be positive exact integers")


@dataclass(slots=True)
class SignWork:
    sign_queries: int = 0
    ratio_factors: int = 0
    integer_work_bits: int = 0
    peak_integer_bits: int = 0
    retained_items: int = 0
    peak_retained_items: int = 0
    operator_terms: int = 0
    support_cells: int = 0
    binary_probes: int = 0


@dataclass(frozen=True, slots=True)
class ShiftTerm:
    shift: int
    coefficient: int

    def __post_init__(self) -> None:
        if type(self.shift) is not int or type(self.coefficient) is not int:
            raise TypeError("shifted-binomial terms require exact integers")


@dataclass(frozen=True, slots=True)
class SignRun:
    start: int
    stop: int
    sign: int


class _Work:
    def __init__(
        self,
        counts: SignWork,
        limits: SignLimits,
        modular: ModularSignOracle | None = None,
    ) -> None:
        self.counts = counts
        self.limits = limits
        self.owned = 0
        self.modular = modular

    def bits(self, amount: int) -> None:
        amount = max(1, amount)
        self.counts.integer_work_bits += amount
        self.counts.peak_integer_bits = max(self.counts.peak_integer_bits, amount)
        if amount > self.limits.max_integer_bits:
            raise ValueError("sign integer size budget exhausted")
        if self.counts.integer_work_bits > self.limits.max_integer_work_bits:
            raise ValueError("sign integer work budget exhausted")

    def retain(self, amount: int = 1) -> None:
        # Cumulative conservative reservation for temporary objects in this call.
        if self.counts.retained_items + amount > self.limits.max_retained_items:
            raise ValueError("sign retained-item budget exhausted")
        self.owned += amount
        self.counts.retained_items += amount
        self.counts.peak_retained_items = max(
            self.counts.peak_retained_items, self.counts.retained_items
        )

    def close(self) -> None:
        self.counts.retained_items -= self.owned


def _sign(value: int | Fraction) -> int:
    return (value > 0) - (value < 0)


def _canonical(terms: tuple[ShiftTerm, ...], work: _Work) -> tuple[ShiftTerm, ...]:
    if type(terms) is not tuple or len(terms) > work.limits.max_packets:
        raise ValueError("sign packet budget exhausted")
    work.retain(3 * len(terms))
    values: dict[int, int] = {}
    for term in terms:
        if type(term) is not ShiftTerm:
            raise TypeError("sign isolation requires typed terms")
        term.__post_init__()
        old = values.get(term.shift, 0)
        work.bits(max(old.bit_length(), term.coefficient.bit_length()) + 1)
        work.bits(term.shift.bit_length())
        values[term.shift] = old + term.coefficient
    return tuple(ShiftTerm(s, c) for s, c in sorted(values.items()) if c)


def _eliminate(terms: tuple[ShiftTerm, ...], work: _Work) -> tuple[ShiftTerm, ...]:
    """L_{r,a} deletes the first term; all other shifts move down by one."""
    pivot = terms[0].shift
    work.retain(len(terms) - 1)
    result: list[ShiftTerm] = []
    for term in terms[1:]:
        if work.counts.operator_terms >= work.limits.max_operator_terms:
            raise ValueError("sign operator-term budget exhausted")
        work.counts.operator_terms += 1
        work.bits(max(term.shift.bit_length(), pivot.bit_length()) + 1)
        distance = term.shift - pivot
        work.bits(term.coefficient.bit_length() + distance.bit_length() + 1)
        result.append(ShiftTerm(term.shift - 1, term.coefficient * distance))
    return tuple(result)


def _fraction_add(
    total: Fraction, ratio: Fraction, coefficient: int, work: _Work
) -> Fraction:
    left = total.numerator.bit_length() + ratio.denominator.bit_length()
    right = (
        ratio.numerator.bit_length()
        + coefficient.bit_length()
        + total.denominator.bit_length()
    )
    work.bits(max(left, right) + 1)
    work.bits(total.denominator.bit_length() + ratio.denominator.bit_length())
    return total + coefficient * ratio


def _probe(
    row: int,
    terms: tuple[ShiftTerm, ...],
    k: int,
    work: _Work,
    bound: int | None = None,
) -> int:
    if work.counts.sign_queries >= work.limits.max_sign_queries:
        raise ValueError("sign query budget exhausted")
    work.counts.sign_queries += 1
    if not terms:
        return 0
    if all(t.coefficient > 0 for t in terms):
        return 1
    if all(t.coefficient < 0 for t in terms):
        return -1
    if work.modular is not None:
        if bound is None:
            raise ArithmeticError("modular sign probe has no magnitude hypothesis")
        return work.modular.sign(
            row, tuple((t.shift, t.coefficient) for t in terms), k, bound=bound
        )
    pivot = terms[0].shift
    if len(terms) == 2 and terms[0].coefficient == -terms[1].coefficient:
        # Exact binomial symmetry/unimodality. No factorial or row expansion.
        work.bits(
            max(
                row.bit_length(), k.bit_length(), *(t.shift.bit_length() for t in terms)
            )
            + 4
        )
        first = abs(2 * (k - pivot) - row)
        second = abs(2 * (k - terms[1].shift) - row)
        return _sign(terms[0].coefficient) * _sign(second - first)
    span = terms[-1].shift - pivot
    if span > work.limits.max_factor_steps - work.counts.ratio_factors:
        raise ValueError("sign ratio-factor budget exhausted before expansion")
    ratio = Fraction(1)
    total = Fraction(terms[0].coefficient)
    previous = pivot
    for term in terms[1:]:
        for shift in range(previous, term.shift):
            work.bits(max(k.bit_length(), shift.bit_length(), row.bit_length()) + 2)
            numerator = k - shift
            denominator = row - k + shift + 1
            if numerator <= 0 or denominator <= 0:
                raise ArithmeticError("ratio probe escaped its positive support cell")
            work.bits(ratio.numerator.bit_length() + numerator.bit_length())
            work.bits(ratio.denominator.bit_length() + denominator.bit_length())
            work.counts.ratio_factors += 1
            ratio = Fraction(
                ratio.numerator * numerator, ratio.denominator * denominator
            )
        total = _fraction_add(total, ratio, term.coefficient, work)
        previous = term.shift
    return _sign(total)


def _append(runs: list[SignRun], start: int, stop: int, sign: int, work: _Work) -> None:
    if start >= stop:
        return
    if runs and start < runs[-1].stop:
        if start != runs[-1].stop - 1 or sign != runs[-1].sign:
            raise ArithmeticError("inconsistent shared endpoint in sign reconstruction")
        start = runs[-1].stop
        if start >= stop:
            return
    if runs and start != runs[-1].stop:
        raise ArithmeticError("gap in sign reconstruction")
    work.retain()
    if runs and runs[-1].sign == sign:
        runs[-1] = SignRun(runs[-1].start, stop, sign)
    else:
        runs.append(SignRun(start, stop, sign))


def _restore(
    row: int,
    terms: tuple[ShiftTerm, ...],
    derivative: list[SignRun],
    work: _Work,
    bound: int | None = None,
) -> list[SignRun]:
    cache: dict[int, int] = {}
    result: list[SignRun] = []
    for run in derivative:
        left, right = run.start, run.stop  # inclusive parent endpoints
        for k in (left, right):
            if k not in cache:
                work.retain()
                cache[k] = _probe(row, terms, k, work, bound)
        low_sign, high_sign = cache[left], cache[right]
        if low_sign == high_sign:
            _append(result, left, right + 1, low_sign, work)
            continue
        direction = run.sign
        if not direction or direction * low_sign > direction * high_sign:
            raise ArithmeticError("derivative sign disagrees with monotone ratio")
        cuts: list[int] = []
        for threshold in (0, 1):
            low, high = left, right + 1
            while low < high:
                work.bits(max(low.bit_length(), high.bit_length()) + 1)
                middle = (low + high) // 2
                if middle not in cache:
                    work.retain()
                    work.counts.binary_probes += 1
                    cache[middle] = _probe(row, terms, middle, work, bound)
                if direction * cache[middle] >= threshold:
                    high = middle
                else:
                    low = middle + 1
            cuts.append(low)
        _append(result, left, cuts[0], -direction, work)
        _append(result, cuts[0], cuts[1], 0, work)
        _append(result, cuts[1], right + 1, direction, work)
    return result


def _cell(
    row: int,
    terms: tuple[ShiftTerm, ...],
    start: int,
    stop: int,
    work: _Work,
    bound: int | None = None,
) -> list[SignRun]:
    # Explicit postorder chain, no recursive function or coefficient scan.
    levels: list[tuple[int, tuple[ShiftTerm, ...], int, int | None]] = []
    while len(terms) > 1 and stop - start > 1:
        work.retain()
        levels.append((row, terms, stop, bound))
        terms = _eliminate(terms, work)
        if bound is not None:
            # On this positive-pivot cell both operator weights are nonnegative
            # and their sum is row+1. The original bound is a caller hypothesis.
            work.bits(bound.bit_length() + row.bit_length() + 2)
            bound *= row + 1
        row += 1
        stop -= 1
    value = _probe(row, terms, start, work, bound)
    work.retain()
    runs = [SignRun(start, stop, value)]
    while levels:
        row, terms, expected_stop, bound = levels.pop()
        runs = _restore(row, terms, runs, work, bound)
        if runs[0].start != start or runs[-1].stop != expected_stop:
            raise ArithmeticError("sign reconstruction changed its admitted interval")
    return runs


def isolate_common_growth_signs(
    row: int,
    terms: tuple[ShiftTerm, ...],
    start: int,
    stop: int,
    *,
    work: SignWork,
    limits: SignLimits | None = None,
) -> tuple[SignRun, ...]:
    """Exact integer sign partition of sum c_s*choose(row,k-s), [start,stop).

    Support endpoints and binary probes replace a coefficient walk. Point
    comparison remains a separately bounded exact-rational operation. Returned
    intervals carry no source, chart or successor-publication authority.
    """
    return _isolate(row, terms, start, stop, work=work, limits=limits)


def isolate_common_growth_signs_assuming_bound(
    row: int,
    terms: tuple[ShiftTerm, ...],
    start: int,
    stop: int,
    *,
    assumed_bound: int,
    modular: ModularSignOracle,
    work: SignWork,
    limits: SignLimits | None = None,
) -> tuple[SignRun, ...]:
    """Conditional CRT extractor: caller must prove |f(k)|<=bound on the interval.

    Congruence does not authenticate this hypothesis: a false bound can produce
    an incorrect sign. This research API grants no source/publication authority.
    Bounds for successive eliminations are transported, never guessed from jets.
    """
    if type(assumed_bound) is not int or assumed_bound < 0:
        raise ValueError("magnitude hypothesis must be a nonnegative exact integer")
    return _isolate(
        row,
        terms,
        start,
        stop,
        work=work,
        limits=limits,
        bound=assumed_bound,
        modular=modular,
    )


def _isolate(
    row: int,
    terms: tuple[ShiftTerm, ...],
    start: int,
    stop: int,
    *,
    work: SignWork,
    limits: SignLimits | None,
    bound: int | None = None,
    modular: ModularSignOracle | None = None,
) -> tuple[SignRun, ...]:
    if any(type(v) is not int for v in (row, start, stop)):
        raise TypeError("row and interval require exact integers")
    if row < 0 or stop < start:
        raise ValueError("invalid binomial row or interval")
    transaction = _Work(work, limits or SignLimits(), modular)
    try:
        transaction.bits(
            max(row.bit_length(), start.bit_length(), stop.bit_length()) + 2
        )
        if bound is not None:
            transaction.bits(bound.bit_length())
        canonical = _canonical(terms, transaction)
        if start == stop:
            return ()
        transaction.retain(2 + 4 * len(canonical))
        boundaries = {start, stop}
        for term in canonical:
            transaction.bits(max(term.shift.bit_length(), row.bit_length()) + 2)
            for boundary in (term.shift, term.shift + row + 1):
                if start < boundary < stop:
                    boundaries.add(boundary)
        order = sorted(boundaries)
        result: list[SignRun] = []
        for left, right in pairwise(order):
            active = tuple(t for t in canonical if t.shift <= left <= t.shift + row)
            transaction.retain(len(active))
            work.support_cells += 1
            for run in _cell(row, active, left, right, transaction, bound):
                _append(result, run.start, run.stop, run.sign, transaction)
        return tuple(result)
    finally:
        transaction.close()
