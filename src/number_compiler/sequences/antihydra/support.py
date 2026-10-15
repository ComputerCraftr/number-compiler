"""Section tape support and a compressed literal-transition grammar.

The grammar retains transition labels before prime evaluation. Repeating sweeps
have quadratic timestamps; they must never be expanded into physical events.
"""

from __future__ import annotations

import itertools
from collections.abc import Iterator
from math import comb

from number_compiler.resources.metric_keys import antihydra as _antihydra_keys
from number_compiler.sequences.antihydra.machine import TRANSITIONS
from number_compiler.sequences.antihydra.runtime import Run

# Ports are 2*state+read, in the pinned machine alphabet.
A0, A1, B0, B1, C0, C1, D0, D1, E0, E1, F0, F1 = range(12)
STARTUP = ((A0, 1), (B0, 1), (C1, 1), (C0, 1), (D0, 1), (A0, 1), (B1, 1), (E1, 4))


def sweep(j: int) -> tuple[tuple[int, int], ...]:
    return (
        (E0, 1),
        (F1, 1),
        (A1, 3 * j + 1),
        (A0, 1),
        (B0, 1),
        (C1, 3 * j + 2),
        (C0, 1),
        (D1, 1),
        (B1, 1),
        (E1, 2),
    )


def section_suffix(a: int, b: int) -> tuple[tuple[int, int], ...]:
    if a < 0 or b < 3:
        raise ValueError("published section grammar requires a>=0, b>=3")
    k = b // 2
    v: tuple[tuple[int, int], ...] = (
        (E0, 1),
        (F1, 1),
        (A1, 3 * k - 2),
        (A0, 1),
        (B0, 1),
        (C1, 3 * k - 1),
        (C0, 1),
        (D1, 1),
    )
    w = ((E0, 1), (F1, 1), (A1, 2 if b & 1 else 1), (A0, 1), (B1, 1), (E1, 3 * k + 1))
    if b & 1:
        v += ((B1, 1),)
        return v + (((E0, 1), (F0, 1)) if a == 0 else w)
    return v + ((B0, 1), (C1, a), (C0, 1), (D0, 1), (A0, 1), (B1, 1), (E1, a + 3)) + w


def move(port: int) -> int:
    transition = TRANSITIONS[port // 2][port % 2]
    return 0 if transition is None else transition[1]


def tape_intervals(result: Run) -> tuple[tuple[int, int, int], ...]:
    """Disjoint constant-prime intervals [lo,hi) of the visited terminal tape."""
    result.require_source()
    if result.halted:
        # Previous section had a=0; F0 is one cell left of its separator.
        head = result.head
        k = (result.h - 5) // 2
        return (
            (head, head + 1, 2),
            (head + 1, head + 3, 3),
            (head + 3, head + 4, 2),
            (head + 4, head + 4 + 3 * k, 3),
            (head + 4 + 3 * k, head + 5 + 3 * k, 2),
        )
    separator = -4 - result.returns
    lo = -3 if result.returns == 0 else separator - result.balance
    intervals = (
        (lo, separator, 3),
        (max(lo, separator), separator + 1, 2),
        (separator + 1, result.head, 3),
        (result.head, result.head + 1, 2),
    )
    return tuple((a, b, p) for a, b, p in intervals if a < b)


def integer_binomial(n: int, k: int) -> int:
    """Integer-valued binomial, including negative Laurent exponents."""
    return comb(n, k) if n >= 0 else (-1) ** k * comb(k - n - 1, k)


def tape_hasse(result: Run, degree: int, modulus: int) -> tuple[int, ...]:
    """Coefficients of P(1+X), computed before any cyclic quotient."""
    intervals = tape_intervals(result)
    return tuple(
        sum(
            p * (integer_binomial(hi, k + 1) - integer_binomial(lo, k + 1))
            for lo, hi, p in intervals
        )
        % modulus
        for k in range(degree + 1)
    )


def source_sections(result: Run) -> Iterator[tuple[int, int, int, int]]:
    """Fold retained chronological cylinder support into section coordinates.

    The arithmetic owner already discovered every branch and retained it in
    bounded (at most 64-bit) cylinder words.  A demanded projection consumes
    those words in order.  It does not query the source recurrence again and
    does not retain a second itinerary.  The finite projection still performs
    one charged support fold per represented macro return because each section
    has its own spacetime translation.
    """
    from number_compiler.sequences.antihydra.blocks import (
        Cylinder,
        arithmetic_from_word,
        physical_roof,
        terminal_effect,
    )

    result.require_source()
    h, a, head, time = 8, 0, 1, 11
    completed = 0
    terminated = False
    if result.returns == 0:
        if (head, time) != (result.head, result.physical_ticks):
            raise ArithmeticError("event support diverged from bound execution")
        return
    owner = result.ledger.register("antihydra.observer.leaf-roofs", "workspace")
    result.ledger.reserve(owner, nodes=1)
    atoms: list[Cylinder | None] = [None, None]
    retained_atoms = 0
    try:
        # ``result`` was authenticated above. Publish the retained support once
        # and consume its ledger-owned store directly; the public property
        # otherwise repeats whole-result validation before this linear fold.
        segments = result._term._materialize_segments(result)
        for segment in segments:
            block = segment.cylinder
            if segment.start != completed or block.residue != h % (1 << block.width):
                raise ValueError("retained Antihydra section support was changed")
            offset = 0
            while offset < block.width and completed < result.returns:
                odd = (block.parity_word >> offset) & 1
                if odd != h & 1:
                    raise ValueError("retained Antihydra branch support was changed")
                counters = result.ledger.counters
                counters["observer_retained_support_steps"] = (
                    counters.get("observer_retained_support_steps", 0) + 1
                )
                counters["observer_retained_support_operand_bits"] = (
                    counters.get("observer_retained_support_operand_bits", 0)
                    + h.bit_length()
                    + a.bit_length()
                    + time.bit_length()
                )
                yield a, h - 4, head, time
                completed += 1
                if a == 0 and odd:
                    dl, dr = terminal_effect(h)
                    time += dl + dr
                    head += dr - dl
                    terminated = True
                    break
                leaf = atoms[odd]
                if leaf is None:
                    result.ledger.reserve(owner, nodes=1)
                    try:
                        leaf = physical_roof(arithmetic_from_word(odd, 1, odd))
                        atoms[odd] = leaf
                        retained_atoms += 1
                    except BaseException:
                        result.ledger.release(owner, nodes=1)
                        raise
                    counters["observer_retained_leaf_roof_constructions"] = (
                        counters.get("observer_retained_leaf_roof_constructions", 0) + 1
                    )
                h, a, dl, dr = leaf.apply(h, a)
                counters["observer_retained_physical_roof_terms"] = (
                    counters.get("observer_retained_physical_roof_terms", 0) + 1
                )
                time += dl + dr
                head += dr - dl
                offset += 1
            if completed == result.returns or terminated:
                break
        if (head, time) != (result.head, result.physical_ticks):
            raise ArithmeticError("event support diverged from bound execution")
    finally:
        result.ledger.release(owner, nodes=1 + retained_atoms)


def _directional_word(
    word: tuple[tuple[int, int], ...], head: int, degree: int
) -> list[list[int]]:
    values = [[0] * (degree + 1) for _ in range(2)]
    runs: list[tuple[int, int]] = []
    for port, count in word:
        direction = move(port)
        if not direction or not count:
            continue
        if runs and runs[-1][0] == direction:
            runs[-1] = direction, runs[-1][1] + count
        else:
            runs.append((direction, count))
    # Directional moments depend on the visited interval, not on which TM
    # control port traversed it. Adjacent equal-direction ports in a sweep
    # share one interval and therefore one short binomial row.
    for direction, count in runs:
        lo, hi = (head, head + count) if direction > 0 else (head - count + 1, head + 1)
        channel = values[int(direction > 0)]
        # Build the two integer-valued binomial rows once. This recurrence is
        # exact for negative Laurent coordinates as well as positive ones;
        # calling ``comb`` separately for every order repeatedly rebuilds the
        # same short falling products at each sweep sample.
        upper = lower = 1
        for order in range(degree + 1):
            k = order + 1
            upper = upper * (hi - k + 1) // k
            lower = lower * (lo - k + 1) // k
            channel[order] += upper - lower
        head += direction * count
    return values


def directional_hasse(result: Run, degree: int, modulus: int) -> dict[str, object]:
    """Spatial Hasse moments of L/R events before quotienting, via exact sums.

    For order d each sweep's run sum is a polynomial in its index of degree at
    most d+1. Newton forward differences sum arbitrarily many sweeps using
    d+2 samples. This operation never enumerates their physical events.
    """
    if type(degree) is not int or not 0 <= degree <= 8 or modulus < 2:
        raise ValueError("directional moments require order 0..8 and modulus>=2")
    result.require_source()
    totals = _directional_word(STARTUP, 0, degree)
    samples = 0
    for a, b, head, _ in source_sections(result):
        count = b // 2 - 1
        rows = [
            _directional_word(sweep(j), head - 2 * j, degree) for j in range(degree + 2)
        ]
        samples += degree + 2
        for channel in range(2):
            for order in range(degree + 1):
                differences = [value[channel][order] for value in rows]
                for d in range(degree + 2):
                    totals[channel][order] += differences[0] * integer_binomial(
                        count, d + 1
                    )
                    differences = [y - x for x, y in itertools.pairwise(differences)]
        suffix = _directional_word(section_suffix(a, b), head - 2 * count, degree)
        for channel in range(2):
            for order in range(degree + 1):
                totals[channel][order] = (
                    totals[channel][order] + suffix[channel][order]
                ) % modulus
    if (totals[0][0] % modulus, totals[1][0] % modulus) != (
        result.left % modulus,
        result.right % modulus,
    ):
        raise ArithmeticError(
            "directional support augmentation disagrees with physical clock"
        )
    result.ledger.counters[_antihydra_keys.DIRECTIONAL_POLYNOMIAL_SAMPLES] = samples
    return {
        "center": 1,
        "modulus": modulus,
        "left": [x % modulus for x in totals[0]],
        "right": [x % modulus for x in totals[1]],
    }
