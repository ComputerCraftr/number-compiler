"""Untrusted packed comma-control candidate, built from canonical chart moves.

This research compiler shares the production arithmetic but grants no runtime
admission. Base construction and mask composition are measured separately;
packing a table does not prove a cheap constructor or its Isabelle refinement.
"""

from __future__ import annotations

import argparse
import json
from collections.abc import Callable
from dataclasses import dataclass
from math import gcd
from time import perf_counter
from typing import Literal

from devtools.experiments.comma.generate_rank_candidate import (
    _decade_round_candidate,
)
from number_compiler.sequences.comma.arithmetic import (
    cycle_residue_period,
    cycle_transfer,
    phase_prefix_displacement,
)
from number_compiler.sequences.comma.boundary_chart import (
    PERIOD,
    BoundaryChart,
    chart_step,
)

FULL_MASK = (1 << PERIOD) - 1


@dataclass(frozen=True, slots=True)
class FrobeniusClock:
    """Exponent-five anchored CRT clock; no branch-safety authority."""

    c4: int
    c3: int
    c7: int
    c11: int

    def __post_init__(self) -> None:
        if any(
            type(value) is not int or not 0 <= value < modulus
            for value, modulus in zip(
                (self.c4, self.c3, self.c7, self.c11), (4, 3, 7, 11), strict=True
            )
        ):
            raise ValueError("invalid comma Frobenius clock")

    @classmethod
    def from_residue(cls, residue: int) -> FrobeniusClock:
        if type(residue) is not int or not 0 <= residue < 924:
            raise ValueError("invalid comma power residue")
        theta = residue - 5
        return cls(theta % 4, theta % 3, theta % 7, theta % 11)

    def advance(self) -> FrobeniusClock:
        return FrobeniusClock(
            (self.c4 + 1) % 4,
            (self.c3 + 1) % 3,
            (self.c7 + 1) % 7,
            (self.c11 + 1) % 11,
        )

    def short_phase(self, displacement: int) -> int:
        """Project only the CRT coordinates observed by this orbit."""
        period = cycle_residue_period(displacement)
        parity = self.c4 % 2
        if period == 1:
            return 0
        if period == 2:
            return parity
        if period == 3:
            return self.c3
        if period == 6:
            return parity + 2 * ((self.c3 - parity) * 2 % 3)
        if period == 22:
            return parity + 2 * ((self.c11 - parity) * 6 % 11)
        return self.c4 + 4 * ((self.c7 - self.c4) * 2 % 7)


@dataclass(frozen=True, slots=True)
class FrobeniusEntry:
    """Control coordinates with the orbit position needed for exact transport.

    Equal ``(leading, orbit, innovation)`` does not assert equal literal
    weights. The original offset and exponent remain occurrence data in the
    weighted chart constructor.
    """

    leading: int
    orbit: int
    position: int
    orbit_displacement: int
    potential: int
    modulus: int
    deck: int
    power: int
    innovation: int

    @property
    def control_id(self) -> tuple[int, int, int]:
        return self.leading, self.orbit, self.innovation

    @property
    def canonical_headroom(self) -> int:
        minimum = 1 + int(self.leading < 9)
        return minimum + (-self.orbit - 10 * self.innovation - minimum) % (
            10 * self.modulus
        )

    @property
    def headroom(self) -> int:
        """Exact Entry-to-Near lift, including the digit-orbit displacement."""
        minimum = 1 + int(self.leading < 9)
        return minimum + (
            self.canonical_headroom - self.orbit_displacement - minimum
        ) % (10 * self.modulus)


def entry_diagonal_headroom(
    leading: int, offset: int, power: int, displacement: int
) -> int:
    """Exact digit/diagonal headroom; this does not erase occurrence weight.

    The checked power is divisible by ten. Its quotient centers the spatial
    quotient before headroom is reconstructed. No orbit row is searched.
    """
    if (
        type(leading) is not int
        or not 1 <= leading <= 9
        or type(offset) is not int
        or offset < 0
        or type(displacement) is not int
        or displacement <= 0
        or type(power) is not int
        or not 0 <= power < displacement
        or displacement % 10
        or power % 10
    ):
        raise ValueError("invalid comma Entry diagonal")
    quotient, digit = divmod(offset, 10)
    diagonal = (quotient - power // 10) % (displacement // 10)
    minimum = 1 + int(leading < 9)
    return minimum + (-10 * diagonal - digit - minimum) % displacement


def frobenius_entry(
    leading: int,
    offset: int,
    clock: FrobeniusClock,
    *,
    charge_bits: Callable[[int], None] | None = None,
) -> FrobeniusEntry:
    """Recenter one exact Entry into its bounded digit-orbit innovation.

    Only a local digit orbit (at most ten terms) is evaluated. There is no
    graph enumeration, memo table, sampled exponent, or admission decision.
    """
    if type(offset) is not int or offset < 0 or type(clock) is not FrobeniusClock:
        raise ValueError("invalid comma Frobenius Entry")
    transfer = cycle_transfer(leading, offset % 10)
    divisor = gcd(leading, 10)
    orbit = offset % divisor
    digit = offset % 10
    position = (
        (digit - orbit) // divisor * pow(leading // divisor, -1, transfer.period)
    ) % transfer.period
    displacement = phase_prefix_displacement(leading, orbit, position)
    potential = (displacement - digit + orbit) // 10
    modulus = transfer.displacement // 10
    deck = (offset // 10 - potential) % modulus
    exponent = 5 + clock.short_phase(transfer.displacement)
    if charge_bits is not None:
        charge_bits(offset.bit_length() + 128 + 32 * position)
        charge_bits(2 * exponent.bit_length() * transfer.displacement.bit_length())
    power = pow(10, exponent, transfer.displacement) // 10
    return FrobeniusEntry(
        leading,
        orbit,
        position,
        displacement,
        potential,
        modulus,
        deck,
        power,
        (deck - power) % modulus,
    )


def offset_orbit(offset: int) -> int:
    """Signed subtraction is essential before the modulo operation."""
    if type(offset) is not int or not 0 <= offset <= 90:
        raise ValueError("comma decade offset must be in 0..90")
    digit = offset % 10
    return ((offset - (5 * digit * digit - 4 * digit)) % 460) // 10


def orbit_representatives() -> tuple[int, ...]:
    fibers: dict[int, int] = {}
    for offset in range(91):
        fibers.setdefault(offset_orbit(offset), offset)
    if set(fibers) != set(range(46)):
        raise AssertionError("offset orbit does not cover 46 fibers")
    return tuple(fibers[i] for i in range(46))


def rotate_phase(mask: int, advance: int) -> int:
    """Pullback: result[r] = mask[(r + advance) mod 924]."""
    if type(mask) is not int or not 0 <= mask <= FULL_MASK:
        raise ValueError("phase mask is outside the 924-bit domain")
    if type(advance) is not int:
        raise TypeError("phase advance must be an integer")
    shift = advance % PERIOD
    return ((mask >> shift) | (mask << (PERIOD - shift))) & FULL_MASK


@dataclass(frozen=True, order=True)
class WordOutput:
    kind: Literal["live", "fork", "landmine"]
    value: int = 0
    crossings: int = 0

    def __post_init__(self) -> None:
        if (
            type(self.value) is not int
            or type(self.crossings) is not int
            or self.crossings < 0
        ):
            raise ValueError("malformed control label")
        if self.kind == "live":
            valid = 0 <= self.value < 46 and self.crossings == 0
        elif self.kind == "fork":
            valid = 2 <= self.value <= 9
        else:
            valid = self.kind == "landmine" and self.value == 0
        if not valid:
            raise ValueError("invalid live or terminal control label")


@dataclass(frozen=True)
class PhaseWord:
    """A disjoint total partition; each leaf keeps its exact stop label/count."""

    leaves: tuple[tuple[WordOutput, int], ...]

    def __post_init__(self) -> None:
        occupied = 0
        labels: set[WordOutput] = set()
        for output, mask in self.leaves:
            if output in labels or mask <= 0 or mask & ~FULL_MASK or occupied & mask:
                raise ValueError("duplicate, overlapping or malformed phase partition")
            labels.add(output)
            occupied |= mask
        if occupied != FULL_MASK:
            raise ValueError("phase partition omits admitted phases")

    def at(self, phase: int) -> WordOutput:
        if type(phase) is not int or not 0 <= phase < PERIOD:
            raise ValueError("phase must be in 0..923")
        return next(output for output, mask in self.leaves if mask & (1 << phase))


def _word(parts: dict[WordOutput, int]) -> PhaseWord:
    return PhaseWord(tuple(sorted((out, mask) for out, mask in parts.items() if mask)))


def reference_base_words() -> tuple[PhaseWord, ...]:
    """Measured reference construction, not quotient-first proof generation."""
    words = []
    for representative in orbit_representatives():
        parts: dict[WordOutput, int] = {}
        for phase in range(PERIOD):
            step = _decade_round_candidate(phase, representative)
            if step.successor is not None:
                next_phase, offset = step.successor
                if next_phase != (phase + 1) % PERIOD:
                    raise AssertionError("canonical decade step violated phase helix")
                output = WordOutput("live", offset_orbit(offset))
            elif step.fork_a is not None:
                output = WordOutput("fork", step.fork_a)
            else:
                output = WordOutput("landmine")
            parts[output] = parts.get(output, 0) | (1 << phase)
        words.append(_word(parts))
    return tuple(words)


def square_words(
    words: tuple[PhaseWord, ...], span: int
) -> tuple[tuple[PhaseWord, ...], int]:
    if type(span) is not int or span < 1 or len(words) != 46:
        raise ValueError("invalid source-fiber action or span")
    result = []
    intersections = 0
    for word in words:
        parts: dict[WordOutput, int] = {}
        for left, mask in word.leaves:
            if left.kind != "live":
                parts[left] = parts.get(left, 0) | mask
                continue
            if not 0 <= left.value < 46 or left.crossings != 0:
                raise ValueError("invalid live fiber")
            for right, right_mask in words[left.value].leaves:
                intersections += 1
                common = mask & rotate_phase(right_mask, span)
                if common:
                    output = (
                        right
                        if right.kind == "live"
                        else WordOutput(right.kind, right.value, span + right.crossings)
                    )
                    parts[output] = parts.get(output, 0) | common
        result.append(_word(parts))
    return tuple(result), intersections


@dataclass(frozen=True)
class SectorBranch:
    mask: int
    target: tuple[int, int] | WordOutput


class SectorMaskCompiler:
    """Postorder control DAG over Entry(f,x), with only short clock branches.

    No whole phase table is created. Actual source offsets and weighted literal
    counts are deliberately outside this control-only research representation.
    """

    def __init__(self) -> None:
        self.words: dict[tuple[int, int], PhaseWord] = {}
        self.branches: dict[tuple[int, int], tuple[SectorBranch, ...]] = {}
        self.chart_moves = 0
        self.intersections = 0
        self.stack_visits = 0

    def _branches(self, leading: int, offset: int) -> tuple[SectorBranch, ...]:
        transfer = cycle_transfer(leading, offset % 10)
        period = cycle_residue_period(transfer.displacement)
        if PERIOD % period:
            raise AssertionError("local cyclotomic period does not divide 924")
        repetition = FULL_MASK // ((1 << period) - 1)
        branches = []
        for phase in range(period):
            chart = BoundaryChart("entry", leading, 0, offset)
            while True:
                self.chart_moves += 1
                move = chart_step(phase, chart)
                if move.next_chart is None:
                    target: tuple[int, int] | WordOutput = (
                        WordOutput("landmine")
                        if move.fork_a is None
                        else WordOutput("fork", move.fork_a)
                    )
                    break
                next_chart = move.next_chart
                if next_chart.kind == "entry":
                    if next_chart.delta == 1 and next_chart.leading == 1:
                        target = WordOutput("live", offset_orbit(next_chart.coordinate))
                    elif next_chart.delta == 0 and next_chart.leading == leading + 1:
                        target = (next_chart.leading, next_chart.coordinate)
                    else:
                        raise AssertionError("sector failed its chronological measure")
                    break
                if chart.kind == "near" and next_chart.coordinate >= chart.coordinate:
                    raise AssertionError("near move did not decrease headroom")
                chart = next_chart
            branches.append(SectorBranch(repetition << phase, target))
        return tuple(branches)

    def word(self, leading: int, offset: int) -> PhaseWord:
        if (
            type(leading) is not int
            or type(offset) is not int
            or not 1 <= leading <= 9
            or not 0 <= offset <= 98
        ):
            raise ValueError("sector response requires leading=1..9 and offset=0..98")
        root = (leading, offset)
        stack = [root]
        while stack:
            self.stack_visits += 1
            key = stack[-1]
            if key in self.words:
                stack.pop()
                continue
            if key not in self.branches:
                self.branches[key] = self._branches(*key)
            missing = next(
                (
                    branch.target
                    for branch in self.branches[key]
                    if isinstance(branch.target, tuple)
                    and branch.target not in self.words
                ),
                None,
            )
            if missing is not None:
                stack.append(missing)
                continue
            parts: dict[WordOutput, int] = {}
            for branch in self.branches[key]:
                if isinstance(branch.target, WordOutput):
                    parts[branch.target] = parts.get(branch.target, 0) | branch.mask
                else:
                    for output, mask in self.words[branch.target].leaves:
                        self.intersections += 1
                        common = mask & branch.mask
                        if common:
                            parts[output] = parts.get(output, 0) | common
            self.words[key] = _word(parts)
            stack.pop()
        return self.words[root]

    def base_words(self) -> tuple[PhaseWord, ...]:
        return tuple(self.word(1, x) for x in orbit_representatives())

    def boundary_words(self, decades: tuple[PhaseWord, ...]) -> tuple[PhaseWord, ...]:
        if len(decades) != 46 or any(
            out.kind == "live" for word in decades for out, _ in word.leaves
        ):
            raise ValueError("boundary construction requires 46 complete stop words")
        result = []
        for kind in ("N", "Z"):
            for a in range(2, 10):
                # N(a,p) has one unique crossing into Entry(a,90+a-1).
                # Compute it from the same canonical Near owner, not a table.
                offset = 0
                if kind == "N":
                    self.chart_moves += 1
                    move = chart_step(0, BoundaryChart("near", a - 1, 0, 1))
                    expected = move.next_chart
                    if (
                        expected is None
                        or expected.kind != "entry"
                        or expected.leading != a
                        or expected.delta != 0
                    ):
                        raise AssertionError(
                            "N boundary did not enter its expected sector"
                        )
                    offset = expected.coordinate
                word = self.word(a, offset)
                parts: dict[WordOutput, int] = {}
                for out, mask in word.leaves:
                    if out.kind != "live":
                        parts[out] = parts.get(out, 0) | mask
                        continue
                    for tail, tail_mask in decades[out.value].leaves:
                        self.intersections += 1
                        common = mask & rotate_phase(tail_mask, 1)
                        if common:
                            if tail.kind == "live":
                                raise ValueError("B32 incomplete at boundary")
                            target = WordOutput(
                                tail.kind, tail.value, 1 + tail.crossings
                            )
                            parts[target] = parts.get(target, 0) | common
                result.append(_word(parts))
        return tuple(result)


def losing_fixed_point(words: tuple[PhaseWord, ...]) -> tuple[tuple[int, ...], int]:
    """Synchronous Boolean tropical closure; round one is terminal rank zero."""
    if len(words) != 16:
        raise ValueError("boundary action needs all sixteen schemas")
    losing: tuple[int, ...] = (0,) * 16
    rounds = 0
    while True:
        updated = []
        for schema, word in enumerate(words):
            mask = losing[schema]
            for out, source_mask in word.leaves:
                if out.kind == "landmine":
                    mask |= source_mask
                elif out.kind == "fork" and 2 <= out.value <= 9:
                    index = out.value - 2
                    # Membership is a pullback, hence positive exponent gain.
                    both = losing[index] & losing[index + 8]
                    mask |= source_mask & rotate_phase(both, out.crossings)
                else:
                    raise ValueError(
                        "boundary word is not a complete fork/landmine action"
                    )
            updated.append(mask)
        next_losing = tuple(updated)
        if next_losing == losing:
            return losing, rounds
        rounds += 1
        if rounds > 16 * PERIOD:
            raise AssertionError("monotone finite losing iteration did not stabilize")
        losing = next_losing


def surviving_cycle(
    words: tuple[PhaseWord, ...], losing: tuple[int, ...]
) -> tuple[int, int, str]:
    initial = (0, 10)
    current = initial
    visited: set[tuple[int, int]] = set()
    gain = 0
    choices = []
    while current not in visited:
        visited.add(current)
        schema, phase = current
        if losing[schema] & (1 << phase):
            raise AssertionError("cycle entered a losing cylinder")
        out = words[schema].at(phase)
        if out.kind != "fork":
            raise AssertionError("survivor has no complete fork")
        next_phase = (phase + out.crossings) % PERIOD
        alternatives = (out.value - 2, out.value - 2 + 8)
        live = [
            child for child in alternatives if not losing[child] & (1 << next_phase)
        ]
        if len(live) != 1:
            raise AssertionError("survivor fork is not uniquely determined")
        choices.append(str(int(live[0] >= 8)))
        current = (live[0], next_phase)
        gain += out.crossings
    if current != initial:
        raise AssertionError("source orbit has a transient before its return")
    survivors = {
        (schema, phase)
        for schema, mask in enumerate(losing)
        for phase in range(PERIOD)
        if not mask & (1 << phase)
    }
    if visited != survivors:
        raise AssertionError("source cycle does not cover all surviving cylinders")
    return len(visited), gain, "".join(choices)


def audit(*, compare_reference: bool = False) -> dict[str, object]:
    start = perf_counter()
    compiler = SectorMaskCompiler()
    words = compiler.base_words()
    base_seconds = perf_counter() - start
    base_moves = compiler.chart_moves
    base_nodes = len(compiler.words)
    reference_seconds = 0.0
    if compare_reference:
        start = perf_counter()
        if words != reference_base_words():
            raise AssertionError(
                "symbolic sector words disagree with canonical full rounds"
            )
        reference_seconds = perf_counter() - start
    levels = []
    span = 1
    for _ in range(5):
        start = perf_counter()
        words, intersections = square_words(words, span)
        span *= 2
        levels.append(
            {
                "span": span,
                "intersections": intersections,
                "leaves": sum(len(w.leaves) for w in words),
                "seconds": perf_counter() - start,
            }
        )
    outputs = {out for word in words for out, _ in word.leaves}
    start = perf_counter()
    boundary = compiler.boundary_words(words)
    boundary_seconds = perf_counter() - start
    start = perf_counter()
    losing, rounds = losing_fixed_point(boundary)
    fixed_point_seconds = perf_counter() - start
    length, gain, choice_word = surviving_cycle(boundary, losing)
    return {
        "candidate_only": True,
        "production_admission": False,
        "base_scalar_evaluations": 0,
        "base_chart_moves": base_moves,
        "base_sector_nodes": base_nodes,
        "all_sector_nodes": len(compiler.words),
        "all_short_phase_branches": sum(len(bs) for bs in compiler.branches.values()),
        "all_chart_moves": compiler.chart_moves,
        "all_sector_mask_intersections": compiler.intersections,
        "all_sector_stack_visits": compiler.stack_visits,
        "reference_scalar_evaluations": 46 * PERIOD if compare_reference else 0,
        "reference_seconds": reference_seconds,
        "base_seconds": base_seconds,
        "levels": levels,
        "B32_live_outputs": sum(out.kind == "live" for out in outputs),
        "B32_distinct_outputs": len(outputs),
        "max_stop_crossings": max(out.crossings for out in outputs),
        "boundary_scalar_evaluations": 0,
        "boundary_seconds": boundary_seconds,
        "losing_count": sum(mask.bit_count() for mask in losing),
        "max_losing_rank": rounds - 1,
        "fixed_point_seconds": fixed_point_seconds,
        "survivors": 16 * PERIOD - sum(mask.bit_count() for mask in losing),
        "source_cycle_length": length,
        "source_cycle_gain": gain,
        "source_cycle_choices": choice_word,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compare-reference", action="store_true")
    args = parser.parse_args()
    print(json.dumps(audit(compare_reference=args.compare_reference), sort_keys=True))


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
