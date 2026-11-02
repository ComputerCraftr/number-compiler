"""Finite source-bound Laurent and carry projections for reverse/add.

This consumer advances the exact canonical symmetric RLE port from the
queried term's literal seed. It never creates Q19 roots and never promotes a
supplied carry word into a physical future-period certificate. The term owns
the cache and ledger; this module owns only the arithmetic fold.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass

from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import reverse_add as _metric_keys

from .temporal_port_quotient import (
    DigitRuns,
    SymmetricCoefficientPort,
    decimal_run_residues,
)

MAX_FINITE_LAURENT_TICKS = 4097
_RESIDUE_MODULUS = 1386  # lcm(7, 198)
_J_MODULUS = 693  # 7 * 99, enough to recover J modulo seven


def _require_natural(value: int, name: str) -> None:
    if type(value) is not int or value < 0:
        raise ValueError(f"{name} must be a nonnegative exact integer")


def _decimal_width_upper_bound(value: int) -> int:
    """An integer-only decimal width bound used before seed digit expansion."""
    bits = value.bit_length()
    return max(1, (302 * bits + 999) // 1000)


def _j_from_literal_residues(integer_mod693: int, reverse_mod693: int) -> int:
    difference = (reverse_mod693 - integer_mod693) % _J_MODULUS
    if difference % 99:
        raise ValueError("literal reversal defect is not divisible by 99")
    return (difference // 99) % 7


@dataclass(frozen=True, slots=True)
class LaurentAction7:
    """Rank-one affine action on the alternating accumulators over F7."""

    multiplier: int
    coupling: int
    sum_offset: int
    difference_offset: int

    def __post_init__(self) -> None:
        fields = (
            self.multiplier,
            self.coupling,
            self.sum_offset,
            self.difference_offset,
        )
        if any(type(value) is not int or not 0 <= value < 7 for value in fields):
            raise ValueError("Laurent action coefficients must be canonical mod seven")
        if self.multiplier not in (1, 2, 4):
            raise ValueError("Laurent action multiplier is outside the rank-one family")
        if (1 + 3 * self.coupling) % 7 != self.multiplier:
            raise ValueError("Laurent action violates its rank-one matrix law")

    @classmethod
    def identity(cls) -> LaurentAction7:
        return cls(1, 0, 0, 0)

    @classmethod
    def two_steps(cls, j_source: int, j_middle: int) -> LaurentAction7:
        if any(
            type(value) is not int or not 0 <= value < 7
            for value in (j_source, j_middle)
        ):
            raise ValueError("Laurent forcing values must be canonical mod seven")
        return cls(4, 1, (2 * j_source + j_middle) % 7, -j_middle % 7)

    def apply(self, total: int, difference: int) -> tuple[int, int]:
        if any(
            type(value) is not int or not 0 <= value < 7
            for value in (total, difference)
        ):
            raise ValueError("Laurent input residues must be canonical mod seven")
        return (
            (self.multiplier * total + self.sum_offset) % 7,
            (difference + self.coupling * total + self.difference_offset) % 7,
        )


@dataclass(frozen=True, slots=True)
class SourceBoundLaurentResult:
    """Exact bounded endpoint and alternating-accumulator projections."""

    generation: int
    source_mod7: int
    source_reverse_mod7: int
    target_mod7: int
    target_reverse_mod7: int
    source_mod198: int
    source_reverse_mod198: int
    target_mod198: int
    target_reverse_mod198: int
    first_accumulator_mod7: int
    second_accumulator_mod7: int
    first_accumulator_mod198: int
    second_accumulator_mod198: int

    def cache_snapshot(self) -> tuple[int, ...]:
        """Return the complete immutable numeric payload used by term caches."""
        values = (
            self.generation,
            self.source_mod7,
            self.source_reverse_mod7,
            self.target_mod7,
            self.target_reverse_mod7,
            self.source_mod198,
            self.source_reverse_mod198,
            self.target_mod198,
            self.target_reverse_mod198,
            self.first_accumulator_mod7,
            self.second_accumulator_mod7,
            self.first_accumulator_mod198,
            self.second_accumulator_mod198,
        )
        if any(type(value) is not int for value in values):
            raise ValueError("Laurent observation contains a malformed coordinate")
        return values


@dataclass(slots=True)
class _LaurentWork:
    source_ticks: int = 0
    run_records_visited: int = 0
    operand_bits: int = 0
    paired_blocks_checked: int = 0


def _from_seed(
    seed: int,
    generation: int,
    *,
    work: _LaurentWork,
) -> SourceBoundLaurentResult:
    """Run exact finite source transport under the caller's ledger reservation."""
    _require_natural(seed, "reverse/add seed")
    _require_natural(generation, "generation")
    if generation > MAX_FINITE_LAURENT_TICKS and seed != 0:
        raise ValueError(
            "source-bound Laurent supports at most 4097 physical ticks; "
            "no unbounded carry-driver period is certified"
        )

    if seed == 0:
        return SourceBoundLaurentResult(
            generation=generation,
            source_mod7=0,
            source_reverse_mod7=0,
            target_mod7=0,
            target_reverse_mod7=0,
            source_mod198=0,
            source_reverse_mod198=0,
            target_mod198=0,
            target_reverse_mod198=0,
            first_accumulator_mod7=0,
            second_accumulator_mod7=0,
            first_accumulator_mod198=0,
            second_accumulator_mod198=0,
        )

    source_digits = digits_lsd(seed, 10)
    source_runs = _digits_to_runs(source_digits)
    source_projection = decimal_run_residues(source_runs, _RESIDUE_MODULUS)
    source_integer = source_projection.integer_residue
    source_reverse = source_projection.reverse_residue
    port = SymmetricCoefficientPort.from_source_digits(source_digits)
    work.run_records_visited += (
        len(source_digits)
        + port.half_width
        + 2 * len(port.half_runs)
        + source_projection.run_records_visited
    )
    work.operand_bits += source_projection.operand_bits

    first7, second7 = seed % 7, 0
    first198, second198 = seed % 198, 0
    alternating7 = seed % 7
    alternating198 = seed % 198
    pending_action: LaurentAction7 | None = None
    pending_state7: tuple[int, int] | None = None
    pending_state198: tuple[int, int] | None = None
    pending_middle: SymmetricCoefficientPort | None = None
    pending_q: int | None = None
    current_mod77 = seed % 77
    current_mod1386 = seed % _RESIDUE_MODULUS
    current_reverse1386 = source_reverse
    for tick in range(generation):
        source_port = port
        before_sum7 = current_mod1386 % 7 if tick % 2 == 0 else alternating7
        before_difference7 = (first7 - second7) % 7
        before_sum198 = current_mod1386 % 198 if tick % 2 == 0 else alternating198
        before_difference198 = (first198 - second198) % 198

        transition = source_port.successor_with_carry()
        port = transition.target
        digits = transition.normalized_digits_lsd
        work.source_ticks += 1
        growth = transition.carry.growth
        internal_mask, carry_visits, carry_operand_bits = (
            transition.carry.internal_carry_mask_mod(_RESIDUE_MODULUS)
        )
        scale = 10 if growth else 1
        forward_sum = current_mod1386 + current_reverse1386
        next_integer = forward_sum % _RESIDUE_MODULUS
        scaled_mask = scale * internal_mask + growth
        reverse_correction = 99 * scaled_mask
        reverse_numerator = scale * next_integer - reverse_correction
        next_reverse = reverse_numerator % _RESIDUE_MODULUS
        work.run_records_visited += transition.run_records_visited + carry_visits
        work.operand_bits += carry_operand_bits + sum(
            max(1, abs(value).bit_length())
            for value in (
                current_mod1386,
                current_reverse1386,
                forward_sum,
                next_integer,
                internal_mask,
                scaled_mask,
                reverse_correction,
                reverse_numerator,
                next_reverse,
            )
        )
        next_mod7 = next_integer % 7
        next_mod198 = next_integer % 198
        next_reverse7 = next_reverse % 7
        next_reverse198 = next_reverse % 198
        next_u7 = next_mod7 if (tick + 1) % 2 == 0 else next_reverse7
        next_u198 = next_mod198 if (tick + 1) % 2 == 0 else next_reverse198
        if tick % 2 == 0:
            second7 = (second7 + next_u7 - alternating7) % 7
            second198 = (second198 + next_u198 - alternating198) % 198
        else:
            first7 = (first7 + next_u7 - alternating7) % 7
            first198 = (first198 + next_u198 - alternating198) % 198
        alternating7, alternating198 = next_u7, next_u198

        next_mod77 = next_integer % 77
        if tick % 2 == 0 and tick + 2 <= generation and current_mod77 % 11 == 0:
            if next_mod77 % 11:
                raise AssertionError("exact successor lost its mod-11 source guard")
            # The same issued digit-run projection already owns both residues.
            # Recovering J from a second weighted switch fold would duplicate
            # that work and introduce an unnecessary proof obligation.
            j_source = _j_from_literal_residues(
                current_mod1386 % _J_MODULUS, current_reverse1386 % _J_MODULUS
            )
            j_middle = _j_from_literal_residues(
                next_integer % _J_MODULUS, next_reverse % _J_MODULUS
            )
            q = (digits[-1][0] - digits[0][0]) & 1
            pending_action = LaurentAction7.two_steps(j_source, j_middle)
            pending_state7 = (before_sum7, before_difference7)
            pending_state198 = (before_sum198, before_difference198)
            pending_middle = port
            pending_q = q
        elif tick % 2 == 1 and pending_action is not None:
            if (
                pending_state7 is None
                or pending_state198 is None
                or pending_middle is not source_port
                or pending_q is None
            ):
                raise AssertionError("Laurent action lost its exact chronological seam")
            if pending_action.apply(*pending_state7) != (
                next_mod7,
                (first7 - second7) % 7,
            ):
                raise AssertionError("mod-seven Laurent action disagrees with carries")
            total198, difference198 = pending_state198
            if (
                (4 * total198 + 99 * pending_q) % 198,
                (difference198 + total198 - 99 * pending_q) % 198,
            ) != (next_mod198, (first198 - second198) % 198):
                raise AssertionError(
                    "mod-198 Laurent action disagrees with boundary bit"
                )
            work.paired_blocks_checked += 1
            pending_action = None
            pending_state7 = None
            pending_state198 = None
            pending_middle = None
            pending_q = None

        current_mod77 = next_mod77
        current_mod1386 = next_integer
        current_reverse1386 = next_reverse

    return SourceBoundLaurentResult(
        generation=generation,
        source_mod7=source_integer % 7,
        source_reverse_mod7=source_reverse % 7,
        target_mod7=current_mod1386 % 7,
        target_reverse_mod7=current_reverse1386 % 7,
        source_mod198=source_integer % 198,
        source_reverse_mod198=source_reverse % 198,
        target_mod198=current_mod1386 % 198,
        target_reverse_mod198=current_reverse1386 % 198,
        first_accumulator_mod7=first7,
        second_accumulator_mod7=second7,
        first_accumulator_mod198=first198,
        second_accumulator_mod198=second198,
    )


def _digits_to_runs(digits_lsd: Sequence[int]) -> DigitRuns:
    runs: list[tuple[int, int]] = []
    for digit in digits_lsd:
        if type(digit) is not int or not 0 <= digit <= 9:
            raise ValueError("source digit is outside decimal alphabet")
        if runs and runs[-1][0] == digit:
            previous, count = runs[-1]
            runs[-1] = previous, count + 1
        else:
            runs.append((digit, 1))
    return tuple(runs)


def source_bound_laurent_projection(
    seed: int,
    generation: int,
    *,
    ledger: ResourceLedger,
    scratch_owner: int,
) -> SourceBoundLaurentResult:
    """Build under a caller-reserved, generation-bounded scratch allowance."""
    _require_natural(seed, "reverse/add seed")
    _require_natural(generation, "generation")
    if type(ledger) is not ResourceLedger:
        raise TypeError("Laurent source projection requires its term ledger")
    if generation > MAX_FINITE_LAURENT_TICKS and seed != 0:
        raise ValueError(
            "source-bound Laurent supports at most 4097 physical ticks; "
            "no unbounded carry-driver period is certified"
        )
    max_width = _decimal_width_upper_bound(seed) + min(
        generation, MAX_FINITE_LAURENT_TICKS
    )
    scratch_nodes = 64 if seed == 0 else 24 * max_width + 64
    work = _LaurentWork()
    try:
        with ledger.reservation(scratch_owner, nodes=scratch_nodes):
            result = _from_seed(
                seed,
                generation,
                work=work,
            )
        return result
    except BaseException:
        ledger.bump(_metric_keys.REVERSE_LAURENT_FAILED_WORK)
        raise
    finally:
        ledger.bump(_metric_keys.REVERSE_LAURENT_SOURCE_TICKS, work.source_ticks)
        ledger.bump(
            _metric_keys.REVERSE_LAURENT_RUN_RECORD_VISITS,
            work.run_records_visited,
        )
        ledger.bump(_metric_keys.REVERSE_LAURENT_OPERAND_BITS, work.operand_bits)
        ledger.bump(
            _metric_keys.REVERSE_LAURENT_PAIRED_BLOCKS,
            work.paired_blocks_checked,
        )


__all__ = [
    "MAX_FINITE_LAURENT_TICKS",
    "LaurentAction7",
    "SourceBoundLaurentResult",
    "source_bound_laurent_projection",
]
