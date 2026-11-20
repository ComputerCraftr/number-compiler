"""Authenticated weighted decimal carry projection for guarded Collatz ports.

This module owns the detailed per-source weighted inlet calculation. The
``GuardedPortJoin`` API delegates here so its source/bridge contract remains
small and the unique calculation is not duplicated.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.sequences.collatz.border_pair_temporal_matrix import (
    WeightedPairMatrix,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.guarded_port_source import (
    restrict_forced_five_suffix as _restrict_forced_five_suffix,
)
from number_compiler.sequences.collatz.guarded_port_source import (
    restrict_source as _restrict,
)
from number_compiler.sequences.collatz.guarded_radix6_bridge import (
    FiveBand,
    GuardedTemporalCarryCounts,
    certify_guarded_radix6_bridge,
    common_plus_one_valuation,
    merge_bands,
    trace_is_zero_tail,
)
from number_compiler.sequences.collatz.source_closed_port_action import (
    MacroTraceGrammar,
    SourceCongruence,
)

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.guarded_port_join import GuardedPortJoin


@dataclass(frozen=True, slots=True)
class PoweredZeroTailCarries:
    """Exact carry result for one source-guarded zero-tail matrix program."""

    carry_tens: int
    carry_hundreds: int
    odds: int
    last_pair: int
    matrix_power_period: int
    matrix_compositions: int
    matrix_squarings: int
    matrix_row_evaluations: int

    def __post_init__(self) -> None:
        values = (
            self.carry_tens,
            self.carry_hundreds,
            self.odds,
            self.last_pair,
            self.matrix_power_period,
            self.matrix_compositions,
            self.matrix_squarings,
            self.matrix_row_evaluations,
        )
        if any(type(value) is not int or value < 0 for value in values):
            raise ValueError("invalid powered zero-tail carry result")
        if self.matrix_power_period not in (1, 5) or self.last_pair >= 100:
            raise ValueError("powered zero-tail period or endpoint is invalid")
        if self.matrix_squarings > self.matrix_compositions:
            raise ValueError("matrix squarings exceed the product count")


def power_zero_tail_carries(
    joined: GuardedPortJoin,
    source: int,
) -> PoweredZeroTailCarries | None:
    """Power the measured inlet-matrix period on one authenticated source row.

    This constructor requires the complete source cylinder to force the
    zero-tail 6305 trace and enough 2-adic depth for every return. It compares
    the generated ordered 100-state matrix blocks before authorizing a power.
    """
    if not joined.source.contains(source):
        raise ValueError("powered carry source is outside its original guard")
    trace = joined.port.trace
    if type(trace) is not MacroTraceGrammar or trace.length == 0:
        return None
    returns = trace.length
    if (
        returns > 8192
        or joined.port.action.steps != 2 * returns
        or joined.port.odd_events != 2 * returns
        or not joined.bridge.centered_at_minus_one
        or not trace_is_zero_tail(trace)
        or common_plus_one_valuation(joined.source, 2) < 2 * returns + 2
    ):
        return None
    phase = joined.source.forced_residue(25)
    if phase is None:
        return None
    if pow(21, 5, 25) != 1:
        raise ArithmeticError("low cyclotomic carry clock is not period five")

    inverse_16 = pow(16, -1, 25)
    blocks: list[tuple[WeightedPairMatrix, WeightedPairMatrix]] = []
    for index in range(5):
        residue_25 = (pow(21, index, 25) * (phase + 1) - 1) % 25
        source_400 = 15 + 16 * (((residue_25 - 15) * inverse_16) % 25)
        after_first_200 = ((3 * source_400 + 1) // 2) % 200
        blocks.append(
            (
                WeightedPairMatrix.odd_half((source_400 // 100) & 1),
                WeightedPairMatrix.odd_half((after_first_200 // 100) & 1),
            )
        )
    period = next(
        (
            candidate
            for candidate in (1, 5)
            if all(blocks[index] == blocks[index % candidate] for index in range(5))
        ),
        None,
    )
    if period is None:
        raise ArithmeticError("generated inlet matrices have no certified period")

    cycle = WeightedPairMatrix.identity()
    compositions = 0
    for block in blocks[:period]:
        for matrix in block:
            cycle = cycle.then(matrix)
            compositions += 1
    complete_cycles, remainder = divmod(returns, period)
    powered_row = cycle.power_row_with_work(source % 100, complete_cycles)
    compositions += powered_row.matrix_compositions
    squarings = powered_row.matrix_squarings
    row_evaluations = powered_row.row_evaluations
    row = powered_row.row
    for block in blocks[:remainder]:
        for matrix in block:
            following: set[tuple[int, int, int]] = set()
            for entry in row:
                successors = matrix.successors(entry[0])
                row_evaluations += 1
                for output, tens, hundreds in successors:
                    following.add((output, entry[1] + tens, entry[2] + hundreds))
            row = tuple(sorted(following))

    endpoint_pair = joined.port.endpoint(source) % 100
    pointed = tuple(entry for entry in row if entry[0] == endpoint_pair)
    if len(pointed) != 1:
        raise ArithmeticError(
            "guarded matrix power has no unique source endpoint carry row"
        )
    last, tens, hundreds = pointed[0]
    if last != endpoint_pair:
        raise ArithmeticError("guarded carry matrix lost its source endpoint")
    return PoweredZeroTailCarries(
        tens,
        hundreds,
        2 * returns,
        last,
        period,
        compositions,
        squarings,
        row_evaluations,
    )


def authenticate_weighted_ports(
    joined: GuardedPortJoin,
    source: int,
    *,
    max_steps: int = 512,
) -> GuardedTemporalCarryCounts:
    """Intersect every demanded temporal matrix row with its source guard.

    At stage t, the original source must imply the entire 200-state inlet
    letter under the affine prefix, as well as every available source-wide
    base-6 five-suffix reset. The matrix then yields the exact two decimal
    carry arrivals. On an authenticated five-phase period the same proof uses
    the logarithmic powered matrix, not a linear walk.
    """
    steps = joined.port.action.steps
    if type(max_steps) is not int or not 0 <= max_steps <= 4096:
        raise ValueError("invalid joined matrix temporal budget")
    if type(source) is not int or not joined.source.contains(source):
        raise ValueError("temporal inlet source is outside joint source guard")
    program_modulus = 200 << steps
    program_guard = SourceCongruence(source % program_modulus, program_modulus)
    fiber = _restrict(joined.source, program_guard)
    if fiber is None or not fiber.contains(source):
        raise ArithmeticError("temporal inlet preimage has no original-source fiber")
    # The special five-return cycle is proved for the COMPLETE original
    # joined cylinder. It must never be inferred from just a pointed root.
    powered = joined.powered_zero_tail_carries(source)
    if powered is not None:
        tens = powered.carry_tens
        hundreds = powered.carry_hundreds
        odds = powered.odds
        last = powered.last_pair
        return GuardedTemporalCarryCounts.create_checked(
            program_guard,
            steps,
            odds,
            tens,
            hundreds,
            last,
            matrix_power_period=powered.matrix_power_period,
            forced_six_reset_events=0,
            port_punctures=0,
            matrix_compositions=powered.matrix_compositions,
            matrix_squarings=powered.matrix_squarings,
            scalar_steps=0,
            matrix_row_evaluations=powered.matrix_row_evaluations,
        )
    if steps > max_steps:
        raise BlockContextBudgetExceeded(
            "unproved nonperiodic carry-inlet program exceeds its budget"
        )
    value = source
    prefix = DyadicTerminalFieldAction.identity()
    odds = tens = hundreds = resets = remainders = row_evaluations = 0
    # All source alternatives inside the *inlet guard* have these guaranteed
    # base-6 fives; the original wider source cannot be used as a substitute
    # for a stricter source-derived observation.
    original_cover = certify_guarded_radix6_bridge(
        fiber,
        prefix,
        0,
        max_upper_digits=0,
        max_lower_digits=32,
    )
    bands = original_cover.source_fives
    v2 = common_plus_one_valuation(fiber, 2)
    v3 = common_plus_one_valuation(fiber, 3)
    for t in range(steps):
        # Detect newly born fives from the exact centered affine action, then
        # put their 6-adic congruence into the ORIGINAL source guard.
        if prefix.offset + (1 << t) == prefix.gain and v2 >= t:
            born = min(v2 - t, v3 + odds)
            if born:
                bands = merge_bands(bands + (FiveBand(0, born),))
        odd_now = value & 1
        for band in bands:
            if odd_now:
                resets += band.upper - band.lower
            remainders += max(0, band.upper - band.lower - odd_now)
            if band.lower == 0:
                checked = _restrict_forced_five_suffix(fiber, prefix, band)
                if checked is None or checked.count != fiber.count:
                    raise ArithmeticError(
                        "forced radix-6 carry reset contradicts a matrix source row"
                    )
        letter = SourceCongruence(value % 200, 200).pullback(prefix)
        constrained = None if letter is None else _restrict(fiber, letter)
        if constrained is None or constrained.count != fiber.count:
            raise ArithmeticError(
                "weighted matrix inlet is not forced by its complete source guard"
            )
        pair, high, odd = value % 100, (value // 100) & 1, value & 1
        matrix = (
            WeightedPairMatrix.odd_half(high) if odd else WeightedPairMatrix.even(high)
        )
        rows = matrix.successors(pair)
        row_evaluations += 1
        if len(rows) != 1:
            raise ArithmeticError("guarded decimal inlet has no normalized successor")
        output, c1, c2 = rows[0]
        step = (
            DyadicTerminalFieldAction.one_run(1)
            if odd
            else DyadicTerminalFieldAction.zero_run(1)
        )
        next_value = ((3 * value + 1) // 2) if odd else value // 2
        if next_value % 100 != output:
            raise ArithmeticError(
                "forced carry/matrix output contradicts exact affine step"
            )
        prefix = prefix.then(step)
        odds += odd
        tens += c1
        hundreds += c2
        value = next_value
        bands = merge_bands(
            tuple(
                carried
                for band in bands
                if (carried := band.through(odd, 1)) is not None
            )
        )
    if (
        prefix.coefficient_snapshot() != joined.port.action.coefficient_snapshot()
        or odds != joined.port.odd_events
        or value != joined.port.endpoint(source)
    ):
        raise ArithmeticError("joined matrix tape disagrees with the issued macro")
    return GuardedTemporalCarryCounts.create_checked(
        program_guard,
        steps,
        odds,
        tens,
        hundreds,
        value % 100,
        matrix_power_period=None,
        forced_six_reset_events=resets,
        forced_six_div_remainders=remainders,
        port_punctures=steps,
        scalar_steps=steps,
        matrix_row_evaluations=row_evaluations,
    )
