"""Authenticated weighted decimal carry projection for guarded Collatz ports.

This module owns the detailed per-source weighted inlet calculation. The
``GuardedPortJoin`` API delegates here so its source/bridge contract remains
small and the unique calculation is not duplicated.
"""

from __future__ import annotations

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
)
from number_compiler.sequences.collatz.source_closed_port_action import (
    SourceCongruence,
)

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.guarded_port_join import GuardedPortJoin


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
        tens, hundreds, odds, last, compositions, squarings = powered
        return GuardedTemporalCarryCounts.create_checked(
            program_guard,
            steps,
            odds,
            tens,
            hundreds,
            last,
            matrix_power_period=5,
            forced_six_reset_events=0,
            port_punctures=0,
            matrix_compositions=compositions,
            matrix_squarings=squarings,
            scalar_steps=0,
        )
    if steps > max_steps:
        raise BlockContextBudgetExceeded(
            "unproved nonperiodic carry-inlet program exceeds its budget"
        )
    value = source
    prefix = DyadicTerminalFieldAction.identity()
    odds = tens = hundreds = resets = remainders = 0
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
    )
