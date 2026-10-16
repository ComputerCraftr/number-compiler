"""Demanded digit harmonics for completed, source-bound 6305 macros."""

from __future__ import annotations

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.fields.homogeneous_growth import (
    HomogeneousGrowthScale,
)
from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.arithmetic.fields.walsh import walsh64_mod5
from number_compiler.sequences.collatz.border_carry_cylinder import (
    Border6305CarryCylinder,
)
from number_compiler.sequences.collatz.border_harmonic_ring import (
    PeriodicTail6305Ring,
)
from number_compiler.sequences.collatz.border_identity import (
    BorderEntryPort,
    BorderExitPort,
)
from number_compiler.sequences.collatz.border_return_grammar import (
    BorderReturnMacro,
    validate_border_return_macro,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.position_cycle_harmonics import (
    CenteredMotifPositionOrbit,
    PositionHarmonicSpectrum,
)


def demanded_position_harmonics(
    macro: BorderReturnMacro,
    radix: int,
    position: int,
    *,
    walsh64: bool = False,
) -> PositionHarmonicSpectrum:
    """Read digit frequencies at exact issued return seams.

    Fixed and changing tails use their source-bound finite rings. Other
    variable tails retain the issued upper-carry cursor and never infer a
    successor past the published macro.
    """
    validate_border_return_macro(macro)
    if not macro.zero_tails:
        raise ValueError("position harmonic needs an admitted 6305 return")
    if type(radix) is not int or not 2 <= radix <= 64:
        raise ValueError("position radix must be 2..64")
    if type(position) is not int or position < 0:
        raise ValueError("position must be nonnegative")
    if (position + 1) * radix.bit_length() > 4096:
        raise BlockContextBudgetExceeded("position exceeds the exact modulus budget")
    if type(walsh64) is not bool:
        raise TypeError("Walsh64 demand must be Boolean")
    if walsh64 and len(macro.zero_tails) < 64:
        raise ValueError("Walsh64 needs 64 authenticated border returns")

    current = macro.source
    if macro.entry_port is BorderEntryPort.DIGIT_SIX:
        current //= 2
    elif macro.entry_port is BorderEntryPort.DIGIT_ZERO:
        current >>= v2_positive(current)
    if current % 10 == 5:
        current = (3 * current + 1) // 2
    if current % 10 != 3:
        raise ValueError("issued return word has no three-digit source seam")

    if not any(macro.zero_tails):
        initial = Border6305CarryCylinder.from_three_digit(current)
        if initial.zero_tail != 0:
            raise AssertionError("all-zero return word has a nonzero initial tail")
        return initial.demanded_position_harmonics(
            len(macro.zero_tails), radix, position, walsh64=walsh64
        )
    if len(set(macro.zero_tails)) == 1:
        tail = macro.zero_tails[0]
        upper = Border6305CarryCylinder.from_three_digit(current)
        if upper.zero_tail != tail:
            raise AssertionError("constant-tail source lost its upper guard")
        one = DyadicTerminalFieldAction.one_run(1)
        word = one.then(DyadicTerminalFieldAction.zero_run(tail)).then(one)
        return CenteredMotifPositionOrbit(
            current, len(macro.zero_tails), word, 2
        ).spectrum(radix, position, walsh64=walsh64)

    if macro.exit_port in (
        BorderExitPort.RETURN_TO_THREE,
        BorderExitPort.RETURN_AT_HORIZON,
    ):
        for period in (2, 3, 4):
            if len(macro.zero_tails) < period * 2 or len(macro.zero_tails) % period:
                continue
            motif = macro.zero_tails[:period]
            if (
                len(set(motif)) == 1
                or motif * (len(macro.zero_tails) // period) != macro.zero_tails
            ):
                continue
            ring = PeriodicTail6305Ring.from_source(current, motif)
            groups = len(macro.zero_tails) // period
            if ring.admits(groups):
                return ring.demanded_position_harmonics(
                    groups, radix, position, walsh64=walsh64
                )

    modulus = radix ** (position + 1)
    place = modulus // radix
    counts = [0] * radix
    mask = 0
    cursor: Border6305CarryCylinder | None = None
    total_halvings = 0
    for index, zero_tail in enumerate(macro.zero_tails):
        if cursor is None:
            cursor = Border6305CarryCylinder.from_three_digit(current)
        if cursor.zero_tail != zero_tail:
            raise AssertionError("variable-tail orbit lost its issued upper cursor")
        before_digit = (current // place) % radix
        endpoint = cursor.endpoint
        counts[before_digit] += 1
        if walsh64 and index < 64 and ((endpoint // place) % radix != before_digit):
            mask |= 1 << index
        total_halvings += zero_tail + 2
        following = None
        if index + 1 < len(macro.zero_tails):
            following = cursor.next_return()
            if following is None:
                raise AssertionError(
                    "issued variable-tail word crosses a terminal border"
                )
        current, cursor = endpoint, following

    return PositionHarmonicSpectrum(
        radix=radix,
        position=position,
        repetitions=len(macro.zero_tails),
        counts=tuple(counts),
        forced_position_interval=None,
        forced_position_digit=None,
        two_adic_forced_through=None,
        ternary_forced_from=None,
        odd_preperiod=None,
        odd_period=None,
        evaluated_cells=len(macro.zero_tails),
        radial_scale=HomogeneousGrowthScale(2 * len(macro.zero_tails), total_halvings),
        walsh64_change_mod5=walsh64_mod5(mask) if walsh64 else None,
    )


__all__ = ["demanded_position_harmonics"]
