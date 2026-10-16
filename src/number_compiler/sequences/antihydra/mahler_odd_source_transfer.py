"""Exact source-side odd-return summaries shared by the compiler and scheduler.

The logical Antihydra return word at a positive odd centered source ``D`` is
``1, 0**(a - 1)``, where ``a = v2(3D + 1)``.  This module owns the cheap exact
source arithmetic used to recognize that word.  Harmonic and fractional
consumers remain in their existing action owners and are constructed only
after a repeated source motif has actually been witnessed.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.fields.two_adic import v2_nonzero, v2_positive
from number_compiler.sequences.antihydra.mahler_source_actions import (
    MAX_MAHLER_SOURCE_EXTENT,
)

if TYPE_CHECKING:
    from number_compiler.sequences.antihydra.mahler_mixed_harmonic_ring import (
        MahlerMixedOddHarmonicRing,
    )


class _OddEventExtentExceedsBudget(BlockContextBudgetExceeded):
    """A valid next event simply does not fit in the remaining requested span."""


@dataclass(frozen=True, slots=True)
class MahlerOddEventSummary:
    """One exact odd-centered-source event, with logical and ledger effects."""

    source: int
    exponent: int
    endpoint: int

    def __post_init__(self) -> None:
        if type(self.source) is not int or self.source <= 0 or not self.source & 1:
            raise ValueError("odd event source must be a positive odd integer")
        if type(self.exponent) is not int or self.exponent < 1:
            raise ValueError("odd event extent must be a positive integer")
        if (
            type(self.endpoint) is not int
            or self.endpoint <= 0
            or not self.endpoint & 1
        ):
            raise ValueError("odd event endpoint must be a positive odd integer")

    @property
    def extent(self) -> int:
        """Logical normalized returns consumed; this is not the TM roof."""
        return self.exponent

    @property
    def odd_events(self) -> int:
        return 1

    @property
    def ledger_delta(self) -> int:
        return 3 - self.exponent

    @property
    def ledger_minimum(self) -> int:
        return min(0, self.ledger_delta)

    @property
    def odd_h_steps(self) -> int:
        """The conjugate physical-h parity word is ``0,1**(a-1)``."""
        return self.exponent - 1


def summarize_mahler_odd_event(
    source: int,
    *,
    max_extent: int = MAX_MAHLER_SOURCE_EXTENT,
    max_bits: int = 65_536,
    reserve_bits: Callable[[int], None] | None = None,
) -> MahlerOddEventSummary:
    """Compute one source-selected event without building a harmonic action.

    ``reserve_bits`` is supplied by production callers before large integer
    operations.  The compiler uses the same arithmetic core without a ledger.
    """
    if type(source) is not int or source <= 0 or not source & 1:
        raise ValueError("odd event requires a positive odd centered source")
    if type(max_extent) is not int or not 1 <= max_extent <= MAX_MAHLER_SOURCE_EXTENT:
        raise ValueError("odd event extent is outside the exact source budget")
    if type(max_bits) is not int or not 1 <= max_bits <= 1_048_576:
        raise ValueError("odd event bit budget is outside the supported bound")
    source_bits = source.bit_length()
    if source_bits > max_bits:
        raise BlockContextBudgetExceeded("odd event source exceeds the bit budget")
    if reserve_bits is not None:
        reserve_bits(8 * (source_bits + 16))
    numerator = 3 * source + 1
    exponent = v2_positive(numerator)
    if exponent > max_extent:
        raise _OddEventExtentExceedsBudget(
            "odd event exceeds the remaining requested extent"
        )
    # Compute 3^(a-1) * (numerator >> a), avoiding an intermediate product
    # whose size needlessly includes the known 2^a factor.
    quotient = numerator >> exponent
    estimated_bits = source_bits + 2 * exponent + 16
    if estimated_bits > max_bits:
        raise BlockContextBudgetExceeded(
            "odd event endpoint exceeds the exact integer bit budget"
        )
    if reserve_bits is not None:
        reserve_bits(8 * estimated_bits)
    endpoint = pow(3, exponent - 1) * quotient
    if endpoint <= 0 or endpoint & 1 == 0:
        raise ArithmeticError("source-selected odd event lost its odd endpoint")
    return MahlerOddEventSummary(source, exponent, endpoint)


@dataclass(frozen=True, slots=True)
class MahlerOddMacroSelection:
    """One repeated exact source motif ready for powered application."""

    prefix_steps: int
    source: int
    ring: MahlerMixedOddHarmonicRing
    repetitions: int
    witnessed_events: int

    def __post_init__(self) -> None:
        if type(self.prefix_steps) is not int or self.prefix_steps < 0:
            raise ValueError("odd macro prefix extent must be natural")
        if type(self.source) is not int or self.source <= 0 or not self.source & 1:
            raise ValueError("odd macro source must be a positive odd integer")
        from number_compiler.sequences.antihydra.mahler_mixed_harmonic_ring import (
            MahlerMixedOddHarmonicRing,
        )

        if type(self.ring) is not MahlerMixedOddHarmonicRing:
            raise TypeError("odd macro selection requires a source-certified ring")
        if type(self.repetitions) is not int or self.repetitions < 2:
            raise ValueError("odd macro selection must contain at least two copies")
        if type(self.witnessed_events) is not int or self.witnessed_events < 2:
            raise ValueError("odd macro selection needs two witnessed copies")
        if self.witnessed_events != 2 * len(self.ring.exponents):
            raise ValueError("odd macro witness does not cover exactly two motifs")
        if self.ring.source != self.source or not self.ring.admits(self.repetitions):
            raise ValueError("odd macro selection lost its source-cylinder authority")

    @property
    def extent(self) -> int:
        return self.ring.extent * self.repetitions

    @property
    def events(self) -> int:
        return len(self.ring.exponents) * self.repetitions


def select_source_certified_odd_macro(
    source: int,
    remaining_steps: int,
    *,
    max_events: int = 8,
    max_extent: int = MAX_MAHLER_SOURCE_EXTENT,
    max_bits: int = 65_536,
    max_residual_steps: int | None = None,
    reserve_bits: Callable[[int], None] | None = None,
    on_event_work: Callable[[int, int], None] | None = None,
) -> MahlerOddMacroSelection | None:
    """Find and power a repeated prefix only after two exact copies are seen.

    A bounded lookahead of at most eight odd events chooses the first repeated
    prefix motif (period at most four).  The ring's exact 2-adic defect then
    authorizes the maximal repeat count within the requested extent.  Misses
    do not construct the heavier integer/fractional/harmonic actions.
    """
    if type(source) is not int or source <= 0:
        raise ValueError("odd macro selection requires a positive centered source")
    if type(remaining_steps) is not int or remaining_steps < 0:
        raise ValueError("remaining odd macro extent must be natural")
    if type(max_events) is not int or not 2 <= max_events <= 8:
        raise ValueError("odd macro selection is bounded to two through eight events")
    if type(max_extent) is not int or not 1 <= max_extent <= MAX_MAHLER_SOURCE_EXTENT:
        raise ValueError("odd macro extent is outside the exact source budget")
    if type(max_bits) is not int or not 1 <= max_bits <= 1_048_576:
        raise ValueError("odd macro bit budget is outside the supported bound")
    if max_residual_steps is not None and (
        type(max_residual_steps) is not int or max_residual_steps < 0
    ):
        raise ValueError("odd macro residual budget must be natural")
    if remaining_steps < 2 or source.bit_length() > max_bits:
        return None
    if on_event_work is not None:
        on_event_work(0, source.bit_length())

    prefix_steps = 0
    current = source
    if current & 1 == 0:
        zero_run = min(remaining_steps, v2_positive(current))
        if zero_run >= remaining_steps:
            return None
        if zero_run > max_extent:
            return None
        if reserve_bits is not None:
            reserve_bits(8 * (current.bit_length() + 2 * zero_run + 16))
        if on_event_work is not None:
            on_event_work(0, current.bit_length() + 2 * zero_run)
        current = pow(3, zero_run) * (current >> zero_run)
        if on_event_work is not None:
            on_event_work(0, current.bit_length())
        prefix_steps = zero_run
    if current <= 0 or current & 1 == 0:
        raise ArithmeticError("odd macro prefix did not reach an odd source")

    available = min(remaining_steps - prefix_steps, max_extent)
    if available < 2:
        return None
    exponents: list[int] = []
    endpoints: list[int] = []
    current_source = current
    consumed = 0
    for _ in range(max_events):
        if on_event_work is not None:
            on_event_work(1, current_source.bit_length())
        try:
            event = summarize_mahler_odd_event(
                current_source,
                max_extent=available - consumed,
                max_bits=max_bits,
                reserve_bits=reserve_bits,
            )
        except _OddEventExtentExceedsBudget:
            break
        if consumed + event.extent > available:
            break
        exponents.append(event.exponent)
        consumed += event.extent
        current_source = event.endpoint
        endpoints.append(current_source)
        if on_event_work is not None:
            on_event_work(0, event.exponent.bit_length() + event.endpoint.bit_length())
        if consumed >= available:
            break

    # A witnessed motif endpoint determines exact capacity without constructing a
    # harmonic or fractional action. For motif extent L, its affine defect is
    # 2**L * (D - E), where E is the source after one witnessed copy.
    # Compare all candidate periods discovered in the bounded lookahead, then
    # build only the best exact action. Later events need not repeat the motif:
    # the 2-adic capacity itself decides whether the continuation is admitted.
    candidates: list[tuple[int, int, int, int, tuple[int, ...]]] = []
    for period in range(1, min(4, len(exponents) // 2) + 1):
        motif = tuple(exponents[:period])
        if exponents[period : 2 * period] != exponents[:period]:
            continue
        motif_extent = sum(motif)
        if motif_extent * 2 > available:
            continue
        one_copy_endpoint = endpoints[period - 1]
        defect = current - one_copy_endpoint
        if defect == 0:
            continue
        capacity = (motif_extent + v2_nonzero(defect) - 1) // motif_extent
        repetitions = min(capacity, available // motif_extent)
        covered_extent = repetitions * motif_extent
        residual_steps = remaining_steps - prefix_steps - covered_extent
        if repetitions >= 2 and (
            max_residual_steps is None or residual_steps <= max_residual_steps
        ):
            candidates.append((covered_extent, period, capacity, repetitions, motif))
    if not candidates:
        return None
    _selected_extent, period, expected_capacity, expected_repetitions, motif = max(
        candidates, key=lambda item: (item[0], -item[1])
    )
    from number_compiler.sequences.antihydra.mahler_mixed_harmonic_ring import (
        MahlerMixedOddHarmonicRing,
    )

    ring = MahlerMixedOddHarmonicRing.from_source(current, motif)
    if ring.capacity != expected_capacity:
        raise ArithmeticError(
            "cheap odd-motif defect disagrees with source-cylinder capacity"
        )
    repetitions = min(ring.capacity, available // ring.extent)
    if repetitions < 2:
        raise ArithmeticError("source-cylinder capacity lost its witnessed repeat")
    if repetitions != expected_repetitions:
        raise ArithmeticError("source-cylinder repeat count changed after selection")
    return MahlerOddMacroSelection(
        prefix_steps,
        current,
        ring,
        repetitions,
        2 * period,
    )


__all__ = (
    "MahlerOddEventSummary",
    "MahlerOddMacroSelection",
    "select_source_certified_odd_macro",
    "summarize_mahler_odd_event",
)
