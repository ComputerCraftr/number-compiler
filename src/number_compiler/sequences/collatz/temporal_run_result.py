"""Validated result record for a source-bound physical Collatz run."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.sequences.collatz.tape_width import CollatzTapeWidthSummary

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.temporal_run_quotient import (
        CollatzF5AffineAction,
        CollatzRootFiberCertificate,
    )


@dataclass(frozen=True, slots=True)
class CollatzTemporalRunQuotient:
    """Arithmetic run result; scheduler publication supplies source authority."""

    source: int
    physical_ticks: int
    endpoint: int
    odd_ticks: int
    division_ticks: int
    normalized_symbols: int
    phase: int
    run_actions: int
    zero_run_symbols: int
    one_run_symbols: int
    cycle_repetitions: int
    normalized_f5: CollatzF5AffineAction | None
    physical_f5: CollatzF5AffineAction | None
    root_certificate: CollatzRootFiberCertificate | None
    tape_width_summary: CollatzTapeWidthSummary | None = None

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (
                self.source,
                self.physical_ticks,
                self.endpoint,
                self.odd_ticks,
                self.division_ticks,
                self.normalized_symbols,
                self.phase,
                self.run_actions,
                self.zero_run_symbols,
                self.one_run_symbols,
                self.cycle_repetitions,
            )
        ):
            raise TypeError("Collatz temporal quotient fields require exact integers")
        if self.source <= 0 or self.endpoint <= 0 or self.physical_ticks < 0:
            raise ValueError("Collatz temporal quotient requires positive exact states")
        if self.phase not in (0, 1):
            raise ValueError("Collatz temporal phase must be zero or one")
        if self.odd_ticks + self.division_ticks != self.physical_ticks:
            raise ValueError("Collatz physical clock does not sum to requested ticks")
        if self.zero_run_symbols + self.one_run_symbols != self.normalized_symbols:
            raise ValueError("Collatz run symbols do not sum to normalized width")
        if (
            self.normalized_symbols != self.division_ticks
            or self.one_run_symbols + self.phase != self.odd_ticks
        ):
            raise ValueError("Collatz normalized clock lost its pending odd half-step")
        from number_compiler.sequences.collatz.temporal_run_quotient import (
            F5_AFFINE_ALPHABET,
        )

        if (
            self.normalized_f5 is not None
            and self.normalized_f5 not in F5_AFFINE_ALPHABET
        ):
            raise ValueError("Collatz temporal quotient has a foreign F5 action")
        if (
            self.physical_f5 is not None
            and self.physical_f5.apply(self.source) != self.endpoint % 5
        ):
            raise ValueError("Collatz F5 temporal action disagrees with endpoint")
        if self.tape_width_summary is not None:
            summary = self.tape_width_summary
            if type(summary) is not CollatzTapeWidthSummary or (
                summary.source_width != self.source.bit_length()
                or summary.target_width != self.endpoint.bit_length()
                or summary.physical_ticks != self.physical_ticks
                or summary.normalized_symbols != self.division_ticks
                or summary.odd_steps != self.odd_ticks
            ):
                raise ValueError("Collatz width summary is detached from its run")

    @property
    def semantic_key(self) -> tuple[object, ...]:
        """Exact result descriptor, excluding construction-work counters."""
        return (
            self.source,
            self.physical_ticks,
            self.endpoint,
            self.odd_ticks,
            self.division_ticks,
            self.normalized_symbols,
            self.phase,
            self.normalized_f5,
            self.physical_f5,
        )

    @property
    def width(self) -> int:
        return self.endpoint.bit_length()

    @property
    def description_bits(self) -> int:
        integers = (
            self.source,
            self.physical_ticks,
            self.endpoint,
            self.odd_ticks,
            self.division_ticks,
            self.normalized_symbols,
            self.phase,
            self.run_actions,
            self.zero_run_symbols,
            self.one_run_symbols,
            self.cycle_repetitions,
        )
        bits = sum(max(1, value.bit_length()) for value in integers)
        for action in (self.normalized_f5, self.physical_f5):
            if action is not None:
                bits += action.scale.bit_length() + max(1, action.offset.bit_length())
        if self.root_certificate is not None:
            bits += sum(
                max(1, value.bit_length())
                for value in (
                    self.root_certificate.depth,
                    self.root_certificate.support_size,
                    self.root_certificate.amplitude_square,
                    self.root_certificate.powered_symbols,
                )
            )
        return bits

    def radix_digit(self, radix: int, position: int) -> int:
        if type(radix) is not int or radix < 2:
            raise ValueError("radix must be at least two")
        if type(position) is not int or position < 0:
            raise IndexError(position)
        if position and position * (radix.bit_length() - 1) >= self.width:
            raise IndexError(position)
        place = int(radix**position)
        if place > self.endpoint and position:
            raise IndexError(position)
        return self.endpoint // place % radix


__all__ = ["CollatzTemporalRunQuotient"]
