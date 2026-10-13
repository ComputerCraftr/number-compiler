"""Validated result record for a source-bound physical Collatz run."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.sequences.collatz.tape_width import CollatzTapeWidthSummary

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.boundary_macros import (
        CollatzBoundaryMacro,
    )
    from number_compiler.sequences.collatz.joint_temporal_action import (
        CollatzAccumulatorObservation,
        CollatzJointRunAction,
    )
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
    joint_action: CollatzJointRunAction | None = None
    first_boundary: tuple[int, int, int, str] | None = None
    first_boundary_macro: CollatzBoundaryMacro | None = None

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
        if self.joint_action is not None:
            from number_compiler.sequences.collatz.joint_temporal_action import (
                CollatzJointRunAction,
            )

            action = self.joint_action
            if type(action) is not CollatzJointRunAction or (
                action.source != self.source
                or action.endpoint != self.endpoint
                or action.physical_ticks != self.physical_ticks
                or action.normalized_steps != self.division_ticks
                or action.odd_symbols != self.one_run_symbols
                or action.phase != self.phase
            ):
                raise ValueError("Collatz joint action is detached from its run")
        if (self.first_boundary is None) != (self.first_boundary_macro is None):
            raise ValueError("Collatz boundary witness and action must be paired")
        if self.first_boundary is not None:
            witness = self.first_boundary
            if (
                type(witness) is not tuple
                or len(witness) != 4
                or any(type(value) is not int for value in witness[:3])
                or type(witness[3]) is not str
                or witness[0] < 0
                or witness[1] <= 0
                or witness[2] <= 0
                or witness[0] + witness[2] > self.physical_ticks
            ):
                raise ValueError("Collatz first boundary witness is malformed")
        if self.first_boundary_macro is not None:
            from number_compiler.sequences.collatz.boundary_macros import (
                validate_boundary_macro,
            )

            macro = self.first_boundary_macro
            validate_boundary_macro(macro)
            if self.first_boundary is None or (
                self.first_boundary[1] != macro.source
                or self.first_boundary[2] != macro.physical_ticks
                or self.first_boundary[3] != macro.family
            ):
                raise ValueError("Collatz first boundary action is detached")

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
        if self.joint_action is not None:
            fields = self.joint_action.fields
            bits += sum(
                max(1, value.bit_length())
                for value in (
                    fields.gain,
                    fields.offset,
                    fields.sum_gain,
                    fields.sum_offset,
                    fields.previous_gain,
                    fields.previous_offset,
                )
            )
        if self.first_boundary_macro is not None:
            macro = self.first_boundary_macro
            bits += sum(
                max(1, value.bit_length())
                for value in (
                    macro.source,
                    macro.repetitions,
                    macro.maximum_repetitions,
                    macro.physical_ticks,
                    macro.odd_symbols,
                    macro.endpoint,
                    macro.fields.gain,
                    macro.fields.offset,
                    macro.fields.sum_gain,
                    macro.fields.sum_offset,
                )
            )
        return bits

    def accumulator(self, modulus: int) -> CollatzAccumulatorObservation:
        """Demand the authenticated source-plus-normalized-successor residue."""
        if self.joint_action is None:
            raise ValueError(
                "joint Collatz cocycle was not requested before construction"
            )
        return self.joint_action.accumulator_observation(modulus)

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
