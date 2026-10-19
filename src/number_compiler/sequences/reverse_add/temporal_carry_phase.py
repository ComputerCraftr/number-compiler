"""Composable source-issued reverse/add border/inner carry phase contracts.

A phase relates one known K-digit source tile to its certified K-digit target
through a low carry and a *correlated* symmetric middle transfer. A finite
word may be composed with the next issued word. Its repeat compression is
purely conditional: it never claims a new physical Q19 source or inlet.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING

from number_compiler.arithmetic.carry.carry_monoid import CarryFn

from .border_carry_safety import BilateralCyclePort, BorderTile
from .temporal_carry_wire import MiddleCarryWire

if TYPE_CHECKING:
    from .q19_border_control import CertifiedBorderGrowth
    from .temporal_ring_harmonics import ReverseAddTemporalRingBank


@dataclass(frozen=True, slots=True)
class CertifiedCarryPhase:
    """One certified border step and its exact remaining middle-map domain."""

    tick: int
    width: int
    port: BilateralCyclePort
    middle_wire: MiddleCarryWire

    def __post_init__(self) -> None:
        if (
            type(self.tick) is not int
            or self.tick < 0
            or type(self.width) is not int
            or self.width < 2 * self.port.source.k + 1
            or self.port.source.k != self.middle_wire.outer_pairs
            or self.width != self.middle_wire.source_width
            or not set(self.middle_wire.transfers).issubset(self.port.admitted_middle)
        ):
            raise ValueError("invalid source/target symmetric carry phase")
        from .border_carry_safety import border_bilateral_port

        for fn in self.middle_wire.transfers:
            alt = border_bilateral_port(self.port.source, (fn,)).alternatives[0]
            if alt.target != self.port.target or alt.growth != self.port.growth:
                raise ValueError("interior carry response contradicts border output")

    @property
    def low_carry(self) -> int:
        return self.port.low_carry

    @property
    def high_carries(self) -> tuple[int, ...]:
        return self.middle_wire.input_output(self.low_carry)

    @property
    def middle_transfers(self) -> tuple[CarryFn, ...]:
        return self.middle_wire.transfers

    @property
    def first_reset_positions(self) -> tuple[int, ...]:
        """Symmetric pair positions (from outside). -1 denotes all EQ."""
        return tuple(
            dict.fromkeys(
                position for position, _transfer in self.first_reset_witnesses
            )
        )

    @property
    def first_reset_witnesses(self) -> tuple[tuple[int, CarryFn], ...]:
        """Absolute pair coordinate and its correlated middle transfer.

        ``-1`` is the all-EQ identity seam. Nonnegative coordinates count
        from the LSD-side outer border into the middle.
        """
        return tuple(
            (
                -1 if index == -1 else self.port.source.k + index,
                transfer,
            )
            for index, transfer in self.middle_wire.reset_witnesses
        )

    @property
    def conditional_f5(self) -> tuple[tuple[int, ...], ...]:
        """All surviving mod-5 coefficient lifts, never a fabricated phase."""
        return tuple(
            tuple(sorted({s % 5 for s in domain}))
            for domain in self.middle_wire.pair_domains
        )


@dataclass(frozen=True, slots=True)
class CertifiedCarryWord:
    """Finite physical border/carry word issued from retained ring banks.

    The source-bank chain authenticates both the occurrence horizon and the
    exact phase objects.  A live border certificate alone is insufficient to
    issue an arbitrary locally consistent carry word.
    """

    certificate: CertifiedBorderGrowth
    start: int
    entry_width: int
    phases: tuple[CertifiedCarryPhase, ...]
    _source_banks: tuple[ReverseAddTemporalRingBank, ...] = field(
        repr=False, compare=False
    )

    def __post_init__(self) -> None:
        self.validate()

    def validate(self) -> None:
        """Recheck live issuance and exact coverage of the physical horizon."""
        from .temporal_ring_harmonics import ReverseAddTemporalRingBank

        self.certificate.validate(self.certificate.owner, self.certificate.source)
        if (
            type(self.start) is not int
            or self.start < 0
            or type(self.entry_width) is not int
            or self.entry_width < 3
            or type(self.phases) is not tuple
            or not self.phases
            or type(self._source_banks) is not tuple
            or not self._source_banks
            or any(type(phase) is not CertifiedCarryPhase for phase in self.phases)
        ):
            raise ValueError("cannot issue empty border carry word")

        border_digits = self.phases[0].port.source.k
        phase_index = 0
        bank_start = self.start
        for bank in self._source_banks:
            if type(bank) is not ReverseAddTemporalRingBank:
                raise ValueError("carry word source is not an issued ring bank")
            bank.validate()
            if bank.certificate is not self.certificate or bank.start != bank_start:
                raise ValueError("carry word source banks do not cover its horizon")
            if bank.positions != self._source_banks[0].positions:
                raise ValueError("carry word source bank identity changed")
            for offset, wire_phases in enumerate(bank.carry_wire_phases):
                exact = next(
                    (
                        phase
                        for phase in wire_phases
                        if phase.port.source.k == border_digits
                    ),
                    None,
                )
                if exact is None or phase_index >= len(self.phases):
                    raise ValueError("carry word phase is absent from its source bank")
                phase = self.phases[phase_index]
                if phase is not exact:
                    raise ValueError("carry word phase is not source-issued")
                if phase.tick != bank.start + offset:
                    raise ValueError("carry word phase lies outside its source horizon")
                phase_index += 1
            bank_start += bank.duration

        if phase_index != len(self.phases) or bank_start != self.start + len(
            self.phases
        ):
            raise ValueError("carry word source banks do not exactly cover its horizon")

        expected_width = self.entry_width
        for i, p in enumerate(self.phases):
            if p.tick != self.start + i:
                raise ValueError("nonconsecutive physical carry phases")
            if i and self.phases[i - 1].port.target != p.port.source:
                raise ValueError("border return/exit seam is not consecutive")
            if p.width != expected_width:
                raise ValueError("phase width mismatch")
            if p.port.source.k != self.phases[0].port.source.k:
                raise ValueError("border window changed within carry word")
            expected_width += p.port.growth

    @property
    def duration(self) -> int:
        return len(self.phases)

    @property
    def growth(self) -> int:
        return sum(p.port.growth for p in self.phases)

    @property
    def exit_width(self) -> int:
        return self.entry_width + self.growth

    @property
    def entry_border(self) -> BorderTile:
        return self.phases[0].port.source

    @property
    def exit_border(self) -> BorderTile:
        return self.phases[-1].port.target

    def then(self, later: CertifiedCarryWord) -> CertifiedCarryWord:
        self.validate()
        later.validate()
        if (
            self.certificate is not later.certificate
            or self.start + self.duration != later.start
            or self.exit_border != later.entry_border
            or self.exit_width != later.entry_width
        ):
            raise ValueError("not an authenticated adjacent carry word")
        return CertifiedCarryWord(
            self.certificate,
            self.start,
            self.entry_width,
            self.phases + later.phases,
            self._source_banks + later._source_banks,
        )

    def conditional_power(self, repetitions: int) -> ConditionalCarryRepeat:
        self.validate()
        if (
            type(repetitions) is not int
            or repetitions < 0
            or self.entry_border != self.exit_border
        ):
            raise ValueError("conditional power needs a closed border return")
        return ConditionalCarryRepeat(self, repetitions)


@dataclass(frozen=True, slots=True)
class ConditionalCarryRepeat:
    """O(1)-space formal phase repetition, NOT a physical repeat witness."""

    source_word: CertifiedCarryWord
    repetitions: int
    physical_repeat_certified: bool = False

    def __post_init__(self) -> None:
        self.source_word.validate()
        if (
            self.physical_repeat_certified
            or type(self.repetitions) is not int
            or self.repetitions < 0
            or self.source_word.entry_border != self.source_word.exit_border
        ):
            raise ValueError("only conditional border repetition is supported")

    @property
    def duration(self) -> int:
        return self.source_word.duration * self.repetitions

    @property
    def growth(self) -> int:
        return self.source_word.growth * self.repetitions

    def phase(self, tick: int) -> CertifiedCarryPhase:
        self.source_word.validate()
        if type(tick) is not int or not 0 <= tick < self.duration:
            raise IndexError("outside conditional repeated carry word")
        return self.source_word.phases[tick % self.source_word.duration]

    def phase_batch(self, ticks: tuple[int, ...]) -> tuple[CertifiedCarryPhase, ...]:
        """Read many conditional phases after one complete live-source check.

        The scalar API intentionally keeps validating the retained source
        chain on every call. A batch still authenticates that live chain, then
        checks every requested coordinate before returning any phase. A later
        batch validates again, so this does not cache authority across calls.
        """
        if type(ticks) is not tuple:
            raise TypeError("phase batch coordinates must be an exact tuple")
        self.source_word.validate()
        if len(ticks) > 1_000_000 or any(
            type(tick) is not int or not 0 <= tick < self.duration for tick in ticks
        ):
            raise IndexError("outside conditional repeated carry word")
        phases = self.source_word.phases
        period = len(phases)
        return tuple(phases[tick % period] for tick in ticks)

    def conditional_width(self) -> int:
        self.source_word.validate()
        return self.source_word.entry_width + self.growth


__all__ = ["CertifiedCarryPhase", "CertifiedCarryWord", "ConditionalCarryRepeat"]
