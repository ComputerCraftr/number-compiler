"""Reverse/add-specific harmonic actions for every conditional border cycle.

The homogeneous polynomial of a physical cycle with q nongrowth and g growth
steps is 2**q * (1+z)**g.  This module produces its exact F5/F2 harmonics,
its ordered source-bound carry-safety letters and a finite-horizon bridge to
the joint inward constraint engine.  It never imports 2rev10 phase periods.

The carry-cochain forcing is a separate *input* to the affine action.  A
border return does not establish that its future forcing packet repeats.
Neither these coefficients nor a finite border trace authorizes a full-root
reverse/add temporal REPEAT.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import comb
from typing import TYPE_CHECKING, cast

from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    apply_carry_fn,
)
from number_compiler.arithmetic.fields.decimal_pair_partition import (
    DECIMAL_PAIR_BANDS,
    DecimalPairBand,
    decimal_pair_band_members,
)
from number_compiler.arithmetic.polynomials.polynomial import f5_modes

from .border_carry_safety import (
    BilateralCyclePort,
    ConditionalBorderCycle,
    border_carry_port,
    conditional_return_from_trace,
    enumerate_one_digit_cycles,
)

if TYPE_CHECKING:
    from .q19_border_control import CertifiedBorderGrowth
    from .temporal_inward_constraints import ReverseInwardConstraints


def _lucas_binomial_mod5(n: int, k: int) -> int:
    """Binomial coefficient modulo five in O(log_5(n)), without a factorial."""
    if not 0 <= k <= n:
        return 0
    result = 1
    while n or k:
        nd, kd = n % 5, k % 5
        if kd > nd:
            return 0
        result = result * comb(nd, kd) % 5
        n //= 5
        k //= 5
    return result


@dataclass(frozen=True, slots=True)
class MacroCarrySafetyPhase:
    """Coupled leading/trailing carry requirements for one physical tick.

    The high carry is an OUTPUT of the middle carry function applied to the
    independently forced low carry.  A rise 0->1 needs a decisive GT reset;
    a fall 1->0 needs LT. Equality does not imply a reset, since EQ=9 can
    transmit the existing carry across the entire unknown middle.
    """

    tick: int
    source_outer: tuple[int, int]
    target_outer: tuple[int, int]
    growth: int
    low_carry: int
    high_carries: tuple[int, ...]
    admitted_middle: tuple[CarryFn, ...]
    forced_reset: str | None

    @property
    def forced_high_carry(self) -> int | None:
        return self.high_carries[0] if len(self.high_carries) == 1 else None

    @property
    def forced_birth(self) -> bool:
        return self.low_carry == 0 and self.high_carries == (1,)

    @property
    def forced_death(self) -> bool:
        return self.low_carry == 1 and self.high_carries == (0,)


def _safety_phase(tick: int, port: BilateralCyclePort) -> MacroCarrySafetyPhase:
    high = tuple(
        sorted({apply_carry_fn(fn, port.low_carry) for fn in port.admitted_middle})
    )
    if not high:
        raise ValueError("an empty carry-map phase cannot be compiled")
    reset = (
        "gt"
        if high == (1,) and port.low_carry == 0
        else "lt"
        if high == (0,) and port.low_carry == 1
        else None
    )
    return MacroCarrySafetyPhase(
        tick,
        (port.source.high, port.source.low),
        (port.target.high, port.target.low),
        port.growth,
        port.low_carry,
        high,
        port.admitted_middle,
        reset,
    )


@dataclass(frozen=True, slots=True)
class MacroWindowCarrySafety:
    """Source-certified K-digit safety cone, not a guessed K=1 projection.

    A K>1 window can force the carry immediately behind the leading digit
    even when the carry from the unknown middle into the HIGH K-window is
    still conditional. They are different physical carry boundaries.
    """

    tick: int
    source_high: int
    source_low: int
    target_high: int
    target_low: int
    window_digits: int
    low_window_carry: int
    possible_high_window_ingresses: tuple[int, ...]
    possible_leading_ingresses: tuple[int, ...]
    first_inner_non9: int | None
    admitted_middle: tuple[CarryFn, ...]

    @property
    def forced_leading_ingress(self) -> int | None:
        if len(self.possible_leading_ingresses) == 1:
            return self.possible_leading_ingresses[0]
        return None

    @property
    def forced_middle_reset(self) -> str | None:
        """A compulsory GT/LT reset of the complete unknown middle."""
        high = self.possible_high_window_ingresses
        if self.low_window_carry == 0 and high == (1,):
            return "gt"
        if self.low_window_carry == 1 and high == (0,):
            return "lt"
        return None


def _window_safety(tick: int, port: BilateralCyclePort) -> MacroWindowCarrySafety:
    local = border_carry_port(port.source)
    high_window = tuple(
        sorted({apply_carry_fn(fn, port.low_carry) for fn in port.admitted_middle})
    )
    leading: tuple[int, ...] = high_window
    if local.forced_msd_ingress is not None:
        leading = (local.forced_msd_ingress,)
    return MacroWindowCarrySafety(
        tick=tick,
        source_high=port.source.high,
        source_low=port.source.low,
        target_high=port.target.high,
        target_low=port.target.low,
        window_digits=port.source.k,
        low_window_carry=port.low_carry,
        possible_high_window_ingresses=high_window,
        possible_leading_ingresses=leading,
        first_inner_non9=local.first_inner_non9,
        admitted_middle=port.admitted_middle,
    )


@dataclass(frozen=True, slots=True)
class MacroPhaseInwardOrbit:
    """Forced/may output lanes at one inward position through a finite macro.

    A `None` bit is an unresolved lane, not a zero. F5 temporal evaluations
    are issued only for singleton lanes; no 2rev10 periods are imported.
    The two reflected incoming carries are calculated from the SAME
    Q19 pair coefficient; their possible birth/death events are recorded.
    """

    position: int
    pair_f5: tuple[tuple[int, ...], ...]
    low_carries: tuple[tuple[int, ...], ...]
    reflected_carries: tuple[tuple[int, ...], ...]
    reflected_xor: tuple[tuple[int, ...], ...]
    raw_innovation_borrow: tuple[tuple[int, ...], ...]
    carry_borrow_xor: tuple[tuple[int, ...], ...]
    low_birth: tuple[tuple[int, ...], ...]
    low_death: tuple[tuple[int, ...], ...]
    reflected_birth: tuple[tuple[int, ...], ...]
    reflected_death: tuple[tuple[int, ...], ...]
    selected_bands: tuple[tuple[DecimalPairBand, ...], ...]
    complete_future_period_certified: bool = False

    def has_duration(self, duration: int) -> bool:
        """Check every retained output channel against one finite horizon."""
        return all(
            type(values) is tuple and len(values) == duration
            for values in (
                self.pair_f5,
                self.low_carries,
                self.reflected_carries,
                self.reflected_xor,
                self.raw_innovation_borrow,
                self.carry_borrow_xor,
                self.low_birth,
                self.low_death,
                self.reflected_birth,
                self.reflected_death,
                self.selected_bands,
            )
        )

    @property
    def retained_output_nodes(self) -> int:
        """Count outer and row slots for each retained projected output."""
        return sum(
            len(values) + sum(len(row) for row in values)
            for values in (
                self.pair_f5,
                self.low_carries,
                self.reflected_carries,
                self.reflected_xor,
                self.raw_innovation_borrow,
                self.carry_borrow_xor,
                self.low_birth,
                self.low_death,
                self.reflected_birth,
                self.reflected_death,
                self.selected_bands,
            )
        )


def inward_orbit_at(
    system: ReverseInwardConstraints, start: int, duration: int, position: int
) -> MacroPhaseInwardOrbit:
    """Conservative correlated carry responses at an inward position.

    Enumerating pair coefficients and their two incoming carry ports is a
    *superset* of globally admissible sources. It is safe for deciding
    singleton (forced) outputs and cannot invent a carry branch or orbit.
    """
    residues: list[tuple[int, ...]] = []
    lows: list[tuple[int, ...]] = []
    highs: list[tuple[int, ...]] = []
    xors: list[tuple[int, ...]] = []
    borrows: list[tuple[int, ...]] = []
    joint_xors: list[tuple[int, ...]] = []
    lb: list[tuple[int, ...]] = []
    ld: list[tuple[int, ...]] = []
    hb: list[tuple[int, ...]] = []
    hd: list[tuple[int, ...]] = []
    bands: list[tuple[DecimalPairBand, ...]] = []
    for t in system.admitted_temporal_span(start, duration):
        w = system.widths[t]
        if not 0 <= position < (w + 1) // 2:
            raise ValueError("inward position crosses center or terminal row")
        loc = position
        reflected = w - 1 - position
        coeffs = system.pair_domain(t, position)
        ca = system.carry_domain(t, loc)
        cr = system.carry_domain(t, reflected)
        allowed_low_out = set(system.carry_domain(t, loc + 1))
        allowed_high_out = set(system.carry_domain(t, reflected + 1))
        possibilities: set[tuple[int, int, int, int, int]] = set()
        for s in coeffs:
            for a in ca:
                for b in cr:
                    carry_a = 1 if s > 9 else a if s == 9 else 0
                    carry_b = 1 if s > 9 else b if s == 9 else 0
                    if carry_a in allowed_low_out and carry_b in allowed_high_out:
                        possibilities.add((s, a, b, carry_a, carry_b))
        if not possibilities:
            raise ValueError("inward pair contradicts carry response")
        residues.append(tuple(sorted({v[0] % 5 for v in possibilities})))
        lows.append(tuple(sorted({v[1] for v in possibilities})))
        highs.append(tuple(sorted({v[2] for v in possibilities})))
        xors.append(tuple(sorted({v[1] ^ v[2] for v in possibilities})))
        borrows.append(system.raw_borrow_domain(t, position))
        joint_xors.append(system.carry_borrow_xor_domain(t, position))
        lb.append(tuple(sorted({int(v[1] == 0 and v[3] == 1) for v in possibilities})))
        ld.append(tuple(sorted({int(v[1] == 1 and v[3] == 0) for v in possibilities})))
        hb.append(tuple(sorted({int(v[2] == 0 and v[4] == 1) for v in possibilities})))
        hd.append(tuple(sorted({int(v[2] == 1 and v[4] == 0) for v in possibilities})))
        bands.append(
            tuple(
                band
                for band in DECIMAL_PAIR_BANDS
                if any(
                    value[0] in decimal_pair_band_members(band)
                    for value in possibilities
                )
            )
        )
    return MacroPhaseInwardOrbit(
        position,
        tuple(residues),
        tuple(lows),
        tuple(highs),
        tuple(xors),
        tuple(borrows),
        tuple(joint_xors),
        tuple(lb),
        tuple(ld),
        tuple(hb),
        tuple(hd),
        tuple(bands),
    )


@dataclass(frozen=True, slots=True)
class CycleHarmonicAction:
    """A conditional cycle, with exact source-independent *linear* harmonics.

    ``ports`` is an ordered list of demanded middle carry-transfer actions.
    It is *not* a table of future Q19 sources.  A fixed list of carry functions
    is not thereby asserted to describe an arbitrary source at future ticks.
    """

    cycle: ConditionalBorderCycle
    ports: tuple[BilateralCyclePort, ...]
    future_source_certified: bool = False
    complete_integer_certified: bool = False

    def __post_init__(self) -> None:
        if (
            type(self.cycle) is not ConditionalBorderCycle
            or self.ports != self.cycle.bilateral_ports()
            or self.future_source_certified is not False
            or self.complete_integer_certified is not False
        ):
            raise ValueError("macro harmonics require exact conditional cycle ports")
        # Universal run bounds apply cyclically, including the return seam.
        word = "".join(map(str, self.cycle.growth))
        if "00000" in word * 2 or "1111" in word * 2:
            raise ValueError("impossible reverse/add border growth language")

    @classmethod
    def from_cycle(cls, cycle: ConditionalBorderCycle) -> CycleHarmonicAction:
        return cls(cycle=cycle, ports=cycle.bilateral_ports())

    def rotated_to_entry(self, pair: tuple[int, int]) -> CycleHarmonicAction:
        """Rephase a catalogue cycle to an actual authenticated border entry.

        Cycle census entries are canonically rotated; physical orbit entry
        need not be. The carry requirements and ordered skew weights rotate
        together, not merely the digit label or total growth count.
        """
        if pair not in self.cycle.states:
            raise ValueError("border pair not present in this candidate cycle")
        offset = self.cycle.states.index(pair)
        if offset == 0:
            return self
        cycle = self.cycle
        return CycleHarmonicAction.from_cycle(
            ConditionalBorderCycle(
                states=cycle.states[offset:] + cycle.states[:offset],
                incoming=cycle.incoming[offset:] + cycle.incoming[:offset],
                growth=cycle.growth[offset:] + cycle.growth[:offset],
                simple=cycle.simple,
            )
        )

    @property
    def duration(self) -> int:
        return self.cycle.steps

    @property
    def growth(self) -> int:
        return self.cycle.width_growth

    @property
    def quiet(self) -> int:
        return self.duration - self.growth

    def carry_safety_phases(self) -> tuple[MacroCarrySafetyPhase, ...]:
        """All cycle phases, including both ends' *forced* carry births.

        This is calculated from reverse/add's K=1 bilateral addition,
        not from a copied 2rev10 boundary period. Unknown future middle
        transfer programs stay labelled as alternatives.
        """
        return tuple(_safety_phase(t, port) for t, port in enumerate(self.ports))

    def phase_growth(self, tick: int) -> int:
        if type(tick) is not int or tick < 0:
            raise ValueError("temporal phase must be nonnegative")
        return self.cycle.growth[tick % self.duration]

    def phase_port(self, tick: int) -> BilateralCyclePort:
        if type(tick) is not int or tick < 0:
            raise ValueError("temporal phase must be nonnegative")
        return self.ports[tick % self.duration]

    def prefix_counts(self, ticks: int) -> tuple[int, int]:
        """(quiet, growth) for a *conditional* phase program of any length."""
        if type(ticks) is not int or ticks < 0:
            raise ValueError("invalid time extent")
        periods, tail = divmod(ticks, self.duration)
        growth = periods * self.growth + sum(self.cycle.growth[:tail])
        return ticks - growth, growth

    def homogeneous_coefficient_mod5(self, position: int, *, repeats: int = 1) -> int:
        """[z^position] 2^(q*k)(1+z)^(g*k) mod5 via Lucas digits.

        ``repeats`` is an algebraic conditional input, not a source license.
        """
        if type(position) is not int or type(repeats) is not int or repeats < 0:
            raise ValueError("invalid inward coordinate or repeat count")
        return (
            pow(2, self.quiet * repeats, 5)
            * _lucas_binomial_mod5(self.growth * repeats, position)
        ) % 5

    def homogeneous_mode_mod5(self, z: int, *, repeats: int = 1) -> int:
        """Exact F5 multiplier at any of four finite-field spatial modes."""
        if type(z) is not int or type(repeats) is not int or repeats < 0:
            raise ValueError("invalid evaluation mode or repeat count")
        if z % 5 not in (1, 2, 3, 4):
            raise ValueError("choose one of the four nonzero F5 modes")
        return (
            pow(2, self.quiet * repeats, 5) * pow((1 + z) % 5, self.growth * repeats, 5)
        ) % 5

    def phase_modes_mod5(self) -> tuple[tuple[int, int, int, int], ...]:
        """Ordered prefix harmonics, including the identity at phase zero."""
        values: list[tuple[int, int, int, int]] = []
        for t in range(self.duration + 1):
            quiet, growth = self.prefix_counts(t)
            modes = tuple(
                pow(2, quiet, 5) * pow((1 + z) % 5, growth, 5) % 5 for z in (1, 2, 3, 4)
            )
            values.append((modes[0], modes[1], modes[2], modes[3]))
        return tuple(values)

    def conditional_cochain_at_mod5(
        self, z: int, initial: int, forcing: tuple[int, ...]
    ) -> int:
        """Evaluate one complete macro with externally supplied carry cochains.

        Forcing[j] is the F5 evaluation of the *actual* correction polynomial
        F_j(z) at that tick.  The method performs no future source inference.
        Different forcing histories remain different even for equal borders.
        """
        if type(z) is not int or not 0 <= z < 5:
            raise ValueError("evaluation in F5 required")
        if (
            type(initial) is not int
            or type(forcing) is not tuple
            or len(forcing) != self.duration
            or any(type(f) is not int for f in forcing)
        ):
            raise ValueError("one carry-cochain value per physical tick required")
        value = initial % 5
        for growth, correction in zip(self.cycle.growth, forcing, strict=True):
            multiplier = (1 + z) % 5 if growth else 2
            value = (multiplier * value + correction) % 5
        return value

    def cochain_weights_mod5(self, z: int) -> tuple[int, ...]:
        """Weights of the distinct future F5 carry cochains at every tick.

        At z=-1, each growth is a ZERO multiplier. All forcing packets
        before the last growth are punctured, as is the initial pair word.
        This holds for all 96 cycles, irrespective of the future middle map.
        """
        if type(z) is not int or not 0 <= z < 5:
            raise ValueError("F5 evaluation point must be 0..4")
        multiplier = 1
        weights = [0] * self.duration
        for i in range(self.duration - 1, -1, -1):
            weights[i] = multiplier
            multiplier = multiplier * (1 + z if self.cycle.growth[i] else 2) % 5
        return tuple(weights)

    def evaluate_punctured_cochain_mod5(
        self,
        z: int,
        *,
        initial: int | None,
        forcing: tuple[int | None, ...],
    ) -> int | None:
        """Project a conditional macro, ignoring only *proved* zero weights.

        Unknown nonzero-weight inputs keep the result unknown. For a growing
        cycle at z=4, ``initial`` and all corrections before the final growth
        may remain unknown without affecting the exact result.
        """
        if type(forcing) is not tuple or len(forcing) != self.duration:
            raise ValueError("one conditional forcing port per phase required")
        weights = self.cochain_weights_mod5(z)
        homogeneous = (pow(2, self.quiet, 5) * pow(1 + z, self.growth, 5)) % 5
        if homogeneous and initial is None:
            return None
        result = (homogeneous * (initial or 0)) % 5
        for weight, value in zip(weights, forcing, strict=True):
            if not weight:
                continue
            if type(value) is not int:
                return None
            result = (result + weight * value) % 5
        return result

    def conditional_temporal_walsh64_growth(self) -> tuple[int, ...]:
        """Walsh64/F5 of the 64 phase-indexed growth bits, NOT GT masks."""
        from number_compiler.arithmetic.fields.walsh import walsh64_mod5

        mask = sum(self.phase_growth(i) << i for i in range(64))
        return walsh64_mod5(mask)

    def manifest(self) -> dict[str, object]:
        """A small complete harmonic/carry record, with no extrapolation claim."""
        return {
            "border_states": self.cycle.states,
            "growth_word": "".join(map(str, self.cycle.growth)),
            "required_high_carries": self.cycle.incoming,
            "low_carries": tuple(port.low_carry for port in self.ports),
            "admitted_high_carries": tuple(
                phase.high_carries for phase in self.carry_safety_phases()
            ),
            "forced_middle_reset": tuple(
                phase.forced_reset for phase in self.carry_safety_phases()
            ),
            "allowed_middle_maps": tuple(
                tuple(fn.name for fn in port.admitted_middle) for port in self.ports
            ),
            "quiet": self.quiet,
            "growth": self.growth,
            "skew": self.cycle.skew_moment,
            "f5_mode_multipliers": self.phase_modes_mod5()[-1],
            "f5_minus_one_punctured_before": max(
                j for j, bit in enumerate(self.cycle.growth) if bit
            ),
            "future_source_certified": False,
        }


def all_reverse_add_macro_harmonics() -> tuple[CycleHarmonicAction, ...]:
    """Exhaustive 26-state/96-cycle conditional radix-19 border catalogue."""
    return tuple(
        CycleHarmonicAction.from_cycle(c) for c in enumerate_one_digit_cycles()
    )


@dataclass(frozen=True, slots=True)
class PhaseBankHarmonic:
    """Actual finite macro-phase mask with unknown lanes kept conditional."""

    position: int
    channel: DecimalPairBand
    selected: tuple[int | None, ...]
    f5_modes: tuple[int, int, int, int] | None
    future_period_certified: bool = False

    @property
    def forced_phases(self) -> int:
        return sum(bit is not None for bit in self.selected)


@dataclass(frozen=True, slots=True)
class AuthenticatedMacroWindow:
    """One *finite*, source-issued macro return plus coupled inward constraints.

    No source authority is promoted to times beyond the certified horizon.
    A border return may change the Q19 middle action at the next iteration.
    """

    certificate: CertifiedBorderGrowth
    start: int
    action: CycleHarmonicAction

    def validate(self) -> None:
        """Recheck the certificate-bound cycle before reading its phases."""
        cert = self.certificate
        cert.validate(cert.owner, cert.source)
        end = self.start + self.action.duration
        if (
            self.start < 0
            or end > len(cert.growth_word)
            or not cert.outer_pairs
            or end >= len(cert.outer_pairs)
            or any(p is None for p in cert.outer_pairs[self.start : end + 1])
        ):
            raise ValueError("finite border macro is not fully source certified")
        pairs = cert.outer_pairs[self.start : end + 1]
        if (
            pairs[0] != pairs[-1]
            or tuple(pairs[:-1]) != self.action.cycle.states
            or cert.growth_word[self.start : end] != self.action.cycle.growth
        ):
            raise ValueError("certificate does not contain this macro return")

    def phase_window_safety(self) -> tuple[MacroWindowCarrySafety | None, ...]:
        """Join the live full-K border certificate with every macro phase.

        The one-digit cycle is always retained, but a K>=2 tile may prove
        an MSD carry reset hidden from the coarse one-digit state. Unknown
        K-window phases remain None: they are not silently replaced by
        a guessed full-K period.
        """
        self.validate()
        ports = self.certificate.bilateral_window_ports()
        results: list[MacroWindowCarrySafety | None] = []
        for j in range(self.action.duration):
            port = ports[self.start + j] if ports else None
            results.append(
                None if port is None else _window_safety(self.start + j, port)
            )
        return tuple(results)

    def phase_inward_carry_orbits(
        self,
        *,
        positions: tuple[int, ...],
        max_cells: int = 16384,
        source_pair_prefix: int = 0,
        include_source_digits: bool = False,
    ) -> tuple[MacroPhaseInwardOrbit, ...]:
        """Propagate TWO-SIDED phase carry birth/death constraints inward.

        The live source may supply a small demanded Q19 coefficient prefix.
        Phase outputs use the complete five-band/F5 and reflected-port
        relation. No time-period hypothesis is inserted as a premise.
        """
        if (
            type(positions) is not tuple
            or not positions
            or any(type(i) is not int or i < 0 for i in positions)
        ):
            raise ValueError("explicit nonnegative inward positions required")
        system = self.constrain_inward(
            max_cells=max_cells,
            include_source_digits=include_source_digits,
            source_pair_prefix=source_pair_prefix,
        )
        system.propagate()
        skip = int(self.certificate.source is not self.certificate.owner.initial)
        return tuple(
            inward_orbit_at(system, self.start - skip, self.action.duration, position)
            for position in positions
        )

    def phase_bank_harmonics(
        self,
        *,
        positions: tuple[int, ...],
        channel: DecimalPairBand,
        max_cells: int = 16384,
        include_source_digits: bool = False,
        include_source_pairs: bool = False,
    ) -> tuple[PhaseBankHarmonic, ...]:
        """Propagate then select per-position phase masks from one live macro.

        F5 modes evaluate the finite mask polynomial sum_t b_t z^t.
        They are *not* evidence of an infinite temporal period. The modes
        remain unknown if even one phase has an unresolved five-band mask.
        """
        if (
            type(channel) is not DecimalPairBand
            or type(positions) is not tuple
            or not positions
            or any(type(i) is not int or i < 0 for i in positions)
        ):
            raise ValueError("explicit inward coordinate tuple required")
        system = self.constrain_inward(
            max_cells=max_cells,
            include_source_digits=include_source_digits,
            include_source_pairs=include_source_pairs,
        )
        system.propagate()
        results: list[PhaseBankHarmonic] = []
        for position in positions:
            skip = int(self.certificate.source is not self.certificate.owner.initial)
            selected = tuple(
                system.bank_mask_domain(t, position, 1, channel)[0]
                for t in range(
                    self.start - skip, self.start - skip + self.action.duration
                )
            )
            modes = f5_modes(selected)
            results.append(
                PhaseBankHarmonic(
                    position,
                    channel,
                    selected,
                    modes,
                )
            )
        return tuple(results)

    def constrain_inward(
        self,
        *,
        max_cells: int = 16384,
        include_source_pairs: bool = False,
        include_source_digits: bool = False,
        source_pair_prefix: int = 0,
    ) -> ReverseInwardConstraints:
        """Join macro phase/carry ports to the issuer's existing time solver.

        Complete finite border tiles and modular residues are included from
        the *same* live certificate.  No observed masks/2rev10 periods are
        imported as premises.  Call ``propagate`` to find forced bank masks.
        """
        self.validate()
        system = self.certificate.inward_temporal_constraints(
            max_cells=max_cells,
            include_source_pairs=include_source_pairs,
            include_source_digits=include_source_digits,
            source_pair_prefix=source_pair_prefix,
        )
        skip = int(self.certificate.source is not self.certificate.owner.initial)
        if self.start < skip:
            raise ValueError("macro starts before the later issued Q19 source")
        system.constrain_macro_cycle(self.action.cycle, start=self.start - skip)
        return system


def authorize_finite_macro_window(
    certificate: CertifiedBorderGrowth,
    *,
    start: int = 0,
    duration: int | None = None,
) -> AuthenticatedMacroWindow:
    """Extract a genuine border return inside a live certificate, not a power."""
    certificate.validate(certificate.owner, certificate.source)
    if type(start) is not int or start < 0:
        raise ValueError("invalid macro start")
    stop = len(certificate.growth_word) if duration is None else start + duration
    if (
        stop <= start
        or stop > len(certificate.growth_word)
        or not certificate.outer_pairs
        or stop >= len(certificate.outer_pairs)
    ):
        raise ValueError("macro exceeds the authenticated finite horizon")
    pairs = certificate.outer_pairs[start : stop + 1]
    if any(p is None for p in pairs):
        raise ValueError("certified border macro has unresolved outer cells")
    exact_pairs = cast(tuple[tuple[int, int], ...], pairs)
    cycle = conditional_return_from_trace(
        exact_pairs, certificate.growth_word[start:stop]
    )
    window = AuthenticatedMacroWindow(
        certificate, start, CycleHarmonicAction.from_cycle(cycle)
    )
    window.validate()
    return window


__all__ = [
    "AuthenticatedMacroWindow",
    "CycleHarmonicAction",
    "MacroCarrySafetyPhase",
    "MacroPhaseInwardOrbit",
    "inward_orbit_at",
    "MacroWindowCarrySafety",
    "PhaseBankHarmonic",
    "all_reverse_add_macro_harmonics",
    "authorize_finite_macro_window",
]
