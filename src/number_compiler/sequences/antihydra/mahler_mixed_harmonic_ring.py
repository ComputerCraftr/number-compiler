"""Source-guarded mixed-exponent Mahler odd-event macros and q carry harmonics.

The certified word is 1 0**(a_0-1) ... 1 0**(a_m-1).  Repeating this
*known* word needs an exact 2-adic cylinder; matching residues, Walsh spectra,
or a detected finite q orbit never authorizes a new source exponent.

The q transport is closed for EVERY integer radix: for n'=n+a,
    q' = 3**a*q + 2**n',  (2**n)'=2**(n+a).
It contains no invalid inverse of 2 at even-radix boundaries.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.two_adic import v2_nonzero, v2_positive
from number_compiler.arithmetic.fields.walsh import walsh64_mod5
from number_compiler.arithmetic.functions.finite_observer import (
    minimize_finite_orbit,
)
from number_compiler.sequences.antihydra.mahler_harmonic_ring import (
    _affine_pow,
    _orbit_at,
    _phase_histogram,
    _validate_harmonic_state_budget,
    _xor_f5_projection,
)
from number_compiler.sequences.antihydra.mahler_odd_macro import MahlerOddToOddAction
from number_compiler.sequences.antihydra.mahler_odd_source_transfer import (
    _OddEventExtentExceedsBudget,
    summarize_mahler_odd_event,
)
from number_compiler.sequences.antihydra.mahler_source_actions import (
    MAX_MAHLER_SOURCE_EXTENT,
)


def _compiled_motif(exponents: tuple[int, ...]) -> MahlerOddToOddAction:
    if (
        type(exponents) is not tuple
        or not 1 <= len(exponents) <= 8
        or any(type(a) is not int or a < 1 for a in exponents)
    ):
        raise ValueError("a mixed odd-event motif must contain 1..8 positive exponents")
    if sum(exponents) > MAX_MAHLER_SOURCE_EXTENT:
        raise BlockContextBudgetExceeded(
            "mixed odd-event motif exceeds the source-width budget"
        )
    action = MahlerOddToOddAction.identity()
    for a in exponents:
        action = action.then(MahlerOddToOddAction.run(a))
    return action


def _source_repetition_certificate(
    source: int, exponents: tuple[int, ...], action: MahlerOddToOddAction
) -> tuple[int, int]:
    """Validate an internally compiled motif and return its defect/capacity."""
    if type(source) is not int or source <= 0 or source % 2 != 1:
        raise ValueError("mixed odd-event source must be positive and odd")
    if source.bit_length() > 65_536:
        raise BlockContextBudgetExceeded("mixed odd-event source exceeds bit budget")
    if (
        type(exponents) is not tuple
        or not 1 <= len(exponents) <= 8
        or any(type(exponent) is not int or exponent < 1 for exponent in exponents)
    ):
        raise ValueError("a mixed odd-event motif must contain 1..8 positive exponents")
    if type(action) is not MahlerOddToOddAction:
        raise TypeError("a mixed ring needs a typed source-issued motif action")
    if action.odd_events != len(exponents) or action.extent != sum(exponents):
        raise ArithmeticError("compiled mixed action does not match its exponent word")
    if not action.integer_admits(source):
        raise ValueError("specified odd-run motif is not an admitted source cylinder")
    coefficient = (1 << action.extent) - action.joint.gain
    defect = coefficient * source - action.joint.innovation
    if defect == 0:
        raise ArithmeticError(
            "positive odd Mahler source has a zero fixed-point defect"
        )
    capacity = max(0, (v2_nonzero(defect) - 1) // action.extent)
    return defect, capacity


def _discover_prefix_actions(
    source: int, *, max_events: int, max_extent: int
) -> tuple[tuple[tuple[int, ...], MahlerOddToOddAction], ...]:
    """Return admitted source prefixes and their already-composed actions."""
    if type(source) is not int or source <= 0 or source % 2 != 1:
        raise ValueError("mixed discovery requires a positive odd source")
    if type(max_events) is not int or not 1 <= max_events <= 8:
        raise ValueError("motif discovery budget must be in 1..8 events")
    if type(max_extent) is not int or not 1 <= max_extent <= MAX_MAHLER_SOURCE_EXTENT:
        raise ValueError("motif discovery extent is outside the supported bound")
    if source.bit_length() > 65_536:
        raise BlockContextBudgetExceeded("mixed odd-event source exceeds bit budget")
    current = source
    exponents: list[int] = []
    action = MahlerOddToOddAction.identity()
    prefixes: list[tuple[tuple[int, ...], MahlerOddToOddAction]] = []
    extent = 0
    for _ in range(max_events):
        if extent >= max_extent:
            break
        try:
            event = summarize_mahler_odd_event(
                current,
                max_extent=max_extent - extent,
            )
        except _OddEventExtentExceedsBudget:
            break
        exponent = event.exponent
        extent += exponent
        exponents.append(exponent)
        action = action.then(MahlerOddToOddAction.run(exponent))
        prefixes.append((tuple(exponents), action))
        current = event.endpoint
        if current <= 0 or current & 1 == 0:
            raise ArithmeticError("discovered source lost its odd-return boundary")
    return tuple(prefixes)


@dataclass(frozen=True, slots=True)
class MahlerMixedQHarmonicSpectrum:
    radix: int
    places: int
    repetitions: int
    odd_events: int
    prefix_length: int
    period: int
    future_moore_classes: int | None
    carry_phase_counts: tuple[tuple[int, ...], ...]
    borrow_phase_counts: tuple[tuple[int, ...], ...]
    xor_phase_counts: tuple[tuple[int, ...], ...]
    walsh64_xor: tuple[tuple[int, ...], ...] | None

    @property
    def xor_f5(self) -> tuple[int, ...]:
        return _xor_f5_projection(self.xor_phase_counts, self.places)


@dataclass(frozen=True, slots=True)
class MahlerMixedOddHarmonicRing:
    """One exact source-certified motif with a reusable Hensel repeat guard."""

    source: int
    exponents: tuple[int, ...]
    action: MahlerOddToOddAction
    defect: int
    capacity: int

    def __post_init__(self) -> None:
        # A directly constructed or dataclasses.replace()'d ring must never
        # promote a guessed harmonic period to a real source certificate.
        if type(self.source) is not int or self.source <= 0 or not self.source & 1:
            raise ValueError("mixed harmonic owner requires a positive odd source")
        if (
            type(self.exponents) is not tuple
            or type(self.action) is not MahlerOddToOddAction
        ):
            raise TypeError("a mixed ring needs a typed source-issued motif action")
        if self.action.semantic_id != _compiled_motif(self.exponents).semantic_id:
            raise ValueError(
                "mixed ring action is not the authenticated parity program"
            )
        if type(self.defect) is not int or type(self.capacity) is not int:
            raise TypeError("2-adic defect and repetition count must be exact integers")
        expected, capacity = _source_repetition_certificate(
            self.source, self.exponents, self.action
        )
        if self.defect != expected:
            raise ValueError("mixed ring defect is detached from its source")
        if self.capacity != capacity:
            raise ValueError(
                "mixed ring repeat capacity is not a source-cylinder proof"
            )

    @classmethod
    def _issue_from_action(
        cls,
        source: int,
        exponents: tuple[int, ...],
        action: MahlerOddToOddAction,
    ) -> MahlerMixedOddHarmonicRing:
        """Publish a trusted, already-composed action without rebuilding it.

        This is private to the source compiler. Direct construction still
        re-derives and checks the action in ``__post_init__``.
        """
        defect, capacity = _source_repetition_certificate(source, exponents, action)
        result = object.__new__(cls)
        object.__setattr__(result, "source", source)
        object.__setattr__(result, "exponents", exponents)
        object.__setattr__(result, "action", action)
        object.__setattr__(result, "defect", defect)
        object.__setattr__(result, "capacity", capacity)
        return result

    @classmethod
    def from_source(
        cls, source: int, exponents: tuple[int, ...]
    ) -> MahlerMixedOddHarmonicRing:
        if type(exponents) is not tuple:
            raise TypeError("authenticated motif exponents must be a tuple")
        action = _compiled_motif(exponents)
        ring = cls._issue_from_action(source, exponents, action)
        if ring.capacity < 1:
            raise ArithmeticError(
                "issued odd-to-odd motif lacks its first repeat cylinder"
            )
        return ring

    @classmethod
    def discover(
        cls, source: int, *, max_events: int = 4, max_extent: int = 4096
    ) -> MahlerMixedOddHarmonicRing:
        """Discover at most a small witnessed motif, never predict further bits."""
        prefixes = _discover_prefix_actions(
            source, max_events=max_events, max_extent=max_extent
        )
        if not prefixes:
            raise BlockContextBudgetExceeded(
                "mixed odd-event discovery has no event within its extent budget"
            )
        exponents, action = prefixes[-1]
        ring = cls._issue_from_action(source, exponents, action)
        if ring.capacity < 1:
            raise ArithmeticError(
                "discovered odd-event word lacks its first repeat cylinder"
            )
        return ring

    @classmethod
    def best_repeating(
        cls, source: int, *, max_events: int = 4, min_copies: int = 2
    ) -> MahlerMixedOddHarmonicRing | None:
        """Choose the greatest *source-certified* periodic prefix, if one exists."""
        if type(min_copies) is not int or min_copies < 2:
            raise ValueError("a repeated motif must contain at least two copies")
        prefixes = _discover_prefix_actions(
            source,
            max_events=max_events,
            max_extent=MAX_MAHLER_SOURCE_EXTENT,
        )
        best: MahlerMixedOddHarmonicRing | None = None
        for exponents, action in prefixes:
            ring = cls._issue_from_action(source, exponents, action)
            if ring.capacity >= min_copies and (
                best is None
                or ring.capacity * len(exponents) > best.capacity * len(best.exponents)
            ):
                best = ring
        return best

    @property
    def extent(self) -> int:
        return self.action.extent

    @property
    def multiplier(self) -> int:
        return self.action.joint.gain

    @property
    def offset(self) -> int:
        return self.action.joint.innovation

    @property
    def k(self) -> int:
        return (1 << self.extent) - self.multiplier

    def admits(self, repetitions: int) -> bool:
        return type(repetitions) is int and 0 <= repetitions <= self.capacity

    def ledger_safe_copies(self, balance: int, maximum: int) -> int:
        """Return the largest complete-motif prefix safe at every event.

        This is only the integer Antihydra ledger condition. The separate
        source-cylinder cap and fractional Mahler guard are preserved.
        """
        if type(balance) is not int or type(maximum) is not int or maximum < 0:
            raise ValueError("ledger prefix needs an exact balance and natural count")
        limit = min(maximum, self.capacity)
        if limit == 0 or balance + self.action.minimum < 0:
            return 0
        if self.action.delta >= 0:
            return limit
        return min(
            limit,
            1 + (balance + self.action.minimum) // -self.action.delta,
        )

    def power(
        self, repetitions: int, *, max_extent: int = 4096
    ) -> MahlerOddToOddAction:
        if not self.admits(repetitions):
            raise ValueError(
                "requested mixed-event repeat is outside its certified source cylinder"
            )
        powered = self.action.power(repetitions, max_extent=max_extent)
        if not powered.integer_admits(self.source):
            raise ArithmeticError(
                "mixed odd-event temporal power lost its source guard"
            )
        return powered

    def endpoint(self, repetitions: int, *, max_bits: int = 65536) -> int:
        if not self.admits(repetitions):
            raise ValueError("uncertified mixed-event endpoint")
        if type(max_bits) is not int or not 1 <= max_bits <= 1_048_576:
            raise ValueError("mixed endpoint bit budget is outside the supported bound")
        if repetitions == 0:
            return self.source
        shift = self.extent * repetitions
        if (
            self.multiplier.bit_length() * repetitions + abs(self.defect).bit_length()
            > max_bits
        ):
            raise BlockContextBudgetExceeded(
                "materialized mixed odd-event endpoint exceeds bit budget"
            )
        numerator = self.offset + pow(self.multiplier, repetitions) * (
            self.defect >> shift
        )
        endpoint: int
        rem: int
        endpoint, rem = divmod(numerator, self.k)
        if rem or endpoint <= 0 or endpoint % 2 != 1:
            raise ArithmeticError(
                "powered mixed Mahler endpoint lost odd-source authorization"
            )
        return endpoint

    def binary_residue(self, bits: int, repetitions: int) -> int:
        if (
            type(bits) is not int
            or not 0 <= bits <= MAX_MAHLER_SOURCE_EXTENT
            or not self.admits(repetitions)
        ):
            raise ValueError(
                "mixed binary residue demand is outside authorized precision"
            )
        if bits == 0:
            return 0
        modulus = 1 << bits
        numerator = self.offset + pow(self.multiplier, repetitions, modulus) * (
            self.defect >> (self.extent * repetitions)
        )
        return (numerator * pow(self.k, -1, modulus)) % modulus

    def radix_residue(self, radix: int, places: int, repetitions: int) -> int:
        if (
            type(radix) is not int
            or not 2 <= radix <= 64
            or type(places) is not int
            or not 1 <= places <= 128
        ):
            raise ValueError(
                "mixed radix demand is outside supported bounded precision"
            )
        if not self.admits(repetitions):
            raise ValueError("radix projection needs a certified source interval")
        modulus: int = radix**places
        bits = v2_positive(modulus)
        m2 = 1 << bits
        low2 = self.binary_residue(bits, repetitions)
        odd_mod = modulus >> bits
        if odd_mod == 1:
            return low2
        inv2: int = pow(1 << self.extent, -1, odd_mod)
        gain: int = self.multiplier * inv2 % odd_mod
        offset: int = self.offset * inv2 % odd_mod
        a, b = _affine_pow(gain, offset, repetitions, odd_mod)
        odd_residue: int = (a * self.source + b) % odd_mod
        if not bits:
            return odd_residue
        crt_inverse: int = pow(m2, -1, odd_mod)
        correction: int = ((odd_residue - low2) * crt_inverse) % odd_mod
        return (low2 + m2 * correction) % modulus

    def q_phase_spectrum(
        self,
        radix: int,
        places: int,
        repetitions: int,
        *,
        clock: int,
        walsh64: bool = False,
        max_states: int = 8192,
    ) -> MahlerMixedQHarmonicSpectrum:
        """Compose every event of a known motif through a finite q/carry cone.

        Uses (q mod M, 2**n mod M, motif phase, n_events mod 6).
        The q recurrence has NO denominator and works in even radices.
        A detected modular period is a period only while the exact source
        cylinder certifies the repetitions; it cannot admit a new exponent.
        """
        if (
            type(radix) is not int
            or not 2 <= radix <= 64
            or type(places) is not int
            or not 1 <= places <= 6
        ):
            raise ValueError("q temporal quotient needs bounded radix cells")
        if (
            type(clock) is not int
            or clock < 0
            or type(walsh64) is not bool
            or not self.admits(repetitions)
            or repetitions < 1
        ):
            raise ValueError("q temporal source clock or repetition is unauthenticated")
        _validate_harmonic_state_budget(max_states)
        # This observer composes only residues modulo the bounded radix
        # modulus. The exact source-cylinder guard above authorizes the
        # repeated motif; the coefficient/endpoint extent cap belongs to
        # materializing those exact integers, not to this finite modular
        # projection. Work here is independently bounded by max_states.
        total = repetitions * len(self.exponents)
        if walsh64 and total < 64:
            raise ValueError("Walsh64 needs at least 64 source-certified events")
        modulus = radix**places
        q0 = pow(2, clock, modulus) * (3 * self.source + 1) % modulus
        # The modulus may be even: retain 2**clock as a separate state.
        initial = (q0, pow(2, clock, modulus), 0, 0)
        state = initial
        seen: dict[tuple[int, int, int, int], int] = {}
        emissions: list[tuple[int, int, int, int]] = []
        successor_states: list[tuple[int, int, int, int]] = []
        cycle_start: int | None = None
        while len(emissions) < max_states:
            if state in seen:
                cycle_start = seen[state]
                break
            seen[state] = len(emissions)
            q, powtwo, phase, six_phase = state
            exponent = self.exponents[phase]
            gain = pow(3, exponent, modulus)
            factor2 = pow(2, exponent, modulus)
            powtwo_next = factor2 * powtwo % modulus
            q_next = (gain * q + powtwo_next) % modulus
            carry_mask, borrow_mask = 0, 0
            for j in range(1, places + 1):
                m = radix**j
                before = q % m
                product = pow(3, exponent, m) * before % m
                summand = powtwo_next % m
                after = (product + summand) % m
                if after != q_next % m:
                    raise ArithmeticError(
                        "q prime/CRT carry cells disagree with full modular transfer"
                    )
                carry_mask |= int(product + summand >= m) << (j - 1)
                borrow_mask |= int(after < before) << (j - 1)
            emissions.append((exponent, carry_mask, borrow_mask, six_phase))
            state = (
                q_next,
                powtwo_next,
                (phase + 1) % len(self.exponents),
                (six_phase + 1) % 6,
            )
            successor_states.append(state)
            if len(emissions) == total:
                break
        if cycle_start is None and state in seen:
            cycle_start = seen[state]
        if cycle_start is None:
            if len(emissions) != total:
                raise BlockContextBudgetExceeded(
                    "q finite harmonic state failed to close within budget"
                )
            prefix = tuple(emissions)
            cycle: tuple[tuple[int, int, int, int], ...] = ()
            future_classes = None
        else:
            prefix, cycle = (
                tuple(emissions[:cycle_start]),
                tuple(emissions[cycle_start:]),
            )
            orbit_successors = tuple(seen[target] for target in successor_states)
            future_classes = minimize_finite_orbit(
                orbit_successors,
                tuple(emissions),
                max_states=max_states,
            ).class_count

        def series(cell: int, kind: int) -> tuple[int, ...]:
            def word(records: tuple[tuple[int, int, int, int], ...]) -> tuple[int, ...]:
                return tuple((record[kind] >> cell) & 1 for record in records)

            counts = _phase_histogram(word(prefix), word(cycle), total, 2)
            return counts[1]

        carries = tuple(series(i, 1) for i in range(places))
        borrows = tuple(series(i, 2) for i in range(places))
        xors = tuple(
            _phase_histogram(
                tuple(((e[1] ^ e[2]) >> i) & 1 for e in prefix),
                tuple(((e[1] ^ e[2]) >> i) & 1 for e in cycle),
                total,
                2,
            )[1]
            for i in range(places)
        )
        walsh = None
        if walsh64:
            walsh = tuple(
                walsh64_mod5(
                    sum(
                        (
                            (
                                _orbit_at(prefix, cycle, t)[1]
                                ^ _orbit_at(prefix, cycle, t)[2]
                            )
                            >> i
                            & 1
                        )
                        << t
                        for t in range(64)
                    )
                )
                for i in range(places)
            )
        return MahlerMixedQHarmonicSpectrum(
            radix,
            places,
            repetitions,
            total,
            len(prefix),
            len(cycle),
            future_classes,
            carries,
            borrows,
            xors,
            walsh,
        )

    def observation(
        self, *, repetitions: int, clock: int, places: int = 2, walsh64: bool = False
    ) -> dict[str, object]:
        """One demanded, producer-bound multi-prime and temporal harmonic packet."""
        if (
            type(places) is not int
            or not 1 <= places <= 6
            or type(clock) is not int
            or clock < 0
            or type(walsh64) is not bool
        ):
            raise ValueError(
                "mixed harmonic demand is outside its exact bounded domain"
            )
        if not self.admits(repetitions) or repetitions < 1:
            raise ValueError(
                "mixed observation needs a source-certified repeated motif"
            )
        powered = self.power(repetitions)
        q_rows: dict[str, object] = {}
        for radix in (2, 3, 5, 6, 10, 64):
            sp = self.q_phase_spectrum(
                radix,
                places,
                repetitions,
                clock=clock,
                walsh64=walsh64 and repetitions * len(self.exponents) >= 64,
            )
            q_rows[str(radix)] = {
                "temporal_prefix": sp.prefix_length,
                "temporal_period": sp.period,
                "future_moore_classes": sp.future_moore_classes,
                "carry_phase_counts": sp.carry_phase_counts,
                "borrow_phase_counts": sp.borrow_phase_counts,
                "xor_phase_counts": sp.xor_phase_counts,
                "walsh64_xor": sp.walsh64_xor,
            }
        return {
            "motif": self.exponents,
            "repetitions": repetitions,
            "certified_capacity": self.capacity,
            "source_guard": (powered.source_residue, powered.source_modulus),
            "source_clock": clock,
            "extent": repetitions * self.extent,
            "radial_scale": (repetitions * self.extent, repetitions * self.extent),
            "ledger_delta": powered.delta,
            "ledger_minimum": powered.minimum,
            "fractional_guard_empty": powered.joint.guard.empty,
            "endpoint_radix_residues": {
                str(radix): self.radix_residue(radix, places, repetitions)
                for radix in (2, 3, 5, 6, 10, 64)
            },
            "q_temporal_harmonics": q_rows,
            "source_bound": True,
            "all_time_claim": False,
        }


__all__ = ("MahlerMixedOddHarmonicRing", "MahlerMixedQHarmonicSpectrum")
