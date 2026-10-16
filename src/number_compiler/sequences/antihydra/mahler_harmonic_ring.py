"""NC16 Mahler fixed-odd-event harmonic ring, source-closed under 2-adic guards.

This specializes the NC16 Collatz *fixed-word defect* ring to the true
Antihydra/Mahler word ``1 0**(a-1)``.  No 2rev10 reversal stencil is reused:
its contribution is the open, source-fed conditional Moore interface in
``mahler_open_harmonic_moore``.

For P=3**a, Q=2**a, J=3**(a-1) and an odd integer D,
    A(D)=(P D+J)/Q,
    H=(P-Q)D+J,  H(A(D))=(P/Q)H(D).
The source can follow exactly r complete odd-to-odd copies only if
    v2(H)>=a*r+1.
This is a *finite* certificate. The Mahler fractional guard and Antihydra
ledger remain separate predicates and no infinite-source repetition is claimed.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd
from typing import TYPE_CHECKING, TypeVar

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.morphism_core import AffineCocycle, binary_power
from number_compiler.arithmetic.fields.two_adic import v2_nonzero, v2_positive
from number_compiler.arithmetic.fields.walsh import walsh64_mod5
from number_compiler.arithmetic.functions.finite_observer import (
    MAX_FINITE_ORBIT_STATES,
)

if TYPE_CHECKING:
    from number_compiler.sequences.antihydra.mahler_odd_macro import (
        MahlerOddToOddAction,
    )

OrbitValue = TypeVar("OrbitValue")


class OpenMahlerRingInletsRequired(ValueError):
    """The source cone does not fix an interior binary bank."""


def _xor_f5_projection(
    phase_counts: tuple[tuple[int, ...], ...], places: int
) -> tuple[int, ...]:
    """Project one position-by-six-phase XOR bank into its F5 channel."""
    return tuple(
        sum(phase_counts[position][phase] for position in range(places)) % 5
        for phase in range(6)
    )


def _validate_harmonic_state_budget(max_states: int) -> None:
    if type(max_states) is not int or max_states < 1:
        raise ValueError("finite harmonic orbit budget must be positive")
    if max_states > MAX_FINITE_ORBIT_STATES:
        raise BlockContextBudgetExceeded(
            "Mahler harmonic orbit exceeds the shared finite-state budget"
        )


def _affine_pow(
    gain: int, offset: int, repetitions: int, modulus: int
) -> tuple[int, int]:
    """Power any modular affine transfer, including nonunit prime factors."""
    if type(modulus) is not int or modulus < 1:
        raise ValueError("affine modulus must be a positive exact integer")
    action = AffineCocycle(gain % modulus, offset % modulus)
    identity = AffineCocycle(1 % modulus, 0)

    def compose(
        first: AffineCocycle[int], after: AffineCocycle[int]
    ) -> AffineCocycle[int]:
        return first.then(
            after,
            multiply=lambda left, right: left * right % modulus,
            add=lambda left, right: (left + right) % modulus,
        )

    powered = binary_power(
        action, repetitions, identity=identity, compose=compose
    ).value
    return powered.multiplier, powered.addend


def _phase_histogram(
    prefix: tuple[int, ...], cycle: tuple[int, ...], count: int, alphabet: int
) -> tuple[tuple[int, ...], ...]:
    """Count temporal digits by index mod 6, in O(preperiod+period), not O(count)."""
    totals = [[0] * 6 for _ in range(alphabet)]
    leading = min(len(prefix), count)
    for t in range(leading):
        totals[prefix[t]][t % 6] += 1
    remain = count - leading
    if remain and not cycle:
        raise ArithmeticError(
            "finite harmonic orbit exhausted before requested horizon"
        )
    if remain:
        size = len(cycle)
        full, tail = divmod(remain, size)
        orbit_phase = 6 // gcd(size, 6)
        for i, digit in enumerate(cycle):
            for k in range(orbit_phase):
                n = 0 if full <= k else 1 + (full - k - 1) // orbit_phase
                if n:
                    totals[digit][(leading + i + k * size) % 6] += n
        for i in range(tail):
            totals[cycle[i]][(leading + full * size + i) % 6] += 1
    if sum(map(sum, totals)) != count:
        raise ArithmeticError("harmonic phase counts do not conserve source extent")
    return tuple(tuple(row) for row in totals)


def _orbit_at(
    prefix: tuple[OrbitValue, ...], cycle: tuple[OrbitValue, ...], at: int
) -> OrbitValue:
    if at < len(prefix):
        return prefix[at]
    if not cycle:
        raise ValueError("requested time is outside a finite nonperiodic orbit")
    return cycle[(at - len(prefix)) % len(cycle)]


@dataclass(frozen=True, slots=True)
class MahlerRingSpectrum:
    """Exact time-phase/F5 count for a fixed *spatial digit position*."""

    radix: int
    position: int
    copies: int
    prefix_length: int
    period: int
    six_phase_counts: tuple[tuple[int, ...], ...]
    walsh64_parity: tuple[int, ...] | None
    source_guard_bits: int

    @property
    def digit_counts(self) -> tuple[int, ...]:
        return tuple(sum(row) for row in self.six_phase_counts)

    @property
    def phase_f5(self) -> tuple[int, ...]:
        return tuple(
            sum(digit * row[k] for digit, row in enumerate(self.six_phase_counts)) % 5
            for k in range(6)
        )


@dataclass(frozen=True, slots=True)
class MahlerQHarmonicSpectrum:
    """Temporal F5 six-phase carry/borrow spectra of the true q numerator."""

    radix: int
    places: int
    copies: int
    source_clock: int
    prefix_length: int
    period: int
    carry_phase_counts: tuple[tuple[int, ...], ...]
    borrow_phase_counts: tuple[tuple[int, ...], ...]
    xor_phase_counts: tuple[tuple[int, ...], ...]
    walsh64_xor: tuple[tuple[int, ...], ...] | None

    @property
    def xor_f5(self) -> tuple[int, ...]:
        return _xor_f5_projection(self.xor_phase_counts, self.places)


@dataclass(frozen=True, slots=True)
class MahlerFixedOddHarmonicRing:
    """Exact positive source and maximal repeated *fixed-exponent* event cylinder.

    A different exponent is never inferred from equal F5/phase/harmonic IDs.
    The orbit is computed modulo demanded odd moduli and from consumed binary
    source bits, with no illegal 2^-a in an even modulus.
    """

    source: int
    exponent: int
    capacity: int
    defect: int

    @classmethod
    def from_source(
        cls, source: int, *, max_exponent: int = 4096
    ) -> MahlerFixedOddHarmonicRing:
        if type(source) is not int or source <= 0 or not source & 1:
            raise ValueError("Mahler odd harmonic ring requires a positive odd source")
        exponent = v2_positive(3 * source + 1)
        if exponent > max_exponent:
            raise BlockContextBudgetExceeded(
                "source odd event exceeds permitted length"
            )
        p, q, j = 3**exponent, 1 << exponent, 3 ** (exponent - 1)
        defect = (q - p) * source - j
        if not defect:
            raise ArithmeticError(
                "positive Mahler source has an impossible zero defect"
            )
        return cls(
            source, exponent, max(0, (v2_nonzero(defect) - 1) // exponent), defect
        )

    def __post_init__(self) -> None:
        if type(self.source) is not int or self.source <= 0 or not self.source & 1:
            raise ValueError("odd positive source required")
        if type(self.exponent) is not int or self.exponent < 1:
            raise ValueError("positive odd-run exponent required")
        if any(type(x) is not int for x in (self.capacity, self.defect)):
            raise TypeError("exact ring coefficients required")
        if v2_positive(3 * self.source + 1) != self.exponent:
            raise ValueError("ring exponent does not match pointed source")
        if self.defect != self.k * self.source - self.j or self.capacity != max(
            0, (v2_nonzero(self.defect) - 1) // self.exponent
        ):
            raise ValueError("ring source/cylinder capacity certificate is invalid")

    @property
    def p(self) -> int:
        value: int = 3**self.exponent
        return value

    @property
    def q(self) -> int:
        return 1 << self.exponent

    @property
    def j(self) -> int:
        value: int = 3 ** (self.exponent - 1)
        return value

    @property
    def k(self) -> int:
        return self.q - self.p

    @property
    def defect_valuation(self) -> int:
        return v2_nonzero(self.defect)

    @staticmethod
    def source_cylinder(exponent: int, repetitions: int) -> tuple[int, int]:
        """Unique source class for r complete odd-to-odd fixed-word copies."""
        if (
            type(exponent) is not int
            or exponent < 1
            or type(repetitions) is not int
            or repetitions < 1
        ):
            raise ValueError("positive exponent/repetitions required")
        bits = exponent * repetitions + 1
        if bits > 16384:
            raise BlockContextBudgetExceeded("Mahler ring cylinder exceeds bit budget")
        modulus = 1 << bits
        residue: int = (
            3 ** (exponent - 1) * pow((1 << exponent) - 3**exponent, -1, modulus)
        ) % modulus
        return residue, modulus

    def admits(self, repetitions: int) -> bool:
        return type(repetitions) is int and 0 <= repetitions <= self.capacity

    def demand_count(
        self, *, max_events: int, max_steps: int, balance: int | None = None
    ) -> int:
        if any(type(v) is not int or v < 0 for v in (max_events, max_steps)):
            raise ValueError("event and step budgets must be nonnegative")
        if balance is not None and (type(balance) is not int or balance < 0):
            raise ValueError("ledger balance must be nonnegative")
        count = min(self.capacity, max_events, max_steps // self.exponent)
        if balance is not None and self.exponent > 3:
            count = min(count, balance // (self.exponent - 3))
        return count

    def action(
        self, repetitions: int, *, max_extent: int = 4096
    ) -> MahlerOddToOddAction:
        """The authoritative source/fraction/ledger action, not just an orbit."""
        if not self.admits(repetitions):
            raise ValueError("future fixed event is not source-certified")
        from number_compiler.sequences.antihydra.mahler_odd_macro import (
            MahlerOddToOddAction,
        )

        seed_action = MahlerOddToOddAction.run(self.exponent, max_extent=max_extent)
        result = (
            seed_action
            if repetitions == 1
            else seed_action.power(repetitions, max_extent=max_extent)
        )
        if not result.integer_admits(self.source):
            raise ArithmeticError(
                "powered Mahler ring disagrees with its 2-adic cylinder"
            )
        return result

    def endpoint(self, repetitions: int, *, max_bits: int = 65536) -> int:
        if not self.admits(repetitions):
            raise ValueError("future event is outside exact source cylinder")
        if self.p.bit_length() * repetitions + abs(self.defect).bit_length() > max_bits:
            raise BlockContextBudgetExceeded(
                "requested materialized endpoint exceeds bit budget"
            )
        gain_power: int = self.p**repetitions
        numerator: int = self.j + gain_power * (
            self.defect >> (self.exponent * repetitions)
        )
        endpoint_value, remainder = divmod(numerator, self.k)
        endpoint: int = endpoint_value
        if remainder or endpoint <= 0 or not endpoint & 1:
            raise ArithmeticError("fixed-run ring lost its exact odd endpoint")
        return endpoint

    def binary_residue(self, bits: int, repetitions: int) -> int:
        """Exact low bits using the source defect after a*r dyadic shifts."""
        if (
            type(bits) is not int
            or not 0 <= bits <= 4096
            or not self.admits(repetitions)
        ):
            raise ValueError("binary demand outside admitted ring or precision budget")
        if not bits:
            return 0
        modulus = 1 << bits
        residue: int = (
            (
                self.j
                + pow(self.p, repetitions, modulus)
                * (self.defect >> (self.exponent * repetitions))
            )
            * pow(self.k, -1, modulus)
        ) % modulus
        return residue

    def odd_modulus_residue(self, modulus: int, repetitions: int) -> int:
        if (
            type(modulus) is not int
            or modulus < 1
            or modulus % 2 == 0
            or not self.admits(repetitions)
        ):
            raise ValueError("odd-modulus orbit demands an admitted ring")
        inverse_q = pow(self.q, -1, modulus)
        gain, offset = _affine_pow(
            self.p * inverse_q, self.j * inverse_q, repetitions, modulus
        )
        residue: int = (gain * self.source + offset) % modulus
        return residue

    def radix_residue(self, radix: int, places: int, repetitions: int) -> int:
        """Joint 2/odd CRT residue without inverse(2) at an even boundary."""
        if (
            type(radix) is not int
            or not 2 <= radix <= 64
            or type(places) is not int
            or not 1 <= places <= 256
        ):
            raise ValueError("radix/precision outside the demanded digit grammar")
        if not self.admits(repetitions):
            raise ValueError("radix request is outside source-certified ring")
        modulus = radix**places
        bits = v2_positive(modulus)
        if not bits:
            return self.odd_modulus_residue(modulus, repetitions)
        binary_mod = 1 << bits
        low = self.binary_residue(bits, repetitions)
        odd_mod = modulus >> bits
        if odd_mod == 1:
            return low
        odd = self.odd_modulus_residue(odd_mod, repetitions)
        residue: int = (
            low + binary_mod * (((odd - low) * pow(binary_mod, -1, odd_mod)) % odd_mod)
        ) % modulus
        return residue

    def inlet(self, index: int, binary_bits: int) -> int:
        """Source-certified open-ring inlet: *never* wrap a spatial bank."""
        if type(binary_bits) is not int or binary_bits < self.exponent + 1:
            raise ValueError("open-ring bank must retain final odd-seam lookahead")
        if type(index) is not int or not 0 <= index < self.capacity:
            raise ValueError("open-ring inlet lies outside admitted source")
        return self.binary_residue(binary_bits + self.exponent, index) >> binary_bits

    def position_spectrum(
        self,
        radix: int,
        position: int,
        repetitions: int,
        *,
        walsh64: bool = False,
        max_states: int = 8192,
    ) -> MahlerRingSpectrum:
        """Power per-position orbit through finite odd-radix states and a 2-adic cone.

        The binary component is constant iff the source defect has the full
        ``a*r+v2(radix**(position+1))`` precision. Otherwise an *open*
        source inlet is required; we refuse to substitute an invented period.
        """
        if (
            type(radix) is not int
            or not 2 <= radix <= 64
            or type(position) is not int
            or not 0 <= position <= 16
        ):
            raise ValueError("invalid radix position for harmonic ring")
        if not self.admits(repetitions) or repetitions < 1:
            raise ValueError("source did not admit requested repeated motif")
        _validate_harmonic_state_budget(max_states)
        modulus = radix ** (position + 1)
        binary_bits = v2_positive(modulus)
        if self.defect_valuation < self.exponent * repetitions + binary_bits:
            raise OpenMahlerRingInletsRequired(
                "source cone does not fix the interior binary bank"
            )
        binary = self.source % (1 << binary_bits) if binary_bits else 0
        odd_mod = modulus >> binary_bits
        prefix: tuple[int, ...]
        cycle: tuple[int, ...]
        if odd_mod == 1:
            prefix, cycle = (), (binary // (radix**position) % radix,)
        else:
            inverse_q = pow(self.q, -1, odd_mod)
            affine_a, affine_b = (
                self.p * inverse_q % odd_mod,
                self.j * inverse_q % odd_mod,
            )
            visited: dict[int, int] = {}
            digits: list[int] = []
            odd_state = self.source % odd_mod
            cycle_begin: int | None = None
            while len(digits) < max_states:
                if odd_state in visited:
                    cycle_begin = visited[odd_state]
                    break
                visited[odd_state] = len(digits)
                if binary_bits:
                    binary_mod = 1 << binary_bits
                    mixed = (
                        binary
                        + binary_mod
                        * (
                            ((odd_state - binary) * pow(binary_mod, -1, odd_mod))
                            % odd_mod
                        )
                    ) % modulus
                else:
                    mixed = odd_state
                digits.append((mixed // radix**position) % radix)
                odd_state = (affine_a * odd_state + affine_b) % odd_mod
                if len(digits) == repetitions:
                    break
            if cycle_begin is None:
                if len(digits) != repetitions:
                    raise BlockContextBudgetExceeded(
                        "odd-prime harmonic ring did not close within state budget"
                    )
                prefix, cycle = tuple(digits), ()
            else:
                prefix, cycle = tuple(digits[:cycle_begin]), tuple(digits[cycle_begin:])
        counts = _phase_histogram(prefix, cycle, repetitions, radix)
        walsh_packet = None
        if walsh64:
            if repetitions < 64:
                raise ValueError("Walsh64 temporal ring requires 64 certified copies")
            mask = sum((_orbit_at(prefix, cycle, t) & 1) << t for t in range(64))
            walsh_packet = walsh64_mod5(mask)
        return MahlerRingSpectrum(
            radix,
            position,
            repetitions,
            len(prefix),
            len(cycle),
            counts,
            walsh_packet,
            self.exponent * repetitions + binary_bits,
        )

    def q_phase_spectrum(
        self,
        radix: int,
        places: int,
        repetitions: int,
        *,
        clock: int,
        walsh64: bool = False,
        max_states: int = 8192,
    ) -> MahlerQHarmonicSpectrum:
        """Exact periodic odd-prime ring for q_(i+1)=3**a*q_i+2**(n+a).

        State is (D mod p**places, 2**n mod p**places). Both coordinates
        advance by finite affine/multiplicative actions when the source is
        certified to repeat the same odd-run exponent. This is *not* an
        infinite Z-number or Antihydra ledger certificate.
        """
        if type(radix) is not int or not 3 <= radix <= 63 or not radix & 1:
            raise ValueError("q temporal harmonic ring requires odd prime-radix cells")
        if type(places) is not int or not 1 <= places <= 6:
            raise ValueError("bounded q harmonic spatial positions required")
        if (
            type(clock) is not int
            or clock < 0
            or not self.admits(repetitions)
            or repetitions < 1
        ):
            raise ValueError("q harmonic request has unadmitted time/source")
        _validate_harmonic_state_budget(max_states)
        if walsh64 and repetitions < 64:
            raise ValueError("Walsh64 temporal q spectrum needs 64 admitted copies")
        modulus = radix**places
        invq = pow(self.q, -1, modulus)
        affine_gain = self.p * invq % modulus
        affine_offset = self.j * invq % modulus
        step_shift = pow(2, self.exponent, modulus)
        state = (self.source % modulus, pow(2, clock, modulus))
        seen: dict[tuple[int, int], int] = {}
        sequence: list[tuple[int, int]] = []
        cycle_begin: int | None = None
        while len(sequence) < max_states:
            if state in seen:
                cycle_begin = seen[state]
                break
            seen[state] = len(sequence)
            d, powtwo = state
            next_d = (affine_gain * d + affine_offset) % modulus
            next_powtwo = step_shift * powtwo % modulus
            q_now = powtwo * (3 * d + 1) % modulus
            q_next = next_powtwo * (3 * next_d + 1) % modulus
            carry, borrow = 0, 0
            for j in range(1, places + 1):
                cell_mod = radix**j
                before = q_now % cell_mod
                product = ((self.p % cell_mod) * before) % cell_mod
                summand = next_powtwo % cell_mod
                after = (product + summand) % cell_mod
                if after != q_next % cell_mod:
                    raise ArithmeticError(
                        "q harmonic recurrence disagrees with source-guarded affine orbit"
                    )
                carry |= int(product + summand >= cell_mod) << (j - 1)
                borrow |= int(after < before) << (j - 1)
            sequence.append((carry, borrow))
            state = next_d, next_powtwo
            if len(sequence) == repetitions:
                break
        prefix: tuple[tuple[int, int], ...]
        cycle: tuple[tuple[int, int], ...]
        if cycle_begin is None:
            if len(sequence) < repetitions:
                raise BlockContextBudgetExceeded(
                    "q temporal orbit did not close within finite-state budget"
                )
            prefix, cycle = tuple(sequence), ()
        else:
            prefix, cycle = tuple(sequence[:cycle_begin]), tuple(sequence[cycle_begin:])

        def selected(pair: tuple[int, int], kind: str) -> int:
            if kind == "carry":
                return pair[0]
            if kind == "borrow":
                return pair[1]
            return pair[0] ^ pair[1]

        def series(bit: int, kind: str) -> tuple[int, ...]:
            pre = tuple((selected(pair, kind) >> bit) & 1 for pair in prefix)
            cyc = tuple((selected(pair, kind) >> bit) & 1 for pair in cycle)
            binary_counts = _phase_histogram(pre, cyc, repetitions, 2)
            return binary_counts[1]

        carries = tuple(series(i, "carry") for i in range(places))
        borrows = tuple(series(i, "borrow") for i in range(places))
        xors = tuple(series(i, "xor") for i in range(places))
        walsh_packet = None
        if walsh64:
            walsh_packet = tuple(
                walsh64_mod5(
                    sum(
                        (
                            (
                                _orbit_at(prefix, cycle, t)[0]
                                ^ _orbit_at(prefix, cycle, t)[1]
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
        return MahlerQHarmonicSpectrum(
            radix,
            places,
            repetitions,
            clock,
            len(prefix),
            len(cycle),
            carries,
            borrows,
            xors,
            walsh_packet,
        )


__all__ = (
    "MahlerFixedOddHarmonicRing",
    "MahlerQHarmonicSpectrum",
    "MahlerRingSpectrum",
)
