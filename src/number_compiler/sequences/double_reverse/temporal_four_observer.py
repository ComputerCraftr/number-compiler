"""One source-bound four-output carry action and its finite temporal quotient.

The two full internal waves are produced by the same alternating-frame
transducer.  The other two observations are the *boundary-only* overflow
reinsertions in the normal and mirrored orientations.  They are comparisons,
not extra corrections to the physical scalar recurrence.

The certified border phase supplies the two terminal overflow bits.  This
module never infers a global left boundary from a local right suffix.

All period results below concern a finite authenticated sequence of output
actions.  They are not assertions about unobserved future generations.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass

from number_compiler.arithmetic.fields.morphism_core import binary_power

from .temporal_defect_quotient import FourSymbolDefect, defect_modulus
from .temporal_hashlife import PHYSICAL_GROWTH_CYCLES

# Each selected modulus is coprime to ten and ord_m(10) divides 12.
# These projections are computed from the BORDER width clock, not a
# materialized repunit or a separately reconstructed source orbit.
CYCLIC_NEGACYCLIC_MODULI = (7, 9, 11, 13, 37, 101, 999, 1001)


def _trailing_agreement(a: int, b: int, width: int) -> int:
    """Largest w <= width for which a == b modulo 10**w."""
    difference = abs(a - b)
    if difference == 0:
        return width
    matched = 0
    while matched < width and difference % 10 == 0:
        matched += 1
        difference //= 10
    return matched


def _p_signature(
    value: int, primes: tuple[int, ...] = (2, 3, 5, 7, 11)
) -> dict[str, object]:
    """Exact valuation + leading p-adic unit, including cancellation at zero."""
    if value == 0:
        return {str(p): {"valuation": None, "unit_mod_p4": None} for p in primes}
    values: dict[str, object] = {}
    for p in primes:
        absolute = abs(value)
        v = 0
        while absolute % p == 0:
            absolute //= p
            v += 1
        unit = (value // p**v) % p**4
        values[str(p)] = {"valuation": v, "unit_mod_p4": unit}
    return values


@dataclass(frozen=True, slots=True)
class FourObserverEmission:
    """Canonical four-observer output of two consecutive F=T^2 actions.

    The first two fields are signed *local* four-symbol carry words in a
    common decimal suffix coordinate.  Mirroring this bounded suffix is not
    reflection of the entire global word.  Boundary-only overflow defects
    are independently computed using certified full-word widths and phases.
    """

    defect: FourSymbolDefect
    phase: int
    # The physical width is saturated away when it cannot affect any
    # requested residue. Only a genuinely narrow boundary is retained.
    narrow_source_width: int | None = None
    width_phase12: int = 0

    @classmethod
    def from_source(
        cls, defect: FourSymbolDefect, *, phase: int, source_width: int
    ) -> FourObserverEmission:
        defect.verify()
        if type(phase) is not int or phase not in (0, 1, 2, 3):
            raise ValueError("invalid authenticated four-observer phase")
        if type(source_width) is not int or source_width < 1:
            raise ValueError("invalid authenticated source word width")
        r0, l0, r1, l1 = PHYSICAL_GROWTH_CYCLES[phase]
        if (r0, r1) != (defect.first_growth, defect.second_growth):
            raise ValueError(
                "carry-derived right growth conflicts with certified border"
            )
        if l0 + r0 != 1 or l1 + r1 != 1:
            raise ValueError("four-symbol defect requires the one-birth border phase")
        return cls(
            defect,
            phase,
            source_width if source_width < defect.width else None,
            source_width % 12,
        )

    @property
    def right(self) -> int:
        return self.defect.combined_decimal

    @property
    def left(self) -> int:
        return self.defect.left_defect_decimal()

    @property
    def difference(self) -> int:
        # The waves share the same bounded suffix coordinate, not a global
        # reversed-prefix coordinate. Their difference is an observer only.
        return self.right - self.left

    @property
    def right_overflow(self) -> tuple[int, int]:
        word = PHYSICAL_GROWTH_CYCLES[self.phase]
        return word[0], word[2]

    @property
    def mirrored_left_overflow(self) -> tuple[int, int]:
        word = PHYSICAL_GROWTH_CYCLES[self.phase]
        return word[1], word[3]

    def _overflow_defects(
        self, digits: int, flags: tuple[int, int], *, factor: int, reflected: bool
    ) -> tuple[int, int]:
        if (
            type(digits) is not int
            or not 1 <= digits <= self.defect.width
            or type(factor) is not int
            or factor not in (1, 2)
        ):
            raise ValueError("invalid overflow projection precision")
        double_modulus = defect_modulus(digits)
        modulus = double_modulus if factor == 2 else double_modulus // 2
        width = self.narrow_source_width
        if width is None:
            return (-flags[0]) % modulus, (-flags[1]) % modulus
        growth_first = sum(PHYSICAL_GROWTH_CYCLES[self.phase][:2])
        if reflected:
            widths = (
                width + self.right_overflow[0],
                width + growth_first + self.right_overflow[1],
            )
        else:
            widths = (width, width + growth_first)
        first = flags[0] * (pow(10, widths[0] + 1, modulus) - 1) % modulus
        second = flags[1] * (pow(10, widths[1] + 1, modulus) - 1) % modulus
        return first, second

    def right_overflow_defects(
        self, digits: int, *, factor: int = 1
    ) -> tuple[int, int]:
        """Overflow-only reinsertion, on the two reflected source operands."""
        return self._overflow_defects(
            digits, self.right_overflow, factor=factor, reflected=False
        )

    def mirrored_left_overflow_defects(
        self, digits: int, *, factor: int = 1
    ) -> tuple[int, int]:
        """Opposite-boundary reinsertion, on the two normal odd operands."""
        return self._overflow_defects(
            digits, self.mirrored_left_overflow, factor=factor, reflected=True
        )

    def semantic_key(self, width: int) -> tuple[int, int, int, int | None]:
        """Occurrence-free sampled Moore-output signature at one precision.

        Width is relevant only below the requested precision. Equality of
        these signatures is NOT claimed to imply all-future right congruence.
        """
        if type(width) is not int or not 1 <= width <= self.defect.width:
            raise ValueError("invalid semantic carry quotient width")
        modulus = 10**width
        return (
            self.phase,
            self.right % modulus,
            self.left % modulus,
            (
                self.narrow_source_width
                if self.narrow_source_width is not None
                and self.narrow_source_width < width
                else None
            ),
        )

    def cyclotomic_key(self, modulus: int) -> tuple[int, ...]:
        """All four outputs modulo one certified cyclic/negacyclic factor.

        The full repunit width is replaced by its 12-phase clock; no
        occurrence-specific decimal exponent is retained in the key.
        """
        if type(modulus) is not int or modulus not in CYCLIC_NEGACYCLIC_MODULI:
            raise ValueError("unsupported certified cyclotomic factor")
        if pow(10, 12, modulus) != 1:
            raise AssertionError("cyclotomic width-phase certificate is invalid")
        g0 = sum(PHYSICAL_GROWTH_CYCLES[self.phase][:2])
        r0, r1 = self.right_overflow
        l0, l1 = self.mirrored_left_overflow
        right_exponents = (self.width_phase12 + 1, self.width_phase12 + g0 + 1)
        left_exponents = (self.width_phase12 + r0 + 1, self.width_phase12 + g0 + r1 + 1)
        right = tuple(
            b * (pow(10, exponent % 12, modulus) - 1) % modulus
            for b, exponent in zip((r0, r1), right_exponents, strict=True)
        )
        left = tuple(
            b * (pow(10, exponent % 12, modulus) - 1) % modulus
            for b, exponent in zip((l0, l1), left_exponents, strict=True)
        )
        return (
            self.phase,
            self.right % modulus,
            self.left % modulus,
            right[0],
            right[1],
            left[0],
            left[1],
        )

    def output_at_width(
        self, width: int
    ) -> tuple[int, int, tuple[int, int], tuple[int, int]]:
        if type(width) is not int or not 1 <= width <= self.defect.width:
            raise ValueError("four-observer projection exceeds certified suffix")
        modulus = 10**width
        return (
            self.right % modulus,
            self.left % modulus,
            self.right_overflow,
            self.mirrored_left_overflow,
        )

    def difference_signature(self) -> dict[str, object]:
        return _p_signature(99 * self.difference)


@dataclass(frozen=True, slots=True)
class FourObserverAffineClock:
    """Four weighted outputs under one source-observed macro action.

    The right forcing is the actual -198J correction. The other three
    channels are *formal* comparison observers weighted by the same 160
    clock, not additional forces to add to the integer successor. Algebraic
    composition does not authenticate repetition of an actual source orbit.
    """

    width: int
    steps: int
    multiplier: int
    right_forcing: int
    left_forcing: int
    right_overflow_forcing: int
    mirrored_left_overflow_forcing: int

    @property
    def modulus(self) -> int:
        return defect_modulus(self.width)

    @classmethod
    def identity(cls, width: int) -> FourObserverAffineClock:
        defect_modulus(width)
        return cls(width, 0, 1, 0, 0, 0, 0)

    @classmethod
    def from_emission(cls, emission: FourObserverEmission) -> FourObserverAffineClock:
        width = emission.defect.width
        modulus = defect_modulus(width)
        br = emission.right_overflow_defects(width, factor=2)
        bl = emission.mirrored_left_overflow_defects(width, factor=2)
        # Use a fixed 4:1 chronological comparison weighting. Only the
        # right full carry output is the physical radial force.
        return cls(
            width,
            1,
            160 % modulus,
            (-198 * emission.right) % modulus,
            (-198 * emission.left) % modulus,
            (4 * br[0] + br[1]) % modulus,
            (4 * bl[0] + bl[1]) % modulus,
        )

    def then(self, later: FourObserverAffineClock) -> FourObserverAffineClock:
        if type(later) is not FourObserverAffineClock or self.width != later.width:
            raise ValueError("incompatible four-observer temporal join")
        m = self.modulus
        return FourObserverAffineClock(
            self.width,
            self.steps + later.steps,
            later.multiplier * self.multiplier % m,
            (later.multiplier * self.right_forcing + later.right_forcing) % m,
            (later.multiplier * self.left_forcing + later.left_forcing) % m,
            (
                later.multiplier * self.right_overflow_forcing
                + later.right_overflow_forcing
            )
            % m,
            (
                later.multiplier * self.mirrored_left_overflow_forcing
                + later.mirrored_left_overflow_forcing
            )
            % m,
        )

    def power(self, repetitions: int) -> FourObserverAffineClock:
        """Repeat this supplied affine action algebraically, without source authority."""
        if type(repetitions) is not int or repetitions < 0:
            raise ValueError("invalid four-observer repetition")
        return binary_power(
            self,
            repetitions,
            identity=self.identity(self.width),
            compose=lambda first, second: first.then(second),
        ).value

    @property
    def directional_contrast(self) -> int:
        return (self.right_forcing - self.left_forcing) % self.modulus


def projected_period_profiles(
    observations: Sequence[FourObserverEmission], max_lag: int
) -> dict[str, dict[str, object]]:
    """All suffix periods from a single mismatch/valuation pass per lag.

    Unlike scanning every width independently, an equality comparison is
    computed once as the number of trailing agreeing decimal columns. For a
    given width w the same comparison disagrees iff agreement < w.  The
    last violating index gives the exact earliest sampled periodic suffix.
    """
    if not observations:
        raise ValueError("cannot minimize empty four-observer history")
    if type(max_lag) is not int or max_lag < 1:
        raise ValueError("invalid comparison lag")
    width = observations[0].defect.width
    if any(
        type(row) is not FourObserverEmission or row.defect.width != width
        for row in observations
    ):
        raise ValueError("all observations must have the same suffix precision")
    names = ("right", "left", "joint", "difference", "four")
    size = len(observations)
    max_period = min(max_lag, size - 1)
    # For each width retain the best supported observed candidate, and the
    # lags that match over the complete finite window.
    best: dict[str, list[dict[str, int] | None]] = {
        name: [None] * (width + 1) for name in names
    }
    complete: dict[str, list[list[int]]] = {
        name: [[] for _ in range(width + 1)] for name in names
    }
    for lag in range(1, max_period + 1):
        last_at_depth = {name: [-1] * width for name in names}
        for i in range(lag, size):
            current = observations[i]
            previous = observations[i - lag]
            right = _trailing_agreement(current.right, previous.right, width)
            left = _trailing_agreement(current.left, previous.left, width)
            difference = _trailing_agreement(
                current.difference, previous.difference, width
            )
            joint = min(right, left)
            phase = (
                width
                if (
                    current.right_overflow == previous.right_overflow
                    and current.mirrored_left_overflow
                    == previous.mirrored_left_overflow
                )
                else 0
            )
            depths = (right, left, joint, difference, min(joint, phase))
            for name, depth in zip(names, depths, strict=True):
                if depth < width:
                    last_at_depth[name][depth] = i
        for name in names:
            last = -1
            for w in range(1, width + 1):
                last = max(last, last_at_depth[name][w - 1])
                if last == -1:
                    complete[name][w].append(lag)
                if lag > size // 3:
                    continue
                start = max(0, last - lag + 1)
                if size - start < 3 * lag:
                    continue
                tail_candidate = {
                    "observed_lag": lag,
                    "sample_start": start,
                    "samples": size - start,
                }
                older = best[name][w]
                if older is None or (start, lag) < (
                    older["sample_start"],
                    older["observed_lag"],
                ):
                    best[name][w] = tail_candidate
    out: dict[str, dict[str, object]] = {}
    for name in names:
        history: list[dict[str, object]] = []
        previous_key: tuple[int | None, int | None] | None = None
        for w in range(1, width + 1):
            candidate = best[name][w]
            key = (
                candidate["observed_lag"] if candidate is not None else None,
                candidate["sample_start"] if candidate is not None else None,
            )
            if previous_key != key:
                history.append(
                    {"suffix_digits": w, "observed_tail_candidate": candidate}
                )
                previous_key = key
        out[name] = {
            "finite_window_period_lags": complete[name][width],
            "observed_tail_candidate": best[name][width],
            "suffix_period_hierarchy": history,
        }
    return out
