"""Primitive cyclic Collatz quotient, with an exact Laurent seam.

For phase i, delta = 3**k-2**m and J_i are the primitive row coefficients.
D_i = delta*x + J_i transports by 3**p/2.  In radix b=2 or 10 the
moving-cut numerator is

    b**t*x_t = ((b//2)**t * 3**k_t * D_0 - b**t * J_{i+t}) / delta.

The primitive row and phase are source-independent. Apply them only after
the physical issuer checks the receiving source and accepted horizon.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from functools import lru_cache

from number_compiler.arithmetic.automata.affine_port_action import AffinePortAction
from number_compiler.arithmetic.automata.word_period import (
    canonical_primitive_text_rotation,
    least_rotation_index,
    primitive_period,
)


def _nonnegative(value: int, name: str) -> None:
    if type(value) is not int or value < 0:
        raise ValueError(f"{name} must be a nonnegative integer")


def _radix(radix: int) -> None:
    if type(radix) is not int or radix not in (2, 10):
        raise ValueError("cyclic diagonal radix must be 2 or 10")


def _exact_divide(numerator: int, denominator: int) -> int:
    quotient, remainder = divmod(numerator, denominator)
    if remainder:
        raise ArithmeticError("cyclic Laurent seam is not integral")
    return quotient


@dataclass(frozen=True, slots=True)
class CyclicNecklace:
    """One source-independent primitive orbit, shared by every entry phase."""

    word: str
    delta: int = field(init=False)
    offsets: tuple[int, ...] = field(init=False, repr=False)
    odd_prefix: tuple[int, ...] = field(init=False, repr=False)

    def __post_init__(self) -> None:
        word = self.word
        if type(word) is not str or not word or word.strip("01"):
            raise ValueError("cyclic necklace requires a binary word")
        if primitive_period(word)[0] != len(word):
            raise ValueError("cyclic necklace must be primitive")
        if least_rotation_index(word):
            raise ValueError("cyclic necklace must be canonically rotated")
        prefix = [0]
        j = 0
        for i, p in enumerate(word):
            bit = int(p)
            prefix.append(prefix[-1] + bit)
            j = (3 * j + (1 << i)) if bit else j
        delta = 3 ** prefix[-1] - (1 << len(word))
        offsets: list[int] = []
        for p in word:
            offsets.append(j)
            bit = int(p)
            j = _exact_divide((3 if bit else 1) * j - delta * bit, 2)
        if j != offsets[0]:
            raise ArithmeticError("cyclic Laurent offsets failed to close")
        object.__setattr__(self, "delta", delta)
        object.__setattr__(self, "offsets", tuple(offsets))
        object.__setattr__(self, "odd_prefix", tuple(prefix))

    def odds(self, phase: int, steps: int) -> int:
        copies, tail = divmod(steps, len(self.word))
        end = phase + tail
        prefix = self.odd_prefix
        total = copies * prefix[-1] - prefix[phase]
        if end >= len(self.word):
            return total + prefix[-1] + prefix[end - len(self.word)]
        return total + prefix[end]


@lru_cache(maxsize=256)
def _small_necklace(canonical: str) -> CyclicNecklace:
    # Static finite grammar only (period <= 8), never a source or horizon cache.
    return CyclicNecklace(canonical)


@dataclass(frozen=True, slots=True)
class CyclicLaurentAction:
    necklace: CyclicNecklace
    phase: int

    def __post_init__(self) -> None:
        if (
            type(self.necklace) is not CyclicNecklace
            or type(self.phase) is not int
            or not 0 <= self.phase < len(self.necklace.word)
        ):
            raise ValueError("invalid cyclic Laurent phase")

    @classmethod
    def from_word(cls, word: str) -> CyclicLaurentAction:
        if type(word) is not str or not word:
            raise ValueError("cyclic Laurent action requires a binary word")
        return _small_action(word) if len(word) <= 8 else _uncached_action(word)

    @property
    def word(self) -> str:
        word = self.necklace.word
        return word[self.phase :] + word[: self.phase]

    @property
    def delta(self) -> int:
        return self.necklace.delta

    @property
    def offset(self) -> int:
        return self.necklace.offsets[self.phase]

    def offset_at(self, steps: int) -> int:
        return self.necklace.offsets[(self.phase + steps) % len(self.necklace.word)]

    def rotated(self, steps: int) -> CyclicLaurentAction:
        _nonnegative(steps, "phase advance")
        return CyclicLaurentAction(
            self.necklace, (self.phase + steps) % len(self.necklace.word)
        )

    def odds(self, steps: int) -> int:
        _nonnegative(steps, "prefix length")
        return self.necklace.odds(self.phase, steps)

    def ticks(self, steps: int) -> int:
        return steps + self.odds(steps)

    def steps_for_ticks(self, ticks: int) -> int:
        """Invert the physical clock using complete motifs and a bounded tail."""
        _nonnegative(ticks, "physical ticks")
        period = len(self.necklace.word)
        copies, tail = divmod(ticks, period + self.necklace.odd_prefix[-1])
        lo, hi = 0, period - 1
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if self.ticks(mid) <= tail:
                lo = mid
            else:
                hi = mid - 1
        return copies * period + lo

    def defect(self, source: int) -> int:
        return self.delta * source + self.offset

    def prefix_offset(self, steps: int, gain: int) -> int:
        """Laurent innovation (gain*J_i - 2**t*J_j)/delta, no SLP power."""
        return _exact_divide(
            gain * self.offset - (self.offset_at(steps) << steps), self.delta
        )

    def point(self, defect: int, steps: int, gain: int) -> tuple[int, int]:
        """Exact endpoint and transported centered defect, for a guarded inlet."""
        _nonnegative(steps, "guarded point length")
        if defect and (defect & -defect).bit_length() - 1 < steps:
            raise ValueError("cyclic point exceeds its dyadic source guard")
        following = gain * (defect >> steps)
        return _exact_divide(following - self.offset_at(steps), self.delta), following

    def successor_sum(self, steps: int, gain: int) -> tuple[int, int]:
        """Exact affine sum of normalized successors with denominator 2**steps.

        A geometric sum over primitive copies, plus one bounded tail; no
        repeated parity factors or historical sum fields are folded.
        """
        m = len(self.necklace.word)
        copies, tail = divmod(steps, m)

        def phase_sum(length: int) -> int:
            # Compute only the finite motif's response.
            total = 0
            current_gain = 1
            word = self.word
            for bit in word[:length]:
                if bit == "1":
                    current_gain *= 3
                total = 2 * total + current_gain
            return total

        copy_gain = gain // 3 ** self.odds(tail)
        geometric = _exact_divide(copy_gain - (1 << (copies * m)), self.delta)
        sum_gain = (phase_sum(m) * geometric << tail) + copy_gain * phase_sum(tail)
        offsets = self.necklace.offsets
        sum_j = copies * sum(offsets) + sum(
            self.offset_at(i) for i in range(1, tail + 1)
        )
        sum_offset = _exact_divide(
            self.offset * sum_gain - (sum_j << steps), self.delta
        )
        return sum_gain, sum_offset

    def initial_state(
        self, source: int, radix: int, precision: int
    ) -> CyclicDiagonalState:
        """Algebraic finite-ring inlet; physical admission is checked by caller."""
        _radix(radix)
        _nonnegative(precision, "diagonal precision")
        ring = radix**precision
        # In binary delta is a unit.  Decimal uses a division lift even when
        # delta shares factors with ten.  This is required for signed delta too.
        modulus = ring if radix == 2 else abs(self.delta) * ring
        seam = 1 % ring
        residue = (self.delta * (source % ring) + self.offset * seam) % modulus
        return CyclicDiagonalState(self, radix, precision, modulus, residue, seam)


def _uncached_action(word: str) -> CyclicLaurentAction:
    if word.strip("01"):
        raise ValueError("cyclic Laurent action requires a binary word")
    canonical, phase, _ = canonical_primitive_text_rotation(word)
    necklace = (
        _small_necklace(canonical) if len(canonical) <= 8 else CyclicNecklace(canonical)
    )
    return CyclicLaurentAction(necklace, phase)


@lru_cache(maxsize=512)
def _small_action(word: str) -> CyclicLaurentAction:
    # 510 possible nonempty words of length <= 8. Static law, not source work.
    return _uncached_action(word)


@dataclass(frozen=True, slots=True)
class CyclicDiagonalState:
    """Successor-closed response in a fixed precision ring, not a time trace.

    Equality includes phase, homogeneous residue AND seam clock. It is a
    sufficient right congruence, not asserted to be globally Moore-minimal.
    The residue and seam are both bounded by the requested precision.
    """

    action: CyclicLaurentAction
    radix: int
    precision: int
    modulus: int
    residue: int
    seam: int

    def advance(self, steps: int) -> CyclicDiagonalState:
        _nonnegative(steps, "diagonal advance")
        if not steps:
            return self
        mod = self.modulus
        gain = pow(3, self.action.odds(steps), mod)
        if self.radix == 10:
            gain = gain * pow(5, steps, mod) % mod
        following = self.action.rotated(steps)
        residue = gain * self.residue % mod
        lifted_seam = self.seam * pow(self.radix, steps, mod) % mod
        # Quotient the artificial decimal division lift too. Changing the
        # seam by a ring multiple requires exactly the matching J correction.
        # The physical numerator and every future numerator then agree.
        ring = mod if self.radix == 2 else mod // abs(self.action.delta)
        seam = lifted_seam % ring
        residue = (residue - (lifted_seam - seam) * following.offset) % mod
        return CyclicDiagonalState(
            following, self.radix, self.precision, mod, residue, seam
        )

    def numerator_residue(self) -> int:
        difference = self.residue - self.seam * self.action.offset
        delta = self.action.delta
        if self.radix == 2:
            if self.modulus == 1:
                return 0
            return difference * pow(delta, -1, self.modulus) % self.modulus
        signed = difference if delta > 0 else -difference
        return _exact_divide(signed % self.modulus, abs(delta))

    def band(self, cut: int, width: int) -> int:
        """Band in moving numerator coordinates (the physical cut is cut-t)."""
        _nonnegative(cut, "diagonal cut")
        _nonnegative(width, "diagonal width")
        if cut + width > self.precision:
            raise ValueError("band exceeds the diagonal ring precision")
        place: int = self.radix**cut
        modulus: int = self.radix**width
        return self.numerator_residue() // place % modulus


@dataclass(frozen=True, slots=True)
class CyclicDefectGuard:
    """Pointed source and exact first mismatch, separate from response identity."""

    action: CyclicLaurentAction
    source: int
    defect: int = field(init=False)
    first_mismatch: int | None = field(init=False)

    def __post_init__(self) -> None:
        if type(self.source) is not int or self.source <= 0:
            raise ValueError("cyclic defect requires a positive physical source")
        defect = self.action.defect(self.source)
        object.__setattr__(self, "defect", defect)
        object.__setattr__(
            self,
            "first_mismatch",
            (defect & -defect).bit_length() - 1 if defect else None,
        )

    def require_steps(self, steps: int) -> None:
        _nonnegative(steps, "guarded future length")
        if self.first_mismatch is not None and steps > self.first_mismatch:
            raise ValueError("cyclic projection exceeds its physical guard")

    def point(self, steps: int, gain: int) -> tuple[int, int]:
        self.require_steps(steps)
        return self.action.point(self.defect, steps, gain)

    def state(self, steps: int, radix: int, precision: int) -> CyclicDiagonalState:
        self.require_steps(steps)
        return self.action.initial_state(self.source, radix, precision).advance(steps)

    def rebased_state(
        self, steps: int, radix: int, precision: int
    ) -> CyclicDiagonalState:
        """Remove the consumed cut using the guard BEFORE building a modulus.

        D is divisible by 2**steps. Once that exact division has been taken,
        only the demanded physical precision (and the fixed delta lift) is
        needed; a large accepted horizon does not enlarge the ring.
        """
        self.require_steps(steps)
        _radix(radix)
        _nonnegative(precision, "diagonal precision")
        return _rebased_defect_state(self.action, self.defect, steps, radix, precision)

    def exact_lower_response(
        self, steps: int, cut: int, gain: int
    ) -> tuple[AffinePortAction, int]:
        """Exact binary lower response and surviving seam, before upper evaluation."""
        self.require_steps(steps)
        _nonnegative(cut, "moving cut")
        if cut < steps:
            raise ValueError("moving cut discards guarded low bits")
        lower = self.source & ((1 << cut) - 1)
        lower_endpoint, _ = self.action.point(self.action.defect(lower), steps, gain)
        carry, low = divmod(lower_endpoint, 1 << (cut - steps))
        return AffinePortAction(None, gain, carry), low

    def upper_response(
        self, steps: int, radix: int, cut: int, width: int
    ) -> AffinePortAction:
        """Minimal all-upper-inlet affine response at the demanded precision.

        Guard inheritance: radix**cut is divisible by 2**steps when cut>=steps.
        Only the lower source modulo radix**cut enters the carry.  The response
        is computed before any upper child or full affine numerator is built.
        """
        self.require_steps(steps)
        _radix(radix)
        _nonnegative(cut, "moving cut")
        if cut < steps or type(width) is not int or width < 1:
            raise ValueError("moving cut discards guarded bits or lacks precision")
        # The lower inlet is congruent to the authenticated source mod 2**steps.
        # Divide that centered defect BEFORE choosing the physical output ring.
        # The consumed diagonal cut must not inflate the modular power precision.
        lower = (
            self.source if cut >= self.source.bit_length() else self.source % radix**cut
        )
        physical_cut = cut - steps
        state = _rebased_defect_state(
            self.action, self.action.defect(lower), steps, radix, physical_cut + width
        )
        mod: int = radix**width
        gain: int = pow(3, self.action.odds(steps), mod)
        if radix == 10:
            gain = gain * pow(5, steps, mod) % mod
        return AffinePortAction.reduced(mod, gain, state.band(physical_cut, width))


def _rebased_defect_state(
    action: CyclicLaurentAction, defect: int, steps: int, radix: int, precision: int
) -> CyclicDiagonalState:
    """Project an admitted Laurent defect after exact division by 2**steps."""
    if defect and (defect & -defect).bit_length() - 1 < steps:
        raise ValueError("rebased defect exceeds its physical guard")
    following = action.rotated(steps)
    ring: int = radix**precision
    modulus: int = ring if radix == 2 else abs(following.delta) * ring
    seam = 1 % ring
    residue = (
        (pow(3, action.odds(steps), modulus) * ((defect >> steps) % modulus)) % modulus
        if seam
        else 0
    )
    return CyclicDiagonalState(following, radix, precision, modulus, residue, seam)
