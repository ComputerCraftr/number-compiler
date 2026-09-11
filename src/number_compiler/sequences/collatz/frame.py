"""Radix-4 fixed-point and rational-root frames for accelerated Collatz.

For the accelerated odd map

    H(n) = (3*n + 1) / 2**v2(3*n+1),

the low radix-4 ``1`` run is the 2-adic fixed-point frame ``-1/3``.  If

    n = (4**q - 1)/3 + 4**q*m,

then ``3*n+1 = 4**q(3*m+1)``.  The unbounded ``q`` contributes only to the
current valuation and is gauge for the accelerated target.

After stripping that frame the next valuation is a first-mismatch query against
a rational 2-adic root.  The old h=2 roots ``-4/9`` and ``-5/9`` happen to have
period-three radix-4 expansions, but production no longer materializes or
composes those periods.  ``RationalPadicRootGerm`` handles the general root
``-c/3**h`` directly, skipping a constant radix-4 run from
``v2(3*c - 3**h*d)`` and updating the root constant by an exact right shift.
At the first mismatch ``PadicAngularBoundaryGerm`` rewrites the normalized odd
discrepancy as an affine map of the unconsumed higher suffix.
``CollatzAffineSuffixGerm`` then pulls subsequent roots back through that affine
map without constructing intermediate Collatz digit words or exponentially long
root periods.

This is an exact local projection engine, not a claimed finite-state solution of
Collatz.  Binary temporal closure of the branching affine/root descriptors is a
separate theorem frontier.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.automata.program_word import (
    EMPTY,
    CanonicalWord,
    iter_runs,
    word_metrics,
)
from number_compiler.arithmetic.fields.adic_morphism import PadicRadialQuotient
from number_compiler.arithmetic.fields.morphism_core import AffineCocycle
from number_compiler.arithmetic.fields.radix import bit_width, digits_lsd
from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.sequences.collatz.root_germs import (
    PadicAngularBoundaryGerm,
    RationalPadicRootGerm,
    RationalPadicRootMismatch,
)

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.germ_cache import CollatzGermTransitionCache
    from number_compiler.sequences.collatz.power import CollatzEventNode


# Explicit event endpoints cross the same output boundary as whole orbits.


def _sentinel_prefix_mod3(quarters: int, precision: int) -> int:
    """Return ``(4**q-1)/3 mod 3**precision`` in O(log q) arithmetic.

    Computing ``4**q`` modulo one extra factor of three makes the exact integer
    division by three available without constructing ``4**q`` itself.
    """
    if type(quarters) is not int or type(precision) is not int:
        raise TypeError("Collatz sentinel frame requires exact integers")
    q = quarters
    if q < 0 or not 0 < precision <= 40:
        raise ValueError((q, precision))
    modulus = 3**precision
    lifted = pow(4, q, 3 * modulus)
    if (lifted - 1) % 3:
        raise AssertionError((q, precision, lifted))
    return int(((lifted - 1) // 3) % modulus)


@dataclass(frozen=True, slots=True)
class CollatzRadix4FrameFactorization:
    """Exact one-step factorization around the 2-adic root ``-1/3``.

    ``frame_depth`` is diagnostic/gauge information.  It is intentionally not
    part of the canonical future-state key: the accelerated successor depends
    only on ``tail`` and ``local_shift``.
    """

    frame_depth: int
    local_shift: int
    tail: int
    valuation: int
    successor: int

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (
                self.frame_depth,
                self.local_shift,
                self.tail,
                self.valuation,
                self.successor,
            )
        ):
            raise TypeError("radix-4 frame fields require exact integers")
        if self.frame_depth < 0 or self.local_shift not in (0, 1):
            raise ValueError(self)
        if self.tail < 0 or self.valuation != 2 * self.frame_depth + self.local_shift:
            raise ValueError(self)
        expected = (3 * self.tail + 1) >> self.local_shift
        if expected != self.successor or not (self.successor & 1):
            raise ValueError(self)

    @property
    def canonical_future_key(self) -> tuple[object, ...]:
        return ("collatz-radix4-fixed-frame", self.local_shift, self.tail)


def collatz_radix4_frame_factorization(value: int) -> CollatzRadix4FrameFactorization:
    """Factor one positive odd source into removable radix-4 sentinel frames."""
    if type(value) is not int:
        raise TypeError("radix-4 Collatz frame requires an exact integer")
    if value <= 0 or not (value & 1):
        raise ValueError("radix-4 Collatz frame requires a positive odd source")
    tail = value
    q = 0
    while tail and (tail & 3) == 1:
        tail >>= 2
        q += 1
    local = v2_positive(3 * tail + 1)
    if local not in (0, 1):
        # Once every low radix-4 sentinel 1 is stripped, another full factor 4
        # is impossible.  This is the exact two-sector frame theorem.
        raise AssertionError((value, q, tail, local))
    valuation = 2 * q + local
    direct = v2_positive(3 * value + 1)
    if direct != valuation:
        raise AssertionError((value, q, tail, local, valuation, direct))
    successor = (3 * tail + 1) >> local
    return CollatzRadix4FrameFactorization(q, local, tail, valuation, successor)


def strip_radix4_fixed_point_digits(
    digits: Sequence[int],
) -> tuple[int, tuple[int, ...]]:
    """Drop the maximal low run of radix-4 sentinel digit ``1``."""
    ds = tuple(digits)
    if any(type(digit) is not int for digit in ds):
        raise TypeError("radix-4 digits require exact integers")
    if not ds or any(not 0 <= d < 4 for d in ds):
        raise ValueError(digits)
    q = 0
    while q < len(ds) and ds[q] == 1:
        q += 1
    return q, ds[q:]


def strip_radix4_fixed_point_word(word: CanonicalWord) -> tuple[int, CanonicalWord]:
    """Drop the first canonical run when it is the radix-4 sentinel run.

    Returns ``(frame_depth, tail_word)`` without expanding the run length.
    The empty tail represents the all-sentinel finite source.
    """
    from number_compiler.arithmetic.automata.program_word import (
        EMPTY,
        CanonicalWord,
        first_run,
        slice_runs,
    )

    if not isinstance(word, CanonicalWord):
        raise TypeError(type(word))
    if not word.run_count:
        return 0, EMPTY
    first = first_run(word)
    if first.symbol != 1:
        return 0, word
    q = int(first.run_length)
    if word.run_count == 1:
        return q, EMPTY
    return q, slice_runs(word, 1, word.run_count - 1)


@dataclass(frozen=True, slots=True)
class CollatzAffineSuffixGerm:
    """Exact odd Collatz state as an affine map of an unconsumed radix-4 suffix.

    ``value = multiplier * suffix + offset``.  Successor projection pulls the
    next 2-adic root back through this affine map.  Whenever an actual boundary
    query is needed, its odd coefficient is a power of three and the generic
    :class:`RationalPadicRootGerm` consumes the source suffix by runs.

    This removes both intermediate Collatz digit materialization and the
    exponentially growing literal root periods.  It is still a one-successor
    projector; binary temporal closure must be proved separately.
    """

    multiplier: int
    offset: int
    suffix: CanonicalWord
    logical_steps: int = 0

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (
                self.multiplier,
                self.offset,
                self.logical_steps,
            )
        ):
            raise TypeError("Collatz affine suffix fields require exact integers")
        if self.multiplier < 0 or self.offset < 0 or self.logical_steps < 0:
            raise ValueError(self)
        if not isinstance(self.suffix, CanonicalWord):
            raise TypeError(type(self.suffix))
        if self.suffix.length == 0 and self.multiplier:
            object.__setattr__(self, "multiplier", 0)

    @property
    def cocycle(self) -> AffineCocycle[int]:
        return AffineCocycle(self.multiplier, self.offset)

    @classmethod
    def from_word(cls, word: CanonicalWord) -> CollatzAffineSuffixGerm:
        if not isinstance(word, CanonicalWord) or not word.length:
            raise ValueError("positive odd radix-4 source word required")
        # LSD-first odd sources have first digit 1 or 3.
        first = next(iter_runs(word))[0]
        if first not in (1, 3):
            raise ValueError("accelerated Collatz source must be odd")
        return cls(1, 0, word, 0)

    @staticmethod
    def _pow3_exponent(value: int) -> int:
        if type(value) is not int:
            raise TypeError("power-of-three recognition requires an exact integer")
        if value <= 0:
            raise ValueError(value)
        h = 0
        while value % 3 == 0:
            value //= 3
            h += 1
        if value != 1 or h <= 0:
            raise ValueError(
                "pulled-back Collatz root denominator is not a positive power of three"
            )
        return h

    def next_step(self) -> CollatzAffineSuffixAdvance:
        if self.multiplier == 0:
            numerator = 3 * self.offset + 1
            valuation = v2_positive(numerator)
            target = CollatzAffineSuffixGerm(
                0, numerator >> valuation, EMPTY, self.logical_steps + 1
            )
            return CollatzAffineSuffixAdvance(valuation, target, 0, None, None)

        successor = self.cocycle.then(
            AffineCocycle(3, 1),
            multiply=lambda a, b: a * b,
            add=lambda a, b: a + b,
        )
        alpha = successor.multiplier
        beta = successor.addend
        alpha_v2 = v2_positive(alpha)
        beta_v2 = v2_positive(beta)
        if beta_v2 < alpha_v2:
            valuation = beta_v2
            target = CollatzAffineSuffixGerm(
                alpha >> valuation,
                beta >> valuation,
                self.suffix,
                self.logical_steps + 1,
            )
            return CollatzAffineSuffixAdvance(valuation, target, valuation, None, None)

        base_shift = alpha_v2
        odd_denominator = alpha >> base_shift
        h = self._pow3_exponent(odd_denominator)
        root = RationalPadicRootGerm(h, beta >> base_shift)
        mismatch, suffix = root.first_mismatch_word(self.suffix)
        angular = PadicAngularBoundaryGerm.from_mismatch(root, mismatch)
        valuation = base_shift + angular.valuation
        target = CollatzAffineSuffixGerm(
            angular.multiplier,
            angular.offset,
            suffix,
            self.logical_steps + 1,
        )
        return CollatzAffineSuffixAdvance(valuation, target, base_shift, root, mismatch)

    @property
    def algebraic_key(self) -> tuple[object, ...]:
        """Exact future state before the nonsemantic logical-time action."""
        return (
            "collatz-affine-suffix-algebraic",
            self.multiplier,
            self.offset,
            self.suffix.node_id,
            self.suffix.length,
        )

    @property
    def canonical_key(self) -> tuple[object, ...]:
        # CanonicalWord is structurally interned; the source cursor is execution
        # state, not claimed as a finite semantic quotient.
        return (
            "collatz-affine-suffix-germ",
            self.multiplier,
            self.offset,
            self.suffix.node_id,
            self.suffix.length,
            self.logical_steps,
        )

    @property
    def description_bits(self) -> int:
        wm = word_metrics(self.suffix)
        return (
            bit_width(self.multiplier)
            + bit_width(self.offset)
            + bit_width(self.logical_steps)
            + int(wm["description_bits"])
        )


@dataclass(frozen=True, slots=True)
class CollatzAffineSuffixAdvance:
    valuation: int
    target: CollatzAffineSuffixGerm
    fixed_v2: int
    root: RationalPadicRootGerm | None
    mismatch: RationalPadicRootMismatch | None

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (
                self.valuation,
                self.fixed_v2,
            )
        ):
            raise TypeError("Collatz affine advance requires exact integers")
        if self.valuation <= 0 or self.fixed_v2 < 0 or self.fixed_v2 > self.valuation:
            raise ValueError(self)
        if (self.root is None) != (self.mismatch is None):
            raise ValueError(self)


def collatz_affine_suffix_valuations_word(
    word: CanonicalWord,
    steps: int,
    *,
    transition_cache: CollatzGermTransitionCache | None = None,
) -> tuple[tuple[int, ...], CollatzAffineSuffixGerm]:
    """Project accelerated valuations without constructing successor digit words."""
    from number_compiler.sequences.collatz.germ_cache import CollatzGermTransitionCache

    if type(steps) is not int:
        raise TypeError("Collatz valuation count must be an exact integer")
    if steps < 0:
        raise ValueError(steps)
    germ = CollatzAffineSuffixGerm.from_word(word)
    if transition_cache is None:
        transition_cache = CollatzGermTransitionCache()
    if not isinstance(transition_cache, CollatzGermTransitionCache):
        raise TypeError(type(transition_cache))
    out: list[int] = []
    for _ in range(steps):
        advance = transition_cache.advance(germ)
        out.append(advance.valuation)
        germ = advance.target
        if germ.multiplier == 0 and germ.offset == 1:
            # H(1)=1 with valuation two; retain exact fixed point semantics if
            # the caller asks for more projected steps.
            pass
    return tuple(out), germ


def collatz_affine_suffix_valuations_value(
    value: int,
    steps: int,
    *,
    transition_cache: CollatzGermTransitionCache | None = None,
) -> tuple[tuple[int, ...], CollatzAffineSuffixGerm]:
    from number_compiler.arithmetic.automata.program_word import from_values

    if type(value) is not int or type(steps) is not int:
        raise TypeError("Collatz value and valuation count require exact integers")
    if value <= 0 or not (value & 1):
        raise ValueError(value)
    return collatz_affine_suffix_valuations_word(
        from_values(digits_lsd(value, 4)),
        steps,
        transition_cache=transition_cache,
    )


@dataclass(frozen=True, slots=True)
class CollatzAffineSuffixEventProjection:
    """Direct root-germ -> lazy event-DAG projection, with no parity itinerary."""

    root: CollatzEventNode
    target: CollatzAffineSuffixGerm
    events: int
    composition_operations: int

    def __post_init__(self) -> None:
        if type(self.events) is not int or type(self.composition_operations) is not int:
            raise TypeError("Collatz event projection counts require exact integers")
        if self.events < 0 or self.composition_operations < 0:
            raise ValueError(self)


@dataclass(frozen=True, slots=True)
class CollatzFutureValuationRoot:
    """Sector-specific 2-adic root controlling the *next* valuation."""

    local_shift: int

    def __post_init__(self) -> None:
        if type(self.local_shift) is not int:
            raise TypeError("Collatz valuation-root sector must be an exact integer")
        if self.local_shift not in (0, 1):
            raise ValueError(self.local_shift)

    @property
    def constant(self) -> int:
        return 3 + (1 << self.local_shift)  # 4 or 5 in 9*m + constant

    @property
    def radix4_period(self) -> tuple[int, int, int]:
        return (0, 3, 1) if self.local_shift == 0 else (3, 0, 2)

    def root_residue(self, bits: int) -> int:
        if type(bits) is not int:
            raise TypeError("Collatz valuation-root precision must be exact")
        if not 0 < bits <= 64:
            raise ValueError("Collatz valuation-root precision must fit one limb")
        modulus = 1 << bits
        return (-self.constant * pow(9, -1, modulus)) % modulus

    def next_valuation_from_tail(self, tail: int) -> int:
        if type(tail) is not int:
            raise TypeError("Collatz valuation-root tail must be an exact integer")
        if tail < 0:
            raise ValueError(tail)
        result = v2_positive(9 * tail + self.constant) - self.local_shift
        if result <= 0:
            raise AssertionError((self, tail, result))
        return result

    @property
    def rational_root(self) -> RationalPadicRootGerm:
        return RationalPadicRootGerm(2, self.constant)

    def next_valuation_from_digits(self, digits: Sequence[int]) -> int:
        return self.rational_root.valuation_from_digits(digits) - self.local_shift

    def next_valuation_from_word(self, word: CanonicalWord) -> int:
        if not isinstance(word, CanonicalWord):
            raise TypeError(type(word))
        return self.rational_root.valuation_from_word(word) - self.local_shift

    @property
    def canonical_key(self) -> tuple[object, ...]:
        # The period-three expansion is a diagnostic identity of the h=2 case,
        # not retained semantic state.
        return (
            "collatz-future-valuation-root",
            self.local_shift,
            self.rational_root.canonical_key,
        )


@dataclass(frozen=True, slots=True)
class CollatzTwoValuationFrameSummary:
    """Two consecutive accelerated valuations from one radix-4 source frame.

    The first valuation is the ordinary ``-1/3`` sentinel depth.  The second
    is evaluated by the symbolic rational-root germ and therefore does not
    require construction of the intermediate Collatz successor.
    """

    frame_depth: int
    local_shift: int
    current_valuation: int
    next_valuation: int

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (
                self.frame_depth,
                self.local_shift,
                self.current_valuation,
                self.next_valuation,
            )
        ):
            raise TypeError("Collatz valuation summary requires exact integers")
        if self.frame_depth < 0 or self.local_shift not in (0, 1):
            raise ValueError(self)
        if self.current_valuation != 2 * self.frame_depth + self.local_shift:
            raise ValueError(self)
        if self.next_valuation <= 0:
            raise ValueError(self)

    @property
    def canonical_future_key(self) -> tuple[object, ...]:
        # The removed frame depth is gauge.  The surviving sector and the next
        # boundary valuation are the two-step theorem payload.
        return (
            "collatz-two-valuation-fixed-frame",
            self.local_shift,
            self.next_valuation,
        )


def normalize_collatz_frame_word(
    word: CanonicalWord,
) -> tuple[int, int, CanonicalWord]:
    """Return frame depth, residual phase and tail without a root query."""
    from number_compiler.arithmetic.automata.program_word import first_run

    if not isinstance(word, CanonicalWord) or not word.length:
        raise ValueError("positive odd Collatz source required")
    if first_run(word).symbol not in (1, 3):
        raise ValueError("positive odd Collatz source required")
    q, tail = strip_radix4_fixed_point_word(word)
    if not tail.length:
        local = 0
    else:
        first = first_run(tail)
        if first.symbol not in (0, 2, 3):
            raise ValueError("tail is not fixed-point-frame normalized")
        local = int(first.symbol == 3)
    return q, local, tail


def collatz_two_valuation_frame_word(
    word: CanonicalWord,
) -> CollatzTwoValuationFrameSummary:
    """Project ``(k_t,k_{t+1})`` from one canonical radix-4 RLE/SLP word.

    No successor digit word, multiplication carry row, or parity itinerary is
    constructed.  ``word`` is LSD-first and must encode a positive odd integer.
    """
    q, local, tail = normalize_collatz_frame_word(word)
    current = 2 * q + local
    root = CollatzFutureValuationRoot(local)
    # Empty tail is the integer zero.  Its implicit high-zero word is handled
    # exactly by the identity periodic summary.
    nxt = root.next_valuation_from_word(tail)
    return CollatzTwoValuationFrameSummary(q, local, current, nxt)


def collatz_two_valuation_frame_value(value: int) -> CollatzTwoValuationFrameSummary:
    """Integer differential wrapper for :func:`collatz_two_valuation_frame_word`."""
    from number_compiler.arithmetic.automata.program_word import from_values

    if type(value) is not int:
        raise TypeError("Collatz valuation frame requires an exact integer")
    if value <= 0 or not (value & 1):
        raise ValueError(value)
    return collatz_two_valuation_frame_word(from_values(digits_lsd(value, 4)))


@dataclass(frozen=True, slots=True)
class CollatzFixedPointPadicFrame:
    """3-adic innovation after quotienting the removable radix-4 frame.

    The current full valuation is used only to choose the frame transformation.
    Its unbounded ``q=floor(k/2)`` part is not retained.  ``local_shift=k mod 2``
    is the two-sector action that survives frame normalization.
    """

    precision: int
    tail_residue: int
    local_shift: int

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (
                self.precision,
                self.tail_residue,
                self.local_shift,
            )
        ):
            raise TypeError("Collatz fixed-point frame requires exact integers")
        precision = self.precision
        if not 0 < precision <= 40:
            raise ValueError("Collatz 3-adic precision must fit one 64-bit limb")
        if self.local_shift not in (0, 1):
            raise ValueError(self)
        modulus = 3**precision
        object.__setattr__(self, "tail_residue", self.tail_residue % modulus)

    @property
    def modulus(self) -> int:
        return int(3**self.precision)

    @classmethod
    def from_source_residue(
        cls,
        source_residue: int,
        valuation: int,
        *,
        precision: int,
    ) -> CollatzFixedPointPadicFrame:
        if any(
            type(value) is not int
            for value in (
                source_residue,
                valuation,
                precision,
            )
        ):
            raise TypeError("Collatz frame construction requires exact integers")
        if not 0 < precision <= 40 or valuation <= 0:
            raise ValueError((precision, valuation))
        modulus = 3**precision
        q, local = divmod(valuation, 2)
        sentinel = _sentinel_prefix_mod3(q, precision)
        scale = pow(4, q, modulus)
        tail = (source_residue - sentinel) * pow(scale, -1, modulus)
        return cls(precision, tail % modulus, local)

    @classmethod
    def from_odd_value(
        cls, value: int, *, precision: int
    ) -> CollatzFixedPointPadicFrame:
        if type(value) is not int or type(precision) is not int:
            raise TypeError("Collatz odd frame construction requires exact integers")
        if value <= 0 or not (value & 1):
            raise ValueError(value)
        valuation = v2_positive(3 * value + 1)
        return cls.from_source_residue(value, valuation, precision=precision)

    @classmethod
    def from_radial_quotient(
        cls,
        radial: PadicRadialQuotient,
        valuation: int,
    ) -> CollatzFixedPointPadicFrame:
        if type(valuation) is not int:
            raise TypeError("Collatz radial valuation must be an exact integer")
        if (
            type(radial) is not PadicRadialQuotient
            or radial.prime != 3
            or radial.source_annihilated is not True
        ):
            raise ValueError(
                "fixed-point frame requires an annihilated 3-adic radial quotient"
            )
        return cls.from_source_residue(
            radial.innovation,
            valuation,
            precision=radial.precision,
        )

    @property
    def successor_residue(self) -> int:
        inv = 1 if self.local_shift == 0 else pow(2, -1, self.modulus)
        return ((3 * self.tail_residue + 1) * inv) % self.modulus

    def recenter(self, next_valuation: int) -> CollatzFixedPointPadicFrame:
        """Recenter the exact successor residue once its next valuation is known."""
        if type(next_valuation) is not int:
            raise TypeError("Collatz recentering valuation must be an exact integer")
        return CollatzFixedPointPadicFrame.from_source_residue(
            self.successor_residue,
            next_valuation,
            precision=self.precision,
        )

    @property
    def future_root(self) -> CollatzFutureValuationRoot:
        return CollatzFutureValuationRoot(self.local_shift)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "collatz-fixed-point-padic-frame",
            3,
            self.precision,
            self.local_shift,
            self.tail_residue,
        )

    @property
    def description_bits(self) -> int:
        return bit_width(self.modulus - 1) + 1


def fixed_frame_future_collision(precision: int) -> tuple[int, int, int, int]:
    """Construct an exact collision proving finite 3-adic frame non-closure.

    ``m1=3`` and ``m2=3+4*3**a`` have the same residue modulo ``3**a`` and
    the same local sector ``t=1``.  Their next valuations are respectively
    four and one.  This works for every positive precision ``a``.
    """
    if type(precision) is not int:
        raise TypeError("Collatz collision precision must be an exact integer")
    a = precision
    if not 0 < a <= 40:
        raise ValueError("Collatz 3-adic precision must fit one 64-bit limb")
    m1 = 3
    m2 = 3 + 4 * (3**a)
    k1 = CollatzFutureValuationRoot(1).next_valuation_from_tail(m1)
    k2 = CollatzFutureValuationRoot(1).next_valuation_from_tail(m2)
    if m1 % (3**a) != m2 % (3**a) or (k1, k2) != (4, 1):
        raise AssertionError((a, m1, m2, k1, k2))
    return m1, m2, k1, k2


__all__ = [
    "CollatzAffineSuffixAdvance",
    "CollatzAffineSuffixEventProjection",
    "CollatzAffineSuffixGerm",
    "CollatzFixedPointPadicFrame",
    "CollatzFutureValuationRoot",
    "CollatzRadix4FrameFactorization",
    "CollatzTwoValuationFrameSummary",
    "PadicAngularBoundaryGerm",
    "RationalPadicRootGerm",
    "RationalPadicRootMismatch",
    "collatz_affine_suffix_valuations_value",
    "collatz_affine_suffix_valuations_word",
    "collatz_radix4_frame_factorization",
    "collatz_two_valuation_frame_value",
    "collatz_two_valuation_frame_word",
    "fixed_frame_future_collision",
    "strip_radix4_fixed_point_digits",
    "strip_radix4_fixed_point_word",
]
