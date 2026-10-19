"""Joint certified radial / 2-adic Boolean output windows for 3**(2**t).

This is a *partial tape transducer*, not a claimed Fermat primality proof.
The Collatz radial/Sturmian action certifies the TOP binary prefix and the
binary length. The direct 2-adic source plus Boolean shift/add action
certifies the LOW output prefix after a dyadic exponent step. These windows
can be merged into a complete word ONLY if they cover every bit and agree in
any overlap. No Sturmian width symbol is ever reinterpreted as an interior
bit of the exponential; absent middle positions remain explicitly unknown.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from weakref import ReferenceType, ref

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.boolean_counter import BinaryBooleanCarryAction
from number_compiler.arithmetic.fields.homogeneous_growth import (
    GrowthArithmeticEvaluator,
    HomogeneousGrowthScale,
)
from number_compiler.arithmetic.fields.radial_sturmian import RadialSturmianClock
from number_compiler.arithmetic.fields.walsh import WalshH5, walsh_h5_at_offset
from number_compiler.hashlife.execution.source_image_seals import typed_payload_equal
from number_compiler.sequences.power_numbers.three_dyadic_boolean_counter import (
    MAX_COUNTER_FOLD_WIDTH,
    MAX_COUNTER_PRECISION,
    two_adic_unit_binomial,
)

MAX_RADIAL_LEVEL = 4096
MAX_RADIAL_PREFIX = 512
_TAPE_ISSUER = object()


@dataclass(frozen=True, slots=True)
class _TapeProvenance:
    issuer: object
    record: ReferenceType[object]
    snapshot: tuple[object, ...]


def _seal_tape(tape: DyadicCertifiedTape) -> None:
    object.__setattr__(
        tape,
        "_issuer",
        _TapeProvenance(_TAPE_ISSUER, ref(tape), tape.structural_snapshot()),
    )


@dataclass(frozen=True, slots=True, weakref_slot=True)
class DyadicCertifiedTape:
    """Output of one actual dyadic 3-power step, in source bit coordinates.

    All bits are LSD-first integers. ``low_bits`` means the *entire* low prefix
    [0,low_bits), not merely a selected mask. ``high_value`` has ``high_bits``
    positions beginning at ``high_start``. The Boolean action is on the
    normalized unit, whose bits start at source position ``level+3`` in the
    next 3-power source. Its fold correction is partial unless ``complete``.
    """

    source_level: int
    fermat_width: int
    word_bits: int
    low_bits: int
    low_value: int
    high_start: int
    high_bits: int
    high_value: int
    counter: BinaryBooleanCarryAction
    unit_precision: int
    next_unit_low: int
    _issuer: object = field(default=None, init=False, repr=False, compare=False)

    def structural_snapshot(self) -> tuple[object, ...]:
        return (
            self.source_level,
            self.fermat_width,
            self.word_bits,
            self.low_bits,
            self.low_value,
            self.high_start,
            self.high_bits,
            self.high_value,
            self.unit_precision,
            self.next_unit_low,
            id(self.counter),
            self.counter.modulus,
            self.counter.length,
            self.counter.next_carries,
            self.counter.deltas,
            tuple(
                (h.length_mod6, h.phi2, h.phi3_a, h.phi3_b)
                for h in self.counter.harmonics
            ),
            self.counter.structural_snapshot(),
        )

    @property
    def producer_verified(self) -> bool:
        issuer = self._issuer
        return (
            type(issuer) is _TapeProvenance
            and issuer.issuer is _TAPE_ISSUER
            and issuer.record() is self
            and typed_payload_equal(issuer.snapshot, self.structural_snapshot())
        )

    def _require_verified(self) -> None:
        if not self.producer_verified:
            raise ValueError("radial/Boolean tape has no verified source provenance")

    def __post_init__(self) -> None:
        require_integer(self.source_level, "source level", 1, MAX_RADIAL_LEVEL - 1)
        require_integer(self.fermat_width, "Fermat width", 1, 65_536)
        require_integer(self.word_bits, "output word bit length", 1)
        require_integer(
            self.low_bits, "low coverage", 1, min(self.word_bits, MAX_COUNTER_PRECISION)
        )
        require_integer(
            self.high_bits, "high coverage", 1, min(self.word_bits, MAX_RADIAL_PREFIX)
        )
        if self.high_start != self.word_bits - self.high_bits:
            raise ValueError("Sturmian high prefix has incorrect source alignment")
        require_integer(self.low_value, "low output word", 0, (1 << self.low_bits) - 1)
        require_integer(
            self.high_value, "high output word", 0, (1 << self.high_bits) - 1
        )
        require_integer(
            self.unit_precision, "normalized-unit precision", 0, MAX_COUNTER_PRECISION
        )
        if type(self.counter) is not BinaryBooleanCarryAction:
            raise TypeError("output tape must contain its Boolean carry action")
        if (
            self.counter.length != self.unit_precision
            or self.counter.modulus != (1 << self.fermat_width) + 1
        ):
            raise ValueError("counter action has the wrong normalized-unit geometry")
        require_integer(
            self.next_unit_low,
            "next source unit",
            0,
            (1 << self.unit_precision) - 1 if self.unit_precision else 0,
        )
        if self.low_bits > self.high_start:
            overlap = self.low_bits - self.high_start
            mask = (1 << overlap) - 1
            if ((self.low_value >> self.high_start) & mask) != (self.high_value & mask):
                raise ArithmeticError("radial and Boolean tape windows disagree")

    @property
    def gap(self) -> tuple[int, int]:
        """Uncertified middle positions, empty when the output is complete."""
        return (self.low_bits, max(self.low_bits, self.high_start))

    @property
    def complete(self) -> bool:
        return self.producer_verified and self.high_start <= self.low_bits

    @property
    def full_word(self) -> int:
        """Only publish a whole word after exact interval coverage is proved."""
        self._require_verified()
        if not self.complete:
            raise ValueError(("global-0-1-tape-not-certified", self.gap))
        return self.low_value | (self.high_value << self.high_start)

    @property
    def partial_signed_fermat_unit_correction(self) -> int:
        """Boolean action on low *unit* bits; not automatically a global fold."""
        self._require_verified()
        return self.counter.apply(0)[1]

    @property
    def certified_intervals(self) -> tuple[tuple[int, int, str], ...]:
        """The actual covered tape intervals, LSD-first, with source authority."""
        self._require_verified()
        return (
            (0, self.low_bits, "two-adic-boolean-shift-add"),
            (self.high_start, self.word_bits, "certified-collatz-radial-prefix"),
        )

    def output_tape(self, start: int, width: int, *, msb_first: bool = False) -> str:
        """A zero-padded 0/1 window; default ordering is LSD-first."""
        bits = self.output_window(start, width)
        written = format(bits, f"0{width}b")
        return written if msb_first else written[::-1]

    def output_bit(self, index: int) -> int:
        """Demand one genuine bit; never fill an unproved middle gap."""
        return self.output_window(index, 1)

    def output_h5(self, start: int, width: int) -> WalshH5:
        """Six-phase Walsh/F5 of CERTIFIED output positions, globally aligned.

        This is a source observation.  It cannot stand in for the folded
        remainder or certify unobserved positions of the full output word.
        """
        return walsh_h5_at_offset(self.output_window(start, width), width, start)

    def complete_signed_fold(self) -> int:
        """Exact Fermat remainder only when every source bit was certified."""
        from number_compiler.sequences.power_numbers.fermat_signed_reducer import (
            fold_signed_fermat,
        )

        return fold_signed_fermat(self.full_word, self.fermat_width)

    def output_window(self, start: int, width: int) -> int:
        """Return a composed 0/1 slice only when fully covered."""
        self._require_verified()
        start = require_integer(start, "output bit start", 0)
        # Bound the requested slice before constructing its integer mask.  A
        # source word may be very long even though each independently
        # authenticated edge is deliberately small.
        width = require_integer(
            width, "output bit width", 1, MAX_COUNTER_PRECISION + MAX_RADIAL_PREFIX
        )
        stop = start + width
        if stop > self.word_bits:
            raise ValueError("output bit demand extends beyond the source word")
        if self.complete:
            # A mixed window may straddle BOTH certified prefix origins.
            # A verified overlap makes the joined word authoritative.
            return (self.full_word >> start) & ((1 << width) - 1)
        if stop <= self.low_bits:
            return (self.low_value >> start) & ((1 << width) - 1)
        if start >= self.high_start:
            return (self.high_value >> (start - self.high_start)) & ((1 << width) - 1)
        raise ValueError(("middle-source-bit-not-certified", start, stop, self.gap))


def _next_low_word(
    level: int, low_bits: int, fermat_width: int
) -> tuple[int, BinaryBooleanCarryAction, int, int]:
    """Apply the actual 2-adic shifted-square Boolean adder, not a label."""
    # 3**(2**(level+1)) = 1 + 2**(level+3)*u_(level+1).
    unit_precision = max(0, low_bits - (level + 3))
    if unit_precision == 0:
        counter = BinaryBooleanCarryAction.identity((1 << fermat_width) + 1)
        return 1, counter, 0, 0
    unit = two_adic_unit_binomial(level, unit_precision)
    mask = (1 << unit_precision) - 1
    shift = level + 1
    addend = 0 if shift >= unit_precision else ((unit * unit) << shift) & mask
    counter = BinaryBooleanCarryAction.from_words(
        unit, addend, unit_precision, (1 << fermat_width) + 1
    )
    _carry_out, following, _xor_mask = counter.apply_words(0)
    result = (1 + (following << (level + 3))) & ((1 << low_bits) - 1)
    return result, counter, unit_precision, following


@dataclass(frozen=True, slots=True)
class ThreeDyadicRadialCounterTransducer:
    """The dyadic source with a *joint* Collatz radial and Boolean readout.

    The radial generator gives the leading bits and source width, while the
    shifted-square counter gives a low output tape. Neither channel is silently
    extended through the uncertified middle. Large time indices may still be
    used for bounded 2-adic counter queries, but exact radial requests are
    explicitly limited by the evaluator and the exponent-descriptor budget.
    """

    level: int

    def __post_init__(self) -> None:
        require_integer(self.level, "three-dyadic level", 1)

    def composed_step(
        self,
        evaluator: GrowthArithmeticEvaluator,
        *,
        fermat_width: int,
        low_bits: int = 128,
        leading_bits: int = 32,
    ) -> DyadicCertifiedTape:
        if type(evaluator) is not GrowthArithmeticEvaluator:
            raise TypeError("radial output needs a certified growth evaluator")
        t = self.level
        if t + 1 > MAX_RADIAL_LEVEL:
            raise ValueError("radial-source-exponent-descriptor-budget")
        selected_low = require_integer(
            low_bits, "low output bits", 1, MAX_COUNTER_PRECISION
        )
        selected_leading = require_integer(
            leading_bits, "radial output bits", 1, MAX_RADIAL_PREFIX
        )
        w = require_integer(fermat_width, "Fermat width", 1, MAX_COUNTER_FOLD_WIDTH)
        # Reuse the exact Collatz (3/2)^k phase: the dyadic power of two
        # cancels in normalized leading bits, but the absolute binary length
        # needs the known k dyadic shifts restored.
        k = 1 << (t + 1)
        clock = RadialSturmianClock(HomogeneousGrowthScale(k, k))
        order = evaluator.radix_order(clock.scale, 2)
        word_bits = order + k + 1
        high_bits = min(word_bits, selected_leading)
        packet = clock.leading_binary(evaluator, high_bits)
        if packet.binary_order + packet.halvings + 1 != word_bits:
            raise ArithmeticError("Sturmian leading packet has inconsistent length")
        low_length = min(word_bits, selected_low)
        low_value, counter, precision, next_unit = _next_low_word(t, low_length, w)
        tape = DyadicCertifiedTape(
            t,
            w,
            word_bits,
            low_length,
            low_value,
            word_bits - high_bits,
            high_bits,
            packet.prefix_value,
            counter,
            precision,
            next_unit,
        )
        _seal_tape(tape)
        return tape


__all__ = ["DyadicCertifiedTape", "ThreeDyadicRadialCounterTransducer"]
