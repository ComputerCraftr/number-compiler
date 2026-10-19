"""Exact, source-owned base-2 Boolean counter and weighted Fermat fold ports.

The dyadic-three unit has the exact 2-adic binomial expansion

    u_t = sum_{j>=1} (-1)^j * 4**(j-1) / j * C(2**t-1, j-1).

The j-th summand has valuation 2*(j-1)-v2(j), so any *finite*
2-adic demand needs only O(precision) terms, even when t is enormous.
No 3**(2**t) integer or chronological modular-square trace is constructed.

The Boolean counter monoid accepts *authenticated source and addend digits*.
Its action on the two incoming-carry contexts publishes an outgoing carry,
exact weighted signed-Fermat correction and the composable Walsh H5 mask.
CONCAT/REPEAT are exact spatial operations. Neither proves an arbitrary-time
successor for the whole Fermat source nor an unrestricted prime certificate.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from math import lcm
from typing import TYPE_CHECKING, Final, Protocol
from weakref import ReferenceType, ref

from number_compiler.arithmetic.contracts.input_validation import (
    is_object_tuple,
    require_integer,
)
from number_compiler.arithmetic.fields.boolean_counter import (
    MAX_BOOLEAN_BLOCK_BITS,
    BinaryBooleanCarryAction,
)
from number_compiler.arithmetic.fields.walsh import WalshH5

if TYPE_CHECKING:
    from number_compiler.sequences.power_numbers.signed_counter_classes import (
        SignedCounterClassAction,
    )

MAX_COUNTER_PRECISION = 4_096
MAX_COUNTER_FOLD_WIDTH = 65_536
MAX_AUTHENTICATED_OPERAND_BITS = MAX_BOOLEAN_BLOCK_BITS
MAX_COUNTER_WINDOW_BATCH = 8
MAX_COMPLETE_UNIT_BITS: Final[int] = 60_000
_BINARY_COUNTER_FOLD_H5_ID: Final[str] = "binary-counter-fold-h5-v1"
_COUNTER_WINDOW_ISSUER = object()
_FERMAT_CERTIFICATE_ISSUER = object()
_COMPLETE_UNIT_ISSUER = object()


class _CounterRecord(Protocol):
    def structural_snapshot(self) -> tuple[object, ...]: ...


@dataclass(frozen=True, slots=True)
class _CounterProvenance:
    kind: object
    record: ReferenceType[object]
    snapshot: tuple[object, ...]


def _seal_counter(record: _CounterRecord, kind: object) -> None:
    object.__setattr__(
        record,
        "_issuer",
        _CounterProvenance(kind, ref(record), record.structural_snapshot()),
    )


def _counter_verified(record: _CounterRecord, issuer: object, kind: object) -> bool:
    if (
        type(issuer) is not _CounterProvenance
        or issuer.kind is not kind
        or issuer.record() is not record
    ):
        return False
    pending = [(issuer.snapshot, record.structural_snapshot())]
    while pending:
        expected, actual = pending.pop()
        if len(expected) != len(actual):
            return False
        for old, new in zip(expected, actual, strict=True):
            if type(old) is not type(new):
                return False
            if is_object_tuple(old) and is_object_tuple(new):
                pending.append((old, new))
            elif type(old) in (int, bool, str, type(None)):
                if old != new:
                    return False
            elif old is not new:
                return False
    return True


def _checked_precision(precision: int) -> int:
    return require_integer(
        precision, "binary counter precision", 1, MAX_COUNTER_PRECISION
    )


def _checked_level(level: int) -> int:
    level = require_integer(level, "dyadic source level", 1)
    if level.bit_length() > MAX_COUNTER_PRECISION:
        raise ValueError("dyadic level exceeds the symbolic coordinate budget")
    return level


def two_adic_unit_binomial(level: int, precision: int) -> int:
    """Return ``(3**(2**level)-1)//2**(level+2) mod 2**precision``.

    Every summand is computed in Z/2**precision with its powers of two
    cancelled *before* any odd modular inverses.  The binomial factor is
    advanced using C(N-1,j)=-C(N-1,j-1)*(1-N/j) in Z_2; the calculation
    never constructs N=2**level for a large level.
    """
    t = _checked_level(level)
    bits = _checked_precision(precision)
    return _binomial_unit_sum(t, bits)


def _binomial_unit_sum(level: int, precision: int) -> int:
    """Evaluate the exact finite-precision binomial source within its cap."""
    return _binomial_unit_source(level, precision)[0]


def _binomial_unit_source(level: int, precision: int) -> tuple[int, int]:
    """Return the binomial residue and the number of included source terms."""
    t = _checked_level(level)
    bits = require_integer(
        precision, "2-adic source precision", 1, MAX_COMPLETE_UNIT_BITS
    )
    modulus = 1 << bits
    mask = modulus - 1
    total = 0
    choose = 1  # C(2**t-1, j-1) mod 2**bits.
    j = 1
    while True:
        # Floor(log2(j)) bounds v2(j); this lower bound is monotonic
        # once j>=1, so all subsequent summands vanish simultaneously.
        if 2 * (j - 1) - (j.bit_length() - 1) >= bits:
            break
        # If j > 2**t, the binomial coefficient is identically zero.
        # Construct 2**t only when t is small enough to matter here.
        if t < j.bit_length() and j > (1 << t):
            break
        valuation_j = (j & -j).bit_length() - 1
        scale = 2 * (j - 1) - valuation_j
        odd_inverse = pow(j >> valuation_j, -1, modulus)
        summand = ((1 << scale) * choose * odd_inverse) & mask
        total = (total - summand if j & 1 else total + summand) & mask

        # For j <= 2**t, t-v2(j) >= 0.  The factors 2**t/j are 2-adic
        # integers; their odd denominators are invertible modulo 2**bits.
        if t - valuation_j >= bits:
            factor = 1
        else:
            factor = (1 - ((1 << (t - valuation_j)) * odd_inverse)) & mask
        choose = (-choose * factor) & mask
        j += 1
    return total, j - 1


def _certified_unit_bit_bound(level: int) -> int:
    """Bound ``bit_length(u_level)`` using the integer inequality 3^1000<2^1585.

    The bound is a separate source budget, not a uniform-cost primality path.
    Reject large levels before constructing their exponential coordinates.
    """
    t = _checked_level(level)
    if t >= 30:
        raise ValueError("complete-unit-source-bound-exceeds-budget")
    exponent = 1 << t
    bits = (1585 * exponent + 999) // 1000 - (t + 2)
    if bits > MAX_COMPLETE_UNIT_BITS:
        raise ValueError("complete-unit-source-bound-exceeds-budget")
    return max(1, bits)


@dataclass(frozen=True, slots=True, weakref_slot=True)
class BoundedCompleteUnitCertificate:
    """Sealed complete 2-adic source for one resource-bounded Fermat index.

    The source calculation is linear in the complete unit's bit width. It is
    useful as an explicit bounded proof artifact; it does not create a
    uniform-speedup primality path. An incomplete or externally constructed
    packet cannot issue a verdict.
    """

    index: int
    level: int
    precision: int
    term_count: int
    unit: int
    terminal_residue: int
    _issuer: object = field(default=None, init=False, repr=False, compare=False)

    def structural_snapshot(self) -> tuple[object, ...]:
        return (
            self.index,
            self.level,
            self.precision,
            self.term_count,
            self.unit,
            self.terminal_residue,
        )

    @property
    def producer_verified(self) -> bool:
        try:
            return _counter_verified(self, self._issuer, _COMPLETE_UNIT_ISSUER)
        except (AttributeError, TypeError):
            return False

    @property
    def complete_source_verified(self) -> bool:
        return self.producer_verified and self.precision >= max(
            1, self.unit.bit_length()
        )

    @property
    def fermat_width(self) -> int:
        index = require_integer(self.index, "Fermat index", 1, 16)
        return 1 << index

    @property
    def verdict(self) -> str:
        self.verify()
        # The available bridge establishes Pépin's sufficient direction.
        # A failed residue is therefore left unresolved here.
        return "PRIME" if self.terminal_residue == 1 else "UNKNOWN"

    def verify(self) -> None:
        if not self.producer_verified:
            raise ValueError("complete-unit certificate has no source seal")
        index = require_integer(self.index, "Fermat index", 1, 16)
        terminal_level = (1 << index) - 1
        if self.level != terminal_level:
            raise ValueError("complete-unit terminal level is incorrect")
        expected_precision = _certified_unit_bit_bound(terminal_level)
        if self.precision != expected_precision:
            raise ValueError("complete-unit source precision is incorrect")
        if (
            type(self.term_count) is not int
            or not 1 <= self.term_count <= 1 << terminal_level
        ):
            raise ValueError("complete-unit source term count is invalid")
        if type(self.unit) is not int or self.unit < 0:
            raise ValueError("complete-unit source value is invalid")
        if self.unit.bit_length() > expected_precision:
            raise ValueError("complete-unit source exceeds its certified width")
        modulus = (1 << (1 << index)) + 1
        residue = require_integer(
            self.terminal_residue, "terminal unit residue", 0, modulus - 1
        )
        if residue != self.unit % modulus:
            raise ValueError("terminal unit residue disagrees with the source")

    def complete_last_counter_action(self) -> SignedCounterClassAction:
        """Build the complete signed class action for the final unit step.

        Both complete units come from the same bounded binomial source. The
        integer successor identity is checked before forming the full supplied
        block; this action carries no omitted-bit inference.
        """
        from number_compiler.sequences.power_numbers.signed_counter_classes import (
            SignedCounterClassAction,
        )

        self.verify()
        if self.level < 2:
            raise ValueError("no predecessor normalized unit at this level")
        prior_level = self.level - 1
        prior_precision = _certified_unit_bit_bound(prior_level)
        prior, _prior_term_count = _binomial_unit_source(prior_level, prior_precision)
        innovation = self.unit - prior
        if innovation < 0 or innovation != ((prior * prior) << self.level):
            raise ArithmeticError("complete-unit successor identity failed")
        length = max(1, self.unit.bit_length(), prior.bit_length())
        if length > MAX_AUTHENTICATED_OPERAND_BITS:
            raise ValueError("complete-counter-operands-exceed-budget")
        action = SignedCounterClassAction.from_words(
            prior, innovation, length, self.fermat_width
        )
        carry, _classes, delta, _harmonic = action.apply(0)
        if carry != 0 or delta != innovation % ((1 << self.fermat_width) + 1):
            raise ArithmeticError("complete signed class correction mismatch")
        return action


def demand_bounded_complete_unit_certificate(
    index: int,
) -> BoundedCompleteUnitCertificate:
    """Demand a complete unit source, refusing beyond the explicit bit budget."""
    n = require_integer(index, "Fermat index", 1, 16)
    terminal_level = (1 << n) - 1
    precision = _certified_unit_bit_bound(terminal_level)
    unit, term_count = _binomial_unit_source(terminal_level, precision)
    modulus = (1 << (1 << n)) + 1
    certificate = BoundedCompleteUnitCertificate(
        n,
        terminal_level,
        precision,
        term_count,
        unit,
        unit % modulus,
    )
    _seal_counter(certificate, _COMPLETE_UNIT_ISSUER)
    certificate.verify()
    return certificate


@dataclass(frozen=True, slots=True)
class BinaryCounterFoldAction:
    """A two-carry-context, composable signed-fold and H5 action.

    ``deltas[c]`` is the weighted output-minus-source *relative to the start
    of this block*, modulo 2**fermat_width+1.  ``harmonics[c]`` is the H5
    action of its XOR output word for that entry carry.  The two contexts
    are the Moore input states and can sometimes be merged.
    """

    fermat_width: int
    length: int
    next_carries: tuple[int, int]
    deltas: tuple[int, int]
    harmonics: tuple[WalshH5, WalshH5]

    def __post_init__(self) -> None:
        require_integer(
            self.fermat_width, "Fermat fold width", 1, MAX_COUNTER_FOLD_WIDTH
        )
        require_integer(self.length, "Boolean counter block length", 0)
        if (
            type(self.next_carries) is not tuple
            or type(self.deltas) is not tuple
            or type(self.harmonics) is not tuple
            or any(
                len(item) != 2
                for item in (self.next_carries, self.deltas, self.harmonics)
            )
        ):
            raise TypeError("binary counter action requires two exact carry contexts")
        for state in self.next_carries:
            require_integer(state, "Boolean counter output carry", 0, 1)
        modulus = (1 << self.fermat_width) + 1
        for delta in self.deltas:
            require_integer(delta, "signed fold correction", 0, modulus - 1)
        if any(type(h) is not WalshH5 for h in self.harmonics):
            raise TypeError("counter harmonics must be exact WalshH5 records")
        if any(h.length_mod6 != self.length % 6 for h in self.harmonics):
            raise ValueError("counter H5 word length is not source-aligned")

    @property
    def modulus(self) -> int:
        return (1 << self.fermat_width) + 1

    @property
    def _shared_action(self) -> BinaryBooleanCarryAction:
        return BinaryBooleanCarryAction(
            self.modulus,
            self.length,
            self.next_carries,
            self.deltas,
            self.harmonics,
        )

    @classmethod
    def _from_shared(
        cls, action: BinaryBooleanCarryAction, fermat_width: int
    ) -> BinaryCounterFoldAction:
        return cls(
            fermat_width,
            action.length,
            action.next_carries,
            action.deltas,
            action.harmonics,
        )

    @classmethod
    def identity(cls, fermat_width: int) -> BinaryCounterFoldAction:
        width = require_integer(
            fermat_width, "Fermat fold width", 1, MAX_COUNTER_FOLD_WIDTH
        )
        return cls._from_shared(
            BinaryBooleanCarryAction.identity((1 << width) + 1), width
        )

    @classmethod
    def digit(
        cls, source_bit: int, addend_bit: int, fermat_width: int
    ) -> BinaryCounterFoldAction:
        width = require_integer(
            fermat_width, "Fermat fold width", 1, MAX_COUNTER_FOLD_WIDTH
        )
        action = BinaryBooleanCarryAction.digit(
            source_bit, addend_bit, (1 << width) + 1
        )
        return cls._from_shared(action, width)

    def then(self, higher: BinaryCounterFoldAction) -> BinaryCounterFoldAction:
        """LSD-first composition with authenticated higher operand digits."""
        if type(higher) is not BinaryCounterFoldAction:
            raise TypeError("counter composition requires a counter action")
        if self.fermat_width != higher.fermat_width:
            raise ValueError("counter actions use different Fermat moduli")
        return self._from_shared(
            self._shared_action.then(higher._shared_action), self.fermat_width
        )

    def repeat(self, copies: int) -> BinaryCounterFoldAction:
        """Power a genuinely repeated operand block, not an inferred future."""
        return self._from_shared(self._shared_action.repeat(copies), self.fermat_width)

    @property
    def semantic_id(self) -> tuple[object, ...]:
        """An exact right-congruence key for carry/fold/H5 observations.

        Literal block length and source digits are deliberately excluded.
        Only their mod-2w/mod-6 shift phase and the two observable actions
        matter when this block is followed by the *same* higher-word action.
        """
        return (
            _BINARY_COUNTER_FOLD_H5_ID,
            self.fermat_width,
            self.length % lcm(2 * self.fermat_width, 6),
            self.next_carries,
            self.deltas,
            tuple((h.phi2, h.phi3_a, h.phi3_b) for h in self.harmonics),
        )

    @property
    def moore_carry_classes(self) -> int:
        return self._shared_action.moore_carry_classes

    def apply(self, incoming_carry: int = 0) -> tuple[int, int, WalshH5]:
        return self._shared_action.apply(incoming_carry)

    @classmethod
    def from_words(
        cls, source_bits: int, addend_bits: int, length: int, fermat_width: int
    ) -> BinaryCounterFoldAction:
        width = require_integer(
            length, "counter operand width", 0, MAX_AUTHENTICATED_OPERAND_BITS
        )
        selected_width = require_integer(
            fermat_width, "Fermat fold width", 1, MAX_COUNTER_FOLD_WIDTH
        )
        if (
            type(source_bits) is not int
            or type(addend_bits) is not int
            or source_bits < 0
            or addend_bits < 0
            or source_bits.bit_length() > width
            or addend_bits.bit_length() > width
        ):
            raise ValueError("source/addend words must fit the demanded width")
        action = BinaryBooleanCarryAction.from_words(
            source_bits, addend_bits, width, (1 << selected_width) + 1
        )
        return cls._from_shared(action, selected_width)


@dataclass(frozen=True, slots=True, weakref_slot=True)
class DyadicBooleanCounterWindow:
    """Exact demanded binary counter and partial signed-Fermat fold.

    The source and addend are authenticated directly from u_t at finite
    precision.  The window is not a complete prime certificate unless an
    independent all-position coverage proof establishes that every omitted
    signed toggle contributes zero.
    """

    level: int
    start: int
    width: int
    fermat_width: int
    source_bits: int
    addend_bits: int
    carry_in: int
    carry_out: int
    result_bits: int
    incoming_carries: int
    generate_mask: int
    propagate_mask: int
    xor_mask: int
    fold_action: BinaryCounterFoldAction
    _issuer: object = field(default=None, init=False, repr=False, compare=False)

    def structural_snapshot(self) -> tuple[object, ...]:
        return (
            self.level,
            self.start,
            self.width,
            self.fermat_width,
            self.source_bits,
            self.addend_bits,
            self.carry_in,
            self.carry_out,
            self.result_bits,
            self.incoming_carries,
            self.generate_mask,
            self.propagate_mask,
            self.xor_mask,
            self.fold_action,
            self.fold_action.fermat_width,
            self.fold_action.length,
            self.fold_action.next_carries,
            self.fold_action.deltas,
            tuple(
                (h.length_mod6, h.phi2, h.phi3_a, h.phi3_b)
                for h in self.fold_action.harmonics
            ),
        )

    @property
    def producer_verified(self) -> bool:
        if type(self.fold_action) is not BinaryCounterFoldAction:
            return False
        try:
            return _counter_verified(self, self._issuer, _COUNTER_WINDOW_ISSUER)
        except (AttributeError, TypeError):
            return False

    @property
    def covers_complete_unit_transition(self) -> bool:
        """Prove *all* changed unit bits were demanded, without source replay.

        Since 3**5 < 2**8, the bit width of u_(t+1) is at most
        ceil(8*2**(t+1)/5) - (t+3).  All bits below the forced pivot t+1
        are unchanged.  If the requested interval covers that upper bound,
        no residual high-bit correction exists.  This is deliberately false
        for large levels rather than materializing the enormous bound.
        """
        if self.start != self.level + 1 or self.level >= 11:
            return False
        total_exponent = 1 << (self.level + 1)
        maximum_unit_bits = (8 * total_exponent + 4) // 5 - (self.level + 3)
        return self.start + self.width >= maximum_unit_bits

    @property
    def signed_position_counts(self) -> tuple[tuple[int, int], ...]:
        """Sparse *absolute* signed classes modulo 2*Fermat-width."""
        counts: dict[int, int] = {}
        pending = self.xor_mask
        while pending:
            bit = pending & -pending
            index = bit.bit_length() - 1
            residue_class = (self.start + index) % (2 * self.fermat_width)
            signed = 1 - 2 * ((self.source_bits >> index) & 1)
            counts[residue_class] = counts.get(residue_class, 0) + signed
            pending ^= bit
        return tuple(
            sorted((position, total) for position, total in counts.items() if total)
        )

    @property
    def signed_fermat_correction(self) -> int:
        """Exact contribution of *this window*, not of unobserved bits."""
        modulus = (1 << self.fermat_width) + 1
        weighted = sum(
            (1 << position) * count for position, count in self.signed_position_counts
        )
        return weighted % modulus

    @property
    def signed_class_action(self) -> SignedCounterClassAction:
        """Exact two-carry signed-class action for this authenticated window.

        Its ``residue_action`` agrees with the existing weighted fold.  The
        class vector retains all negacyclic positional information of the
        *requested window*, not of the undemanded high source.
        """
        from number_compiler.sequences.power_numbers.signed_counter_classes import (
            SignedCounterClassAction,
        )

        action = SignedCounterClassAction.from_words(
            self.source_bits,
            self.addend_bits,
            self.width,
            self.fermat_width,
            fold_action=self.fold_action,
        )
        if action.residue_action != self.fold_action:
            raise ArithmeticError(
                "signed classes disagree with authenticated fold action"
            )
        return action

    @property
    def absolute_signed_classes(self) -> tuple[tuple[int, int], ...]:
        """Exact source-guarded *partial* Fermat class correction.

        The moving pivot offset is included and the 2**w=-1 sign is
        applied before collecting the w residue classes. Not a certificate
        for bits beyond the demanded source window.
        """
        return self.signed_class_action.shifted_classes(self.carry_in, self.start)

    @property
    def absolute_walsh_h5(self) -> WalshH5:
        """H5 of changed bits at their true source positions."""
        prefix = WalshH5(self.start % 6, 0, 0, 0)
        packet = prefix.then(self.fold_action.apply(self.carry_in)[2])
        return WalshH5(0, packet.phi2, packet.phi3_a, packet.phi3_b)

    def __post_init__(self) -> None:
        _checked_level(self.level)
        _checked_precision(self.width)
        require_integer(self.start, "Boolean counter start", self.level + 1)
        require_integer(
            self.fermat_width, "Fermat fold width", 1, MAX_COUNTER_FOLD_WIDTH
        )
        mask = (1 << self.width) - 1
        for name, value in (
            ("source window", self.source_bits),
            ("addend window", self.addend_bits),
            ("counter output", self.result_bits),
            ("counter incoming carries", self.incoming_carries),
            ("generate mask", self.generate_mask),
            ("propagate mask", self.propagate_mask),
            ("XOR mask", self.xor_mask),
        ):
            require_integer(value, name, 0, mask)
        for c in (self.carry_in, self.carry_out):
            require_integer(c, "Boolean carry", 0, 1)
        if type(self.fold_action) is not BinaryCounterFoldAction:
            raise TypeError("Boolean counter window needs an exact fold action")
        if (
            self.fold_action.fermat_width != self.fermat_width
            or self.fold_action.length != self.width
        ):
            raise ValueError("Boolean counter action has the wrong source geometry")
        # Recompute both source input words and the omitted-prefix carry from
        # the authenticated 2-adic unit, independently of caller-supplied
        # dataclass fields.  Algebraically valid but invented run edits are
        # not allowed to masquerade as source-derived observations.
        unit = two_adic_unit_binomial(self.level, self.start + self.width)
        source = (unit >> self.start) & mask
        addend = (unit * unit >> (self.start - self.level - 1)) & mask
        lower_mask = (1 << self.start) - 1
        incoming = (
            (unit & lower_mask) + (((unit * unit) << (self.level + 1)) & lower_mask)
        ) >> self.start
        expected_action = BinaryCounterFoldAction.from_words(
            source, addend, self.width, self.fermat_width
        )
        if (
            source != self.source_bits
            or addend != self.addend_bits
            or incoming != self.carry_in
            or expected_action != self.fold_action
        ):
            raise ValueError("counter window is not authenticated by its dyadic source")
        carry, delta, _ = self.fold_action.apply(self.carry_in)
        sum_bits = self.source_bits + self.addend_bits + self.carry_in
        carry_tape = 0
        cursor = self.carry_in
        for i in range(self.width):
            carry_tape |= cursor << i
            a = (self.source_bits >> i) & 1
            b = (self.addend_bits >> i) & 1
            cursor = (a & b) | ((a ^ b) & cursor)
        modulus = (1 << self.fermat_width) + 1
        if (
            carry != self.carry_out
            or cursor != self.carry_out
            or sum_bits & mask != self.result_bits
            or carry_tape != self.incoming_carries
            or self.generate_mask != self.source_bits & self.addend_bits
            or self.propagate_mask != self.source_bits ^ self.addend_bits
            or self.xor_mask != self.source_bits ^ self.result_bits
            or (delta * pow(2, self.start % (2 * self.fermat_width), modulus)) % modulus
            != self.signed_fermat_correction
        ):
            raise ArithmeticError(
                "Boolean counter provenance or weighted fold mismatch"
            )
        _seal_counter(self, _COUNTER_WINDOW_ISSUER)

    def verify(self) -> None:
        if not self.producer_verified:
            raise ValueError("Boolean counter window changed after source verification")


def demand_dyadic_boolean_counter(
    level: int,
    width: int,
    *,
    fermat_width: int,
    offset: int = 0,
    source_low_check: tuple[int, int] | None = None,
) -> DyadicBooleanCounterWindow:
    """Request an arbitrary bounded window at/after the unit-difference pivot.

    ``start = level + 1 + offset``.  Incoming carries from the omitted lower
    prefix are computed exactly, so later windows don't silently assume a
    zero entry carry.  The source precision guard executes *before* arithmetic.
    """
    t = _checked_level(level)
    length = _checked_precision(width)
    relative = require_integer(offset, "Boolean counter pivot offset", 0)
    w = require_integer(fermat_width, "Fermat fold width", 1, MAX_COUNTER_FOLD_WIDTH)
    start = t + 1 + relative
    if start + length > MAX_COUNTER_PRECISION:
        raise ValueError(
            ("Boolean-counter-precision-budget", start + length, MAX_COUNTER_PRECISION)
        )
    check_bits = 0
    check_residue = 0
    if source_low_check is not None:
        if type(source_low_check) is not tuple or len(source_low_check) != 2:
            raise TypeError(
                "source low-bit check must be an exact (bits, residue) tuple"
            )
        check_bits = require_integer(
            source_low_check[0], "source check precision", 1, MAX_COUNTER_PRECISION
        )
        check_residue = require_integer(
            source_low_check[1],
            "source check residue",
            0,
            (1 << check_bits) - 1,
        )
    source_precision = max(start + length, check_bits)
    if source_precision > MAX_COUNTER_PRECISION:
        raise ValueError(
            (
                "Boolean-counter-precision-budget",
                source_precision,
                MAX_COUNTER_PRECISION,
            )
        )
    unit = two_adic_unit_binomial(t, source_precision)
    if check_bits and unit & ((1 << check_bits) - 1) != check_residue:
        raise ValueError("Boolean counter source disagrees with its finite CRT port")
    return _counter_window_from_unit(t, start, length, w, unit)


def _counter_window_from_unit(
    level: int, start: int, width: int, fermat_width: int, unit: int
) -> DyadicBooleanCounterWindow:
    """Issue one bounded window from a shared, exact finite-precision unit."""
    relative = start - level - 1
    addend = unit * unit
    mask = (1 << width) - 1
    source = (unit >> start) & mask
    source_addend = (addend >> relative) & mask
    # Sum below 'start'; this is the authenticated entry carry, not an
    # invented constant-zero edge for a moving window.
    lower_mask = (1 << start) - 1
    below = (unit & lower_mask) + ((addend << (level + 1)) & lower_mask)
    incoming = below >> start
    action = BinaryCounterFoldAction.from_words(
        source, source_addend, width, fermat_width
    )
    carry, _, _ = action.apply(incoming)
    total = source + source_addend + incoming
    output = total & mask
    carries = 0
    local_carry = incoming
    for i in range(width):
        carries |= local_carry << i
        local_carry = (((source >> i) & 1) & ((source_addend >> i) & 1)) | (
            (((source >> i) & 1) ^ ((source_addend >> i) & 1)) & local_carry
        )
    if local_carry != carry or carry != total >> width:
        raise ArithmeticError("Boolean counter carry is not compositional")
    result = object.__new__(DyadicBooleanCounterWindow)
    values = (
        level,
        start,
        width,
        fermat_width,
        source,
        source_addend,
        incoming,
        carry,
        output,
        carries,
        source & source_addend,
        source ^ source_addend,
        source ^ output,
        action,
    )
    for name, value in zip(
        (
            "level",
            "start",
            "width",
            "fermat_width",
            "source_bits",
            "addend_bits",
            "carry_in",
            "carry_out",
            "result_bits",
            "incoming_carries",
            "generate_mask",
            "propagate_mask",
            "xor_mask",
            "fold_action",
        ),
        values,
        strict=True,
    ):
        object.__setattr__(result, name, value)
    _seal_counter(result, _COUNTER_WINDOW_ISSUER)
    return result


def demand_dyadic_boolean_counter_windows(
    level: int,
    windows: tuple[tuple[int, int], ...],
    *,
    fermat_width: int,
) -> tuple[DyadicBooleanCounterWindow, ...]:
    """Issue disjoint same-level windows from one finite 2-adic source read."""
    t = _checked_level(level)
    w = require_integer(fermat_width, "Fermat fold width", 1, MAX_COUNTER_FOLD_WIDTH)
    if type(windows) is not tuple or not 1 <= len(windows) <= MAX_COUNTER_WINDOW_BATCH:
        raise ValueError("counter window batch must contain one to eight demands")
    selected: list[tuple[int, int]] = []
    previous_end = t + 1
    source_precision = 0
    for item in windows:
        if type(item) is not tuple or len(item) != 2:
            raise TypeError("counter window demand is an exact (offset, width) pair")
        offset = require_integer(item[0], "Boolean counter pivot offset", 0)
        width = _checked_precision(item[1])
        start = t + 1 + offset
        end = start + width
        if start < previous_end:
            raise ValueError("counter window batch must be sorted and disjoint")
        if end > MAX_COUNTER_PRECISION:
            raise ValueError(
                ("Boolean-counter-precision-budget", end, MAX_COUNTER_PRECISION)
            )
        selected.append((start, width))
        previous_end = end
        source_precision = max(source_precision, end)
    # The one modular binomial source is enough for every requested slice and
    # its lower carry context; no full 3**(2**t) integer is formed.
    unit = two_adic_unit_binomial(t, source_precision)
    return tuple(
        _counter_window_from_unit(t, start, width, w, unit) for start, width in selected
    )


@dataclass(frozen=True, slots=True, weakref_slot=True)
class BoundedFermatCounterCertificate:
    """Finite proof using complete XOR transitions, never a source oracle.

    This is an explicitly bounded integer-width certificate.  Its total
    cost scales with the demanded source width, so it must not be promoted
    as the unrestricted non-replay Fermat primality algorithm.
    """

    index: int
    windows: tuple[DyadicBooleanCounterWindow, ...]
    terminal_unit_residue: int
    _issuer: object = field(default=None, init=False, repr=False, compare=False)

    def structural_snapshot(self) -> tuple[object, ...]:
        return (
            self.index,
            tuple((window, window.structural_snapshot()) for window in self.windows),
            self.terminal_unit_residue,
        )

    @property
    def producer_verified(self) -> bool:
        if type(self.windows) is not tuple or any(
            type(window) is not DyadicBooleanCounterWindow for window in self.windows
        ):
            return False
        if not all(window.producer_verified for window in self.windows):
            return False
        try:
            return _counter_verified(self, self._issuer, _FERMAT_CERTIFICATE_ISSUER)
        except (AttributeError, TypeError):
            return False

    @property
    def complete_source_verified(self) -> bool:
        """Whether the sealed packet authenticates every transition to target."""
        return (
            self.producer_verified
            and len(self.windows) == (1 << self.index) - 2
            and all(window.covers_complete_unit_transition for window in self.windows)
        )

    def __post_init__(self) -> None:
        self.verify()
        _seal_counter(self, _FERMAT_CERTIFICATE_ISSUER)

    @property
    def fermat_width(self) -> int:
        return 1 << self.index

    @property
    def verdict(self) -> str:
        if not self.producer_verified:
            raise ValueError(
                "Fermat counter certificate has no verified full-coverage seal"
            )
        # The bridge proves only Pépin's sufficient direction.  A failed
        # residue is not a compositeness witness, so keep the negative case
        # explicitly unresolved.
        return "PRIME" if self.terminal_unit_residue == 1 else "UNKNOWN"

    def verify(self) -> None:
        require_integer(self.index, "Fermat certificate index", 1, 16)
        if type(self.windows) is not tuple:
            raise TypeError("certificate transitions must be an exact tuple")
        terminal = (1 << self.index) - 1
        if len(self.windows) != terminal - 1:
            raise ValueError("certificate does not cover all unit transitions")
        modulus = (1 << self.fermat_width) + 1
        require_integer(
            self.terminal_unit_residue,
            "terminal normalized-unit residue",
            0,
            modulus - 1,
        )
        residue = 1  # u_1 = 1.
        for t, window in enumerate(self.windows, start=1):
            if (
                type(window) is not DyadicBooleanCounterWindow
                or not window.producer_verified
                or window.level != t
                or window.fermat_width != self.fermat_width
                or not window.covers_complete_unit_transition
            ):
                raise ValueError("missing or unauthenticated complete counter action")
            # Every window validates its binomial-derived source and its
            # complete two-carry action in __post_init__.
            residue = (residue + window.signed_fermat_correction) % modulus
        if residue != self.terminal_unit_residue:
            raise ArithmeticError("terminal unit does not match its signed pivot proof")


def demand_bounded_fermat_counter_certificate(
    index: int,
) -> BoundedFermatCounterCertificate:
    """Finite no-Pepin certificate; refuse before source work when incomplete."""
    n = require_integer(index, "Fermat certificate index", 1, 16)
    terminal = (1 << n) - 1
    if terminal > 11:
        raise ValueError("Boolean-counter-complete-source-budget: terminal too long")
    width = 1 << n
    windows: list[DyadicBooleanCounterWindow] = []
    residue = 1
    modulus = (1 << width) + 1
    for t in range(1, terminal):
        upper_bits = (8 * (1 << (t + 1)) + 4) // 5 - (t + 3)
        length = max(1, upper_bits - (t + 1))
        if t + 1 + length > MAX_COUNTER_PRECISION:
            raise ValueError("Boolean-counter-complete-source-budget")
        window = demand_dyadic_boolean_counter(t, length, fermat_width=width)
        if not window.covers_complete_unit_transition:
            raise ArithmeticError("counter did not cover the complete signed fold")
        windows.append(window)
        residue = (residue + window.signed_fermat_correction) % modulus
    certificate = BoundedFermatCounterCertificate(n, tuple(windows), residue)
    return certificate


__all__ = [
    "MAX_AUTHENTICATED_OPERAND_BITS",
    "MAX_COMPLETE_UNIT_BITS",
    "MAX_COUNTER_FOLD_WIDTH",
    "MAX_COUNTER_PRECISION",
    "MAX_COUNTER_WINDOW_BATCH",
    "BinaryCounterFoldAction",
    "BoundedCompleteUnitCertificate",
    "BoundedFermatCounterCertificate",
    "DyadicBooleanCounterWindow",
    "demand_bounded_complete_unit_certificate",
    "demand_bounded_fermat_counter_certificate",
    "demand_dyadic_boolean_counter",
    "demand_dyadic_boolean_counter_windows",
    "two_adic_unit_binomial",
]
