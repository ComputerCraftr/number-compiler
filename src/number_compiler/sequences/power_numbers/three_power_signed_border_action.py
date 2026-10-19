"""Source-owned cyclotomic/leading-border tripling with weighted signed ports.

This is deliberately NOT a hidden Pépin square or an invented prime theorem.
The admissible source is X_t=3**(2**t); one spatial letter is X -> 3X.
An unknown middle block retains its *weighted source variable* U, not merely
its small carry-transfer map.  For a length-L binary block the exact output
identity is E=3U+c_in-2**L*c_out.  Consequently two words with the same carry
and Walsh masks cannot be falsely identified if their signed folds differ.

The cyclotomic clock can jump any number of ordinary 3X ticks modulo 10**k;
the endpoint's independently certified radial/Sturmian prefix is reused. The
whole unknown word, all intermediate high guards, and the global Fermat fold
are NOT inferred from those endpoints.  A prime consumer must refuse until
there is an independently complete signed-fold certificate.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import pairwise
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from number_compiler.sequences.power_numbers.three_power_signed_phase import (
        SourceRestrictedPhaseRelation,
        SourceSignedPhaseCountPort,
    )
    from number_compiler.sequences.power_numbers.three_power_two_sided_cylinder import (
        FermatTwoSidedSourceCylinder,
    )

from number_compiler.arithmetic.carry.tripling_transfer import (
    CarryFn,
    unknown_middle_transfer_set,
)
from number_compiler.arithmetic.fields.three_power_radix import decimal_tripling_order
from number_compiler.arithmetic.fields.walsh import WalshH5
from number_compiler.sequences.power_numbers._harmonic_authority import (
    harmonic_payload,
    harmonic_verified,
    issue_harmonic,
    new_harmonic_issuer,
)
from number_compiler.sequences.power_numbers.three_power_bilateral_border import (
    ThreePowerBilateralInteriorQuotient,
    carry_h5,
    demand_three_power_inward_phase_quotient,
)


def _exact_cyclic_period(values: list[int]) -> int:
    """Primitive period after the complete cyclic source orbit has closed."""
    length = len(values)
    if not length:
        raise ValueError("empty source orbit")
    prefix = [0] * length
    for i in range(1, length):
        j = prefix[i - 1]
        while j and values[i] != values[j]:
            j = prefix[j - 1]
        if values[i] == values[j]:
            j += 1
        prefix[i] = j
    candidate = length - prefix[-1]
    return candidate if length % candidate == 0 else length


def exact_physical_carry_periods(
    decimal_places: int,
    *,
    max_states: int = 50_000,
) -> tuple[tuple[int, int, int, int], ...]:
    """Exact minimal (full,carry,bit0,bit1) periods at ALL demanded depths.

    This is a deliberately explicit optional audit, NOT the fast runtime
    producer. It examines a complete orbit, refuses above the state budget,
    and never exports periods guessed from finite training windows.
    """
    p = decimal_tripling_order(decimal_places)
    if type(max_states) is not int or p > max_states:
        raise ValueError("complete physical orbit exceeds audit state budget")
    modulus = 10**decimal_places
    boundaries = tuple(10**k for k in range(1, decimal_places + 1))
    words: list[list[int]] = [[] for _ in boundaries]
    residue = 1
    for _ in range(p):
        for i, boundary in enumerate(boundaries):
            words[i].append(3 * (residue % boundary) // boundary)
        residue = residue * 3 % modulus
    if residue != 1 or pow(3, p, modulus) != 1:
        raise ArithmeticError("cyclotomic source orbit did not close")
    return tuple(
        (
            decimal_tripling_order(i + 1),
            _exact_cyclic_period(word),
            _exact_cyclic_period([x & 1 for x in word]),
            _exact_cyclic_period([x >> 1 for x in word]),
        )
        for i, word in enumerate(words)
    )


@dataclass(frozen=True, slots=True)
class CyclotomicTriplingClock:
    """Exact physical 3X phase, without materializing a large 3**exponent.

    ``offset`` counts *ordinary* tripling ticks after exponent ``2**level``.
    This is different from t->t+1 in the dyadic source.  Only low-decimal
    digits are claimed by this object; it contains no invented high digits.
    """

    level: int
    decimal_places: int
    offset: int
    phase: int
    residue: int

    @classmethod
    def from_dyadic_level(
        cls, level: int, decimal_places: int
    ) -> CyclotomicTriplingClock:
        if type(level) is not int or not 1 <= level <= 65_535:
            raise ValueError("source level outside Fermat bounded horizon")
        period = decimal_tripling_order(decimal_places)
        phase = int.__pow__(2, level, period)
        return cls(
            level,
            decimal_places,
            0,
            phase,
            int.__pow__(3, phase, 10**decimal_places),
        )

    @property
    def period(self) -> int:
        return decimal_tripling_order(self.decimal_places)

    def verify(self) -> None:
        if (
            type(self.level) is not int
            or not 1 <= self.level <= 65_535
            or type(self.offset) is not int
            or self.offset < 0
            or self.offset.bit_length() > 65_536
            or type(self.phase) is not int
            or type(self.residue) is not int
        ):
            raise ValueError("invalid physical source clock coordinates")
        period = self.period
        if self.phase != (int.__pow__(2, self.level, period) + self.offset) % period:
            raise ArithmeticError("physical cyclotomic phase does not belong to source")
        if self.residue != int.__pow__(3, self.phase, 10**self.decimal_places):
            raise ArithmeticError("cyclotomic source digit mismatch")

    def advance(self, ordinary_triplings: int) -> CyclotomicTriplingClock:
        if (
            type(ordinary_triplings) is not int
            or ordinary_triplings < 0
            or ordinary_triplings.bit_length() > 65_536
        ):
            raise ValueError("physical tripling duration is invalid")
        self.verify()
        phase = (self.phase + ordinary_triplings) % self.period
        new = CyclotomicTriplingClock(
            self.level,
            self.decimal_places,
            self.offset + ordinary_triplings,
            phase,
            int.__pow__(3, phase, 10**self.decimal_places),
        )
        new.verify()
        return new

    def dyadic_jump(self) -> CyclotomicTriplingClock:
        """Exactly 2**level ordinary tripling ticks, on the LOW suffix only."""
        return self.advance(1 << self.level)

    def carry_after(self, digits: int) -> int:
        if type(digits) is not int or not 1 <= digits <= self.decimal_places:
            raise ValueError("requested carry boundary outside the phase bank")
        self.verify()
        q = 10**digits
        return int(3 * (self.residue % q) // q)

    def carry_vector(self) -> tuple[int, ...]:
        self.verify()
        return tuple(
            3 * (self.residue % (10**k)) // (10**k)
            for k in range(1, self.decimal_places + 1)
        )

    def carry_h5(self) -> tuple[WalshH5, WalshH5]:
        return carry_h5(self.carry_vector(), 0)


@dataclass(frozen=True, slots=True)
class WeightedBinaryCarryBlock:
    """One exact known source word, or a truly unknown symbolic middle word."""

    start: int
    width: int
    source_value: int | None
    transfers: tuple[CarryFn, ...]

    def __post_init__(self) -> None:
        if (
            type(self.start) is not int
            or self.start < 0
            or self.start.bit_length() > 65_536
            or type(self.width) is not int
            or self.width < 1
            or self.width.bit_length() > 65_536
            or type(self.transfers) is not tuple
            or not 1 <= len(self.transfers) <= 27
            or any(
                type(fn) is not tuple
                or len(fn) != 3
                or any(type(c) is not int or not 0 <= c <= 2 for c in fn)
                for fn in self.transfers
            )
        ):
            raise ValueError("invalid bounded weighted carry block")
        if self.source_value is not None:
            if (
                type(self.source_value) is not int
                or self.source_value < 0
                or self.width > 65_536
                or self.source_value.bit_length() > self.width
            ):
                raise ValueError("invalid bounded known source word")
            value = 3 * self.source_value
            exact = tuple((value + c) >> self.width for c in (0, 1, 2))
            if self.transfers != (exact,):
                raise ValueError("carry transfer disagrees with known source")

    @property
    def known(self) -> bool:
        return self.source_value is not None

    @property
    def variable_name(self) -> str | None:
        return None if self.known else f"U[{self.start}:{self.start + self.width}]"

    def possible_outgoing(self, incoming: int) -> tuple[int, ...]:
        if type(incoming) is not int or incoming not in (0, 1, 2):
            raise ValueError("tripling carry ingress must be 0/1/2")
        return tuple(sorted({f[incoming] for f in self.transfers}))

    def emitted_value(self, incoming: int, outgoing: int) -> int | None:
        """Exact E=3U+cin-2**L*cout, conditional on a reachable port."""
        if type(outgoing) is not int or outgoing not in self.possible_outgoing(
            incoming
        ):
            raise ValueError("refused carry transfer")
        if self.source_value is None:
            return None  # retain the independent symbolic U, do not set it to 0
        value = 3 * self.source_value + incoming - (outgoing << self.width)
        if not 0 <= value < (1 << self.width):
            raise ArithmeticError("weighted emission is not a binary block")
        return value

    def emission_h5(
        self, incoming: int, outgoing: int
    ) -> tuple[WalshH5, WalshH5] | None:
        """Exact H5 only where every input digit is authenticated."""
        if self.source_value is None:
            if type(outgoing) is not int or outgoing not in self.possible_outgoing(
                incoming
            ):
                raise ValueError("refused carry transfer")
            return None
        self.emitted_value(incoming, outgoing)
        carry = incoming
        residue = self.source_value
        carries: list[int] = []
        for _ in range(self.width):
            residue, digit = divmod(residue, 2)
            carry = (3 * digit + carry) // 2
            carries.append(carry)
        if carry != outgoing:
            raise ArithmeticError("H5 carry and weighted action disagree")
        return carry_h5(tuple(carries), self.start)

    def signed_source(self, fold_width: int) -> int | None:
        if self.source_value is None:
            return None
        modulus = _signed_fold_modulus(fold_width)
        return (
            self.source_value
            * _signed_position_factor(self.start, fold_width)
            % modulus
        )

    def signed_output(
        self, incoming: int, outgoing: int, fold_width: int
    ) -> int | None:
        output = self.emitted_value(incoming, outgoing)
        if output is None:
            return None
        modulus = _signed_fold_modulus(fold_width)
        return output * _signed_position_factor(self.start, fold_width) % modulus


def _signed_fold_modulus(fold_width: int) -> int:
    if type(fold_width) is not int or not 1 <= fold_width <= 65_536:
        raise ValueError("signed fold width exceeds coordinate budget")
    return (1 << fold_width) + 1


def _signed_position_factor(position: int, fold_width: int) -> int:
    """Use 2**fold_width = -1 without powering an absolute source position."""
    modulus = _signed_fold_modulus(fold_width)
    phase = position % (2 * fold_width)
    magnitude = 1 << (phase % fold_width)
    return magnitude if phase < fold_width else modulus - magnitude


def _known_block(start: int, width: int, source_value: int) -> WeightedBinaryCarryBlock:
    if (
        type(width) is not int
        or not 1 <= width <= 65_536
        or type(source_value) is not int
        or source_value < 0
        or source_value.bit_length() > width
    ):
        raise ValueError("invalid authenticated source word")
    value = 3 * source_value
    fn: CarryFn = (value >> width, (value + 1) >> width, (value + 2) >> width)
    return WeightedBinaryCarryBlock(start, width, source_value, (fn,))


def _unknown_block(start: int, width: int) -> WeightedBinaryCarryBlock:
    if width <= 0:
        raise ValueError("unknown interval must have positive length")
    return WeightedBinaryCarryBlock(
        start, width, None, tuple(sorted(unknown_middle_transfer_set(2, width)))
    )


@dataclass(frozen=True, slots=True, weakref_slot=True)
class SourceWeightedTriplingAction:
    """Bilateral spatial 3X action retaining unknown U and all signed ports.

    The high prefix is independently Sturmian-certified by ``origin`` and
    filters the set of possible upper ingresses.  The whole word remains
    symbolic unless the authenticated blocks cover EVERY source bit.
    """

    origin: ThreePowerBilateralInteriorQuotient
    blocks: tuple[WeightedBinaryCarryBlock, ...]
    admissible_edges: tuple[tuple[tuple[int, int], ...], ...]
    _issuer: object = None

    @property
    def producer_verified(self) -> bool:
        return (
            self.origin.bilateral.binary.producer_verified
            and self.origin.bilateral.decimal.producer_verified
            and self.origin.binary_middle.source_authenticated
            and self.origin.decimal_middle.source_authenticated
            and (
                self.origin.binary_phase_bank is None
                or self.origin.binary_phase_bank.producer_verified
            )
            and (
                self.origin.decimal_phase_bank is None
                or self.origin.decimal_phase_bank.producer_verified
            )
            and harmonic_verified(self, self.issuer_payload(), issuer=_WEIGHTED_ISSUER)
        )

    def issuer_payload(self) -> tuple[object, ...]:
        binary = self.origin.bilateral.binary
        decimal = self.origin.bilateral.decimal
        bin_middle = self.origin.binary_middle
        dec_middle = self.origin.decimal_middle
        # Issuer seals themselves contain weakrefs/nonces. Snapshot ONLY the
        # authenticated immutable data, including the decimal constraints and
        # both temporally phased carry/H5 banks. Omitting decimal here would
        # recreate the independent-port integration error.
        positions = tuple(
            None
            if bank is None
            else (
                bank.base,
                bank.level,
                bank.depth,
                bank.source_prefix,
                bank.preperiod,
                bank.source_period,
                bank.source_phase,
                bank.carry_vector,
                bank.carry_h5,
            )
            for bank in (self.origin.binary_phase_bank, self.origin.decimal_phase_bank)
        )
        return (
            self.origin.bilateral.index,
            self.origin.bilateral.level,
            harmonic_payload(binary),
            harmonic_payload(decimal),
            tuple(
                (w.start, w.width, w.radix_value, w.transfer)
                for w in bin_middle.windows
            ),
            bin_middle.possible_actions,
            bin_middle.possible_high_ingress,
            tuple(
                (w.start, w.width, w.radix_value, w.transfer)
                for w in dec_middle.windows
            ),
            dec_middle.possible_actions,
            dec_middle.possible_high_ingress,
            positions,
            self.blocks,
            self.admissible_edges,
        )

    @property
    def index(self) -> int:
        return self.origin.bilateral.index

    @property
    def level(self) -> int:
        return self.origin.bilateral.level

    @property
    def fold_width(self) -> int:
        return 1 << self.index

    @property
    def terminal_status(self) -> str:
        # This is a one-step ordinary-tripling action, not the full Pépin fold.
        return "UNKNOWN"

    def physical_decimal_clock(self) -> CyclotomicTriplingClock:
        """Same source-owned 3X orbit as the decimal inward phase bank."""
        if not self.producer_verified or self.origin.decimal_phase_bank is None:
            raise ValueError("issued decimal cyclotomic bank required")
        bank = self.origin.decimal_phase_bank
        clock = CyclotomicTriplingClock.from_dyadic_level(self.level, bank.depth)
        if (
            clock.residue != bank.source_prefix
            or clock.carry_vector() != bank.carry_vector
        ):
            raise ArithmeticError("physical carry clock contradicts dyadic border")
        return clock

    @property
    def leading_resets_carry(self) -> bool:
        if not self.producer_verified:
            raise ValueError("unissued weighted source")
        return self.origin.bilateral.binary.high_forgets_ingress

    def signed_leading_overflow_options(self) -> tuple[tuple[int, int], ...]:
        """Guarded (top carry, signed fold), including growth beyond high block."""
        if not self.producer_verified:
            raise ValueError("unissued weighted source")
        modulus = (1 << self.fold_width) + 1
        shift = _signed_position_factor(
            self.origin.bilateral.binary.source_digits, self.fold_width
        )
        return tuple(
            sorted(
                (co, co * shift % modulus)
                for co in {edge[1] for edge in self.admissible_edges[-1]}
            )
        )

    @property
    def unknown_blocks(self) -> tuple[WeightedBinaryCarryBlock, ...]:
        return tuple(b for b in self.blocks if not b.known)

    @property
    def source_signed_known_sum(self) -> int:
        """Sum ONLY independently authenticated source positions."""
        if not self.producer_verified:
            raise ValueError("unissued weighted source")
        return sum(
            b.signed_source(self.fold_width) or 0 for b in self.blocks if b.known
        ) % ((1 << self.fold_width) + 1)

    @property
    def full_source_fold_proven(self) -> bool:
        return self.producer_verified and not self.unknown_blocks

    def unresolved_signed_variables(self) -> tuple[tuple[str, int, int], ...]:
        """(symbol U, coefficient mod Fermat modulus, exact digit width).

        A variable has not been inferred equal to zero. The coefficient is
        always retained even when the high carry is RESET and every H5 mask
        visible at the borders is known.
        """
        if not self.producer_verified:
            raise ValueError("unissued weighted source")
        return tuple(
            (
                b.variable_name or "",
                _signed_position_factor(b.start, self.fold_width),
                b.width,
            )
            for b in self.blocks
            if not b.known
        )

    def conditional_signed_ports(
        self,
    ) -> tuple[tuple[tuple[int, int, int | None, int | None], ...], ...]:
        """For each segment: (cin,cout,signed source,signed target).

        ``None`` is an algebraic unknown, NEVER a zero contribution. The
        signed source coordinate distinguishes two words with identical H5.
        """
        if not self.producer_verified:
            raise ValueError("unissued weighted source")
        answer: list[tuple[tuple[int, int, int | None, int | None], ...]] = []
        for block, edges in zip(self.blocks, self.admissible_edges, strict=True):
            signed = block.signed_source(self.fold_width)
            answer.append(
                tuple(
                    (ci, co, signed, block.signed_output(ci, co, self.fold_width))
                    for ci, co in edges
                )
            )
        return tuple(answer)

    def demand_two_sided_source_cylinder(self) -> FermatTwoSidedSourceCylinder:
        """Demand joint CRT/radial source cylinder and conditional 2w fibers.

        Only independently authenticated source intervals are admitted.
        No source or Fermat-modulus squaring is performed.
        """
        from number_compiler.sequences.power_numbers.three_power_two_sided_cylinder import (
            demand_two_sided_source_cylinder,
        )

        return demand_two_sided_source_cylinder(self)

    def demand_source_restricted_phase_relation(
        self, *, max_fibers: int = 64, inward_boundaries: int = 8
    ) -> SourceRestrictedPhaseRelation:
        """Source-authoritative join: CRT, radial guards, signed 2w counts."""
        from number_compiler.sequences.power_numbers.three_power_signed_phase import (
            demand_source_restricted_phase_relation,
        )

        return demand_source_restricted_phase_relation(
            self, max_fibers=max_fibers, inward_boundaries=inward_boundaries
        )

    def demand_signed_phase_count_port(self) -> SourceSignedPhaseCountPort:
        """Demand the exact positional count quotient, retaining unknown intervals."""
        from number_compiler.sequences.power_numbers.three_power_signed_phase import (
            demand_signed_phase_counts,
        )

        return demand_signed_phase_counts(self)

    def complete_tripling_fold(self) -> tuple[int, int]:
        """Exact small full-word check, only with complete source coverage.

        This is one ordinary 3X step. It CANNOT issue a Fermat prime bit.
        No direct source or Fermat-modulus square occurs here.
        """
        if not self.full_source_fold_proven:
            raise ValueError("complete signed source unavailable: symbolic middle")
        source = sum((b.source_value or 0) << b.start for b in self.blocks)
        carry = 0
        output = 0
        for block, edges in zip(self.blocks, self.admissible_edges, strict=True):
            matches = [co for ci, co in edges if ci == carry]
            if len(matches) != 1:
                raise ArithmeticError("nonunique fully authenticated carry path")
            value = block.emitted_value(carry, matches[0])
            if value is None:
                raise ArithmeticError("full source port unexpectedly became symbolic")
            output += value << block.start
            carry = matches[0]
        output += carry << self.origin.bilateral.binary.source_digits
        if output != 3 * source:
            raise ArithmeticError("signed carry emission disagrees with 3X")
        modulus = (1 << self.fold_width) + 1
        return source % modulus, output % modulus

    def demand_inward_source_refinement(
        self,
        *,
        additional_binary_places: int = 1,
        additional_decimal_places: int = 0,
    ) -> SourceWeightedTriplingAction:
        """Advance ONLY certified inward phase precision at the SAME source.

        This is a demand-driven guarded source refinement, not a proof of
        spatial or temporal period. Existing independently authenticated
        windows are replayed; a missing next source digit may require an
        additional cyclotomic precision demand, never a Fermat square.
        """
        if not self.producer_verified:
            raise ValueError("unissued inward refinement source")
        if any(
            type(v) is not int or not 0 <= v <= 256
            for v in (additional_binary_places, additional_decimal_places)
        ):
            raise ValueError("inward precision refinement outside demand budget")
        binary = self.origin.binary_phase_bank
        decimal = self.origin.decimal_phase_bank
        if binary is None or decimal is None:
            raise ValueError("inward refinement requires both phase clocks")
        next_binary = binary.depth + additional_binary_places
        next_decimal = decimal.depth + additional_decimal_places
        if next_binary > 4096 or next_decimal > 512:
            raise ValueError("inward phase precision exceeds source budget")
        if not (additional_binary_places or additional_decimal_places):
            return self
        # Windows entirely inside an already-certified prefix are subsumed
        # by the new longer prefix. Separately authenticated later islands
        # must survive, otherwise this would broaden the source language.
        b_windows = tuple(
            (w.start, w.width)
            for w in self.origin.binary_middle.windows
            if w.start + w.width > binary.depth
        )
        d_windows = tuple(
            (w.start, w.width)
            for w in self.origin.decimal_middle.windows
            if w.start + w.width > decimal.depth
        )
        b_border = self.origin.bilateral.binary
        d_border = self.origin.bilateral.decimal
        refined = demand_signed_tripling_action(
            self.index,
            self.level,
            phase_binary_places=next_binary,
            phase_decimal_places=next_decimal,
            binary_windows=b_windows,
            decimal_windows=d_windows,
            low_binary_places=b_border.low_places,
            low_decimal_places=d_border.low_places,
            high_binary_places=b_border.high_places,
            high_decimal_places=d_border.high_places,
        )
        if (
            refined.origin.binary_phase_bank is None
            or refined.origin.decimal_phase_bank is None
            or refined.origin.binary_phase_bank.source_prefix % (1 << binary.depth)
            != binary.source_prefix
            or refined.origin.decimal_phase_bank.source_prefix % (10**decimal.depth)
            != decimal.source_prefix
        ):
            raise ArithmeticError("refined source lost a previous certified phase")
        # Every previous authenticated binary island must survive exactly,
        # including requested non-prefix windows and the leading radial block.
        for earlier in self.blocks:
            if earlier.source_value is None:
                continue
            coverage = earlier.start
            for newer in refined.blocks:
                lo = max(coverage, newer.start)
                hi = min(earlier.start + earlier.width, newer.start + newer.width)
                if lo >= hi:
                    continue
                if newer.source_value is None:
                    raise ArithmeticError("source refinement dropped a known island")
                mask = (1 << (hi - lo)) - 1
                old_bits = (earlier.source_value >> (lo - earlier.start)) & mask
                new_bits = (newer.source_value >> (lo - newer.start)) & mask
                if old_bits != new_bits:
                    raise ArithmeticError("source refinement changed an issued digit")
                coverage = hi
                if coverage == earlier.start + earlier.width:
                    break
            if coverage != earlier.start + earlier.width:
                raise ArithmeticError("source refinement lost an issued interval")
        return refined

    def demanded_dyadic_endpoint(self, steps: int = 1) -> SourceWeightedTriplingAction:
        """Demand another certified endpoint, NOT an all-intermediate proof.

        Checks exactly the low-prime cyclotomic temporal jump and obtains a
        separately authenticated high Sturmian guard at the new level.
        """
        if not self.producer_verified or type(steps) is not int or steps < 0:
            raise ValueError("invalid guarded dyadic endpoint demand")
        if steps == 0:
            return self
        next_level = self.level + steps
        if next_level >= (1 << self.index):
            raise ValueError("dyadic endpoint lies outside Fermat source horizon")
        lower = self.origin
        binary = lower.binary_phase_bank
        decimal = lower.decimal_phase_bank
        if binary is None or decimal is None:
            raise ValueError("powering requires certified binary/decimal phase banks")
        candidate = demand_signed_tripling_action(
            self.index,
            next_level,
            phase_binary_places=binary.depth,
            phase_decimal_places=decimal.depth,
            low_binary_places=lower.bilateral.binary.low_places,
            low_decimal_places=lower.bilateral.decimal.low_places,
            high_binary_places=lower.bilateral.binary.high_places,
            high_decimal_places=lower.bilateral.decimal.high_places,
        )
        binary_next = binary.temporal_power(steps)
        decimal_next = decimal.temporal_power(steps)
        next_bin = candidate.origin.binary_phase_bank
        next_dec = candidate.origin.decimal_phase_bank
        if next_bin is None or next_dec is None:
            raise ArithmeticError("dyadic endpoint lost its authenticated phase bank")
        if (
            binary_next.source_prefix != next_bin.source_prefix
            or decimal_next.source_prefix != next_dec.source_prefix
        ):
            raise ArithmeticError(
                "temporal bank and independently certified border disagree"
            )
        physical = CyclotomicTriplingClock.from_dyadic_level(self.level, decimal.depth)
        # The physical exponent displacement is 2**(t+s)-2**t; computing
        # it as an integer is cheap even when the raw source has billions of bits.
        physical = physical.advance((1 << next_level) - (1 << self.level))
        if physical.residue != next_dec.source_prefix:
            raise ArithmeticError(
                "physical 3X orbit contradicts dyadic source endpoint"
            )
        return candidate


_WEIGHTED_ISSUER = new_harmonic_issuer(SourceWeightedTriplingAction)


def signed_action_from_interior(
    origin: ThreePowerBilateralInteriorQuotient,
) -> SourceWeightedTriplingAction:
    """Re-use the NC15 inward phase/windows and *same* two radial borders."""
    if type(origin) is not ThreePowerBilateralInteriorQuotient:
        raise TypeError("weighted action requires an issued bilateral occurrence")
    origin.__post_init__()
    border = origin.bilateral.binary
    relation = origin.binary_middle
    blocks: list[WeightedBinaryCarryBlock] = [
        _known_block(0, border.low_places, border.low_source)
    ]
    cursor = border.low_places
    high_start = border.source_digits - border.high_places
    for island in relation.windows:
        if island.start > cursor:
            blocks.append(_unknown_block(cursor, island.start - cursor))
        blocks.append(_known_block(island.start, island.width, island.radix_value))
        cursor = island.start + island.width
    if cursor < high_start:
        blocks.append(_unknown_block(cursor, high_start - cursor))
    blocks.append(_known_block(high_start, border.high_places, border.source_top))
    if any(b.start + b.width != next_b.start for b, next_b in pairwise(blocks)):
        raise ArithmeticError("source coverage is not contiguous")
    if blocks[-1].start + blocks[-1].width != border.source_digits:
        raise ArithmeticError("weighted source length does not match radial width")
    reachable: list[frozenset[int]] = [frozenset((0,))]
    for block in blocks:
        incoming = reachable[-1]
        if block.start == high_start:
            incoming = incoming.intersection(relation.possible_high_ingress)
        out = frozenset(co for ci in incoming for co in block.possible_outgoing(ci))
        if not out:
            raise ArithmeticError("no weighted carry path satisfies both borders")
        reachable.append(out)
    valid = set(reachable[-1])
    result_edges: list[tuple[tuple[int, int], ...]] = [()] * len(blocks)
    for i in reversed(range(len(blocks))):
        block = blocks[i]
        ingresses = reachable[i]
        if block.start == high_start:
            ingresses = ingresses.intersection(relation.possible_high_ingress)
        edges = tuple(
            sorted(
                (ci, co)
                for ci in ingresses
                for co in block.possible_outgoing(ci)
                if co in valid
            )
        )
        if not edges:
            raise ArithmeticError(
                "two-sided backward carry propagation emptied a block"
            )
        result_edges[i] = edges
        valid = {ci for ci, _ in edges}
    if valid != {0}:
        raise ArithmeticError("source carry must begin with exactly zero")
    # Authenticate H5 packets of all known islands against the OLD source
    # publisher. The missing middle's harmonic remains None, never zero.
    first = blocks[0]
    low_carry = first.possible_outgoing(0)[0]
    if first.emission_h5(0, low_carry) != border.low_h5:
        raise ArithmeticError("weighted low carry H5 disagrees with original border")
    for island in relation.windows:
        island_block = next(
            (b for b in blocks if b.start == island.start and b.width == island.width),
            None,
        )
        if (
            island_block is None
            or not island_block.known
            or island_block.source_value != island.radix_value
        ):
            raise ArithmeticError("weighted source island is not authenticated")
        for ingress in range(3):
            outgoing = island_block.possible_outgoing(ingress)[0]
            if (
                island_block.emission_h5(ingress, outgoing)
                != island.carry_h5_by_ingress[ingress]
            ):
                raise ArithmeticError("weighted carry H5 contradicts certified island")
    # Every admitted ingress to the leading block must produce the CERTIFIED
    # target leading prefix. RESET at the far side alone is not sufficient.
    high_edges = result_edges[-1]
    grow = border.target_digits - border.source_digits
    for ci, co in high_edges:
        high = 3 * border.source_top + ci
        if high // 2**grow != border.target_top or high // 2**border.high_places != co:
            raise ArithmeticError(
                "weighted high-block emission violates Sturmian guard"
            )
        if blocks[-1].emission_h5(ci, co) != dict(border.high_h5_options)[ci]:
            raise ArithmeticError("weighted high H5 contradicts certified border")
    result = SourceWeightedTriplingAction(origin, tuple(blocks), tuple(result_edges))
    issue_harmonic(result, result.issuer_payload(), issuer=_WEIGHTED_ISSUER)
    return result


def demand_signed_tripling_action(
    index: int,
    level: int,
    *,
    phase_binary_places: int = 64,
    phase_decimal_places: int = 6,
    binary_windows: tuple[tuple[int, int], ...] = (),
    decimal_windows: tuple[tuple[int, int], ...] = (),
    low_binary_places: int = 12,
    low_decimal_places: int = 4,
    high_binary_places: int = 8,
    high_decimal_places: int = 4,
) -> SourceWeightedTriplingAction:
    """Fast source-border entry point: NEVER invokes Pépin/eager squares."""
    interior = demand_three_power_inward_phase_quotient(
        index,
        level,
        phase_binary_places=phase_binary_places,
        phase_decimal_places=phase_decimal_places,
        binary_windows=binary_windows,
        decimal_windows=decimal_windows,
        low_binary_places=low_binary_places,
        low_decimal_places=low_decimal_places,
        high_binary_places=high_binary_places,
        high_decimal_places=high_decimal_places,
    )
    return signed_action_from_interior(interior)


__all__ = [
    "CyclotomicTriplingClock",
    "SourceWeightedTriplingAction",
    "WeightedBinaryCarryBlock",
    "decimal_tripling_order",
    "demand_signed_tripling_action",
    "exact_physical_carry_periods",
    "signed_action_from_interior",
]
