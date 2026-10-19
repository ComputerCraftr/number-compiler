"""Two-sided radix-2/10 constraints for the ordinary 3X source action.

The low dyadic exponent source determines its complete low b-adic orbit and
multiplication carry. Certified radial leading digits of 3**k and 3**(k+1)
restrict which carry can enter the upper digit block. The (unobserved)
interior is an exact finite *set* of carry transfers, powered by relation
composition over its enormous length; it is not guessed to repeat a word.

The dyadic transition 3**(2**t) -> 3**(2**(t+1)) is NOT an ordinary tripling:
this relation is one exact 3X letter that a later source-guarded temporal
morphism may consume. No unsupported middle digits or prime bit are emitted.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING

from number_compiler.arithmetic.carry.tripling_transfer import (
    IDENTITY,
    CarryFn,
    compose_sets,
    compose_transfer,
    digit_transfer,
    unknown_middle_transfer_set,
)
from number_compiler.arithmetic.fields.homogeneous_growth import (
    GrowthArithmeticEvaluator,
    HomogeneousGrowthScale,
)
from number_compiler.arithmetic.fields.radial_sturmian import RadialSturmianClock
from number_compiler.arithmetic.fields.three_power_radix import decimal_tripling_order
from number_compiler.arithmetic.fields.walsh import WalshH5, walsh_h5_at_offset
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.power_numbers._harmonic_authority import (
    harmonic_payload,
    harmonic_verified,
    issue_harmonic,
    new_harmonic_issuer,
)
from number_compiler.sequences.power_numbers.source_matrix import (
    FermatMultiradixPort,
    demand_three_power_multiradix_port,
)


def _low_carries(source_low: int, base: int, width: int) -> tuple[int, ...]:
    carry = 0
    result: list[int] = []
    for _ in range(width):
        digit = source_low % base
        source_low //= base
        carry = (3 * digit + carry) // base
        result.append(carry)
    return tuple(result)


def carry_h5(carries: tuple[int, ...], offset: int) -> tuple[WalshH5, WalshH5]:
    # Carry is ternary, so retain BOTH binary planes rather than collapsing
    # RESET2 to a Boolean. The packet is harmonics of a known border ONLY.
    low_mask = sum((c & 1) << j for j, c in enumerate(carries))
    upper_mask = sum(((c >> 1) & 1) << j for j, c in enumerate(carries))
    return (
        walsh_h5_at_offset(low_mask, len(carries), offset),
        walsh_h5_at_offset(upper_mask, len(carries), offset),
    )


if TYPE_CHECKING:
    from number_compiler.sequences.power_numbers.three_power_inward_phase_bank import (
        InwardTemporalPhaseBank,
    )


MAX_BINARY_WINDOW_PRECISION = 4096
MAX_DECIMAL_WINDOW_PRECISION = 512


def source_radix_prefix(level: int, base: int, places: int) -> int:
    """Exact low requested 3**(2**t) digits; no candidate-modulus powering."""
    if (
        type(places) is not int
        or places < 1
        or type(level) is not int
        or level < 1
        or level.bit_length() > 4096
    ):
        raise ValueError("invalid source digit demand")
    if type(base) is not int:
        raise TypeError("source radix requires an exact integer")
    if base == 2:
        if places > MAX_BINARY_WINDOW_PRECISION:
            raise ValueError("source-2-adic-window-precision-budget")
        from number_compiler.sequences.power_numbers.three_dyadic_boolean_counter import (
            two_adic_unit_binomial,
        )

        shift = level + 2
        if shift >= places:
            return 1
        return 1 + (two_adic_unit_binomial(level, places - shift) << shift)
    if base == 10:
        if places > MAX_DECIMAL_WINDOW_PRECISION:
            raise ValueError("source-decimal-orbit-precision-budget")
        # The exact order of 3 modulo 10**j contains both primary factors;
        # use dyadic exponent reduction modulo the order, not 2**level steps.
        order = decimal_tripling_order(places)
        exponent = pow(2, level, order)
        modulus: int = 10**places
        return pow(3, exponent, modulus)
    raise ValueError("unsupported source radix")


@dataclass(frozen=True, slots=True)
class CertifiedMiddleWindow:
    """True digits with a source-derived radix-orbit proof at one interval."""

    start: int
    width: int
    radix_value: int
    transfer: CarryFn
    carry_h5_by_ingress: tuple[tuple[WalshH5, WalshH5], ...]


@dataclass(frozen=True, slots=True, weakref_slot=True)
class RefinedMiddleRelation:
    """Set-valued carry constraint after inserting authenticated source windows."""

    border: RadixBilateralTripling
    windows: tuple[CertifiedMiddleWindow, ...]
    possible_actions: tuple[CarryFn, ...]
    possible_high_ingress: tuple[int, ...]
    _issuer: object = field(default=None, init=False, repr=False, compare=False)

    @property
    def source_authenticated(self) -> bool:
        return self.border.producer_verified and harmonic_verified(
            self, self.structural_payload(), issuer=_REFINED_MIDDLE_ISSUER
        )

    def structural_payload(self) -> tuple[object, ...]:
        return (
            *harmonic_payload(self.border),
            self.windows,
            self.possible_actions,
            self.possible_high_ingress,
        )

    @property
    def complete_source(self) -> bool:
        if not self.source_authenticated:
            raise ValueError("unissued or changed source windows")
        cursor = self.border.low_places
        for item in self.windows:
            if item.start != cursor:
                return False
            cursor += item.width
        return cursor == self.border.source_digits - self.border.high_places

    @property
    def terminal_status(self) -> str:
        return "UNKNOWN"


_REFINED_MIDDLE_ISSUER = new_harmonic_issuer(RefinedMiddleRelation)


def _validate_middle_windows_shape(windows: tuple[tuple[int, int], ...]) -> None:
    if type(windows) is not tuple or len(windows) > 9:
        raise ValueError("invalid middle source-window request")
    for item in windows:
        if (
            type(item) is not tuple
            or len(item) != 2
            or any(type(value) is not int for value in item)
        ):
            raise TypeError("middle window is (absolute-start,width)")
        start, width = item
        if start < 0 or width < 1:
            raise ValueError("source window is outside the unknown interior")


def refine_middle_source_windows(
    border: RadixBilateralTripling,
    windows: tuple[tuple[int, int], ...],
) -> RefinedMiddleRelation:
    """Propagate low carry through known islands and unknown gaps to high.

    All lower digits of each witness are evaluated from the source's exact
    prime-radix orbit; unknown gaps are composed as set-valued transfer powers.
    Carries and H5 of a witnessed island are conditional on its ingress.
    This does not invent an XOR mask or a complete full-word Walsh packet.
    """
    if type(border) is not RadixBilateralTripling or not border.producer_verified:
        raise TypeError("middle refinement requires an authenticated border")
    _validate_middle_windows_shape(windows)
    left = border.low_places
    right = border.source_digits - border.high_places
    if left > right:
        raise ValueError("negative interior interval")
    possible = frozenset((IDENTITY,))
    observed: list[CertifiedMiddleWindow] = []
    prefix = 0
    if windows:
        previous = left
        for start, width in windows:
            if width <= 0 or start < previous or start + width > right:
                raise ValueError("source window is outside the unknown interior")
            previous = start + width
        precision = max(start + width for start, width in windows)
        prefix = source_radix_prefix(border.level, border.base, precision)
    for item in windows:
        if type(item) is not tuple or len(item) != 2:
            raise TypeError("middle window is (absolute-start,width)")
        start, width = item
        if (
            type(start) is not int
            or type(width) is not int
            or width <= 0
            or start < left
            or start + width > right
        ):
            raise ValueError("source window is outside the unknown interior")
        if start < left:
            raise ValueError("interior source windows overlap")
        possible = compose_sets(
            possible, unknown_middle_transfer_set(border.base, start - left)
        )
        value = prefix // border.base**start % border.base**width
        digits: list[int] = []
        remaining = value
        for _ in range(width):
            remaining, digit = divmod(remaining, border.base)
            digits.append(digit)
        transfer = IDENTITY
        for digit in digits:
            transfer = compose_transfer(transfer, digit_transfer(border.base, digit))
        h5: list[tuple[WalshH5, WalshH5]] = []
        for incoming in range(3):
            carry = incoming
            carried: list[int] = []
            for digit in digits:
                carry = (3 * digit + carry) // border.base
                carried.append(carry)
            h5.append(carry_h5(tuple(carried), start))
        observed.append(CertifiedMiddleWindow(start, width, value, transfer, tuple(h5)))
        possible = compose_sets(possible, frozenset((transfer,)))
        left = start + width
    possible = compose_sets(
        possible, unknown_middle_transfer_set(border.base, right - left)
    )
    allowed = tuple(
        sorted(
            f for f in possible if f[border.low_carry] in border.high_ingress_options
        )
    )
    if not allowed:
        raise ArithmeticError(
            "middle source observations are inconsistent with radial borders"
        )
    result = RefinedMiddleRelation(
        border,
        tuple(observed),
        allowed,
        tuple(sorted({f[border.low_carry] for f in allowed})),
    )
    issue_harmonic(result, result.structural_payload(), issuer=_REFINED_MIDDLE_ISSUER)
    return result


@dataclass(frozen=True, slots=True, weakref_slot=True)
class RadixBilateralTripling:
    """Exact conditional low->middle->high transfer of ONE ordinary 3X."""

    index: int
    level: int
    base: int
    low_places: int
    high_places: int
    source_digits: int
    target_digits: int
    low_source: int
    low_product: int
    low_carry: int
    source_top: int
    target_top: int
    unknown_middle_length: int
    high_ingress_options: tuple[int, ...]
    allowed_middle_actions: tuple[CarryFn, ...]
    low_h5: tuple[WalshH5, WalshH5]
    high_h5_options: tuple[tuple[int, tuple[WalshH5, WalshH5]], ...]
    _issuer: object = field(default=None, init=False, repr=False, compare=False)

    @property
    def producer_verified(self) -> bool:
        return harmonic_verified(self, harmonic_payload(self), issuer=_BILATERAL_ISSUER)

    @property
    def low_carry_vector(self) -> tuple[int, ...]:
        """Actual per-position low carry orbit, including carry at 10**2."""
        return _low_carries(self.low_source, self.base, self.low_places)

    @property
    def forced_middle_action(self) -> CarryFn | None:
        return (
            self.allowed_middle_actions[0]
            if len(self.allowed_middle_actions) == 1
            else None
        )

    @property
    def forced_high_ingress(self) -> int | None:
        values = {fn[self.low_carry] for fn in self.allowed_middle_actions}
        return next(iter(values)) if len(values) == 1 else None

    @property
    def high_forgets_ingress(self) -> bool:
        """All carry ingress choices yield the same *upper carry*, not digits."""
        block = self.source_top
        h = self.high_places
        carry_out: set[int] = set()
        for incoming in range(3):
            # Full outgoing carry computed on the same block with ingress.
            carry = incoming
            v = block
            for _ in range(h):
                d = v % self.base
                v //= self.base
                carry = (3 * d + carry) // self.base
            carry_out.add(carry)
        return len(carry_out) == 1

    @property
    def candidate_high_carries(self) -> tuple[int, ...]:
        return tuple(sorted({f[self.low_carry] for f in self.allowed_middle_actions}))

    @property
    def middle_h5_authenticated(self) -> bool:
        return False

    def condition_on_full_h5(
        self,
        full_h5: tuple[WalshH5, WalshH5],
        *,
        max_middle_digits: int = 10,
    ) -> tuple[CarryFn, ...]:
        """Condition possible transfers on a caller-supplied full carry H5.

        The returned alternatives are conditional on this value, not a source
        certificate. Low/high borders do not authenticate a full-word packet.
        Long gaps refuse rather than pretending the middle H5 is zero.
        """
        if not self.producer_verified:
            raise ValueError("unissued bilateral source observation")
        if (
            type(full_h5) is not tuple
            or len(full_h5) != 2
            or any(type(p) is not WalshH5 or p.length_mod6 != 0 for p in full_h5)
        ):
            raise TypeError("harmonic target requires two absolute WalshH5 packets")
        if (
            type(max_middle_digits) is not int
            or max_middle_digits < 0
            or max_middle_digits > 10
        ):
            raise ValueError("harmonic demand budget outside supported range")
        if self.unknown_middle_length > max_middle_digits:
            raise ValueError("middle-harmonic-precision-budget")
        # (whole middle CarryFn, actual carry, Phi2lo,Phi3a-lo,Phi3b-lo,
        #  Phi2hi,Phi3a-hi,Phi3b-hi). Every digit is a possible base-b digit;
        # the calculation does NOT sample the source or assume a repeated word.
        states: set[tuple[CarryFn, int, tuple[int, int, int, int, int, int]]] = {
            (IDENTITY, self.low_carry, (0, 0, 0, 0, 0, 0))
        }
        for step in range(self.unknown_middle_length):
            position = self.low_places + step
            sign = 1 if not position % 2 else -1
            phase = position % 3
            pa, pb = (1, 0) if phase == 0 else ((0, 1) if phase == 1 else (-1, -1))
            following: set[tuple[CarryFn, int, tuple[int, int, int, int, int, int]]] = (
                set()
            )
            for action, carry, packet in states:
                for digit in range(self.base):
                    nxt = (3 * digit + carry) // self.base
                    action_next = compose_transfer(
                        action, digit_transfer(self.base, digit)
                    )
                    low_plane, hi_plane = nxt & 1, (nxt >> 1) & 1
                    delta = (
                        (packet[0] + sign * low_plane) % 5,
                        (packet[1] + pa * low_plane) % 5,
                        (packet[2] + pb * low_plane) % 5,
                        (packet[3] + sign * hi_plane) % 5,
                        (packet[4] + pa * hi_plane) % 5,
                        (packet[5] + pb * hi_plane) % 5,
                    )
                    following.add((action_next, nxt, delta))
                    if len(following) > 100_000:
                        raise ValueError("middle-harmonic-state-budget")
            states = following
        accepted: set[CarryFn] = set()
        lookup = dict(self.high_h5_options)
        for action, carry, packet in states:
            if action not in self.allowed_middle_actions or carry not in lookup:
                continue
            predicted: list[WalshH5] = []
            for plane in range(2):
                low = self.low_h5[plane]
                high = lookup[carry][plane]
                j = plane * 3
                predicted.append(
                    WalshH5(
                        0,
                        (low.phi2 + packet[j] + high.phi2) % 5,
                        (low.phi3_a + packet[j + 1] + high.phi3_a) % 5,
                        (low.phi3_b + packet[j + 2] + high.phi3_b) % 5,
                    )
                )
            if tuple(predicted) == full_h5:
                accepted.add(action)
        return tuple(sorted(accepted))

    @property
    def terminal_status(self) -> str:
        return "UNKNOWN"


_BILATERAL_ISSUER = new_harmonic_issuer(RadixBilateralTripling)


def _build_radix_border(
    index: int,
    level: int,
    port: FermatMultiradixPort,
    high_places: int,
    source_prefix: int,
    source_digits: int,
    target_prefix: int,
    target_digits: int,
) -> RadixBilateralTripling:
    if not port.producer_verified:
        raise ValueError("unissued low-radix source port")
    base, low_places = port.base, port.places
    if base not in (2, 10) or high_places < 1 or high_places > 32:
        raise ValueError("unsupported radial tripling border")
    middle = source_digits - low_places - high_places
    if middle < 0:
        raise ValueError("radial and low windows overlap; use full exact arithmetic")
    b = base**low_places
    low = port.source_residue
    low_carry = (3 * low) // b
    if port.boundaries[-1].tripling_carry != low_carry:
        raise ArithmeticError("Collatz source carry and radix prefix disagree")
    # Upper high block receives one unknown middle carry. The leading target
    # prefix and its certified width restrict it from the opposite side.
    grow = target_digits - source_digits
    if grow < 0 or grow > (2 if base == 2 else 1):
        raise ArithmeticError("tripling width growth outside the radix bound")
    high_ingress: list[int] = []
    modulus = base**high_places
    for carry in range(3):
        output = 3 * source_prefix + carry
        if grow:
            if not (modulus * base ** (grow - 1) <= output < modulus * base**grow):
                continue
        elif not (0 <= output < modulus):
            continue
        got = output // base**grow
        if got == target_prefix:
            high_ingress.append(carry)
    if not high_ingress:
        raise ArithmeticError("source/target certified radial borders are incompatible")
    possible = unknown_middle_transfer_set(base, middle)
    allowed: tuple[CarryFn, ...] = tuple(
        sorted(fn for fn in possible if fn[low_carry] in high_ingress)
    )
    if not allowed:
        raise ArithmeticError("bilateral carry relation has no admissible middle")
    low_carries = _low_carries(low, base, low_places)
    if low_carries[-1] != low_carry:
        raise ArithmeticError("low carry-stencil mismatch")
    upper_packets: list[tuple[int, tuple[WalshH5, WalshH5]]] = []
    receiving_carries: set[int] = {fn[low_carry] for fn in allowed}
    for cin in sorted(receiving_carries):
        state = cin
        temp = source_prefix
        carries: list[int] = []
        for _ in range(high_places):
            digit = temp % base
            temp //= base
            state = (3 * digit + state) // base
            carries.append(state)
        upper_packets.append(
            (cin, carry_h5(tuple(carries), source_digits - high_places))
        )
    result = RadixBilateralTripling(
        index,
        level,
        base,
        low_places,
        high_places,
        source_digits,
        target_digits,
        low,
        3 * low % b,
        low_carry,
        source_prefix,
        target_prefix,
        middle,
        tuple(high_ingress),
        allowed,
        carry_h5(low_carries, 0),
        tuple(upper_packets),
    )
    issue_harmonic(result, harmonic_payload(result), issuer=_BILATERAL_ISSUER)
    return result


@dataclass(frozen=True, slots=True)
class ThreePowerBilateralQuotient:
    """Joint necessary constraints; no invented cross-radix middle digit."""

    index: int
    level: int
    binary: RadixBilateralTripling
    decimal: RadixBilateralTripling

    def __post_init__(self) -> None:
        if type(self.index) is not int or type(self.level) is not int:
            raise TypeError("bilateral source coordinates require exact integers")
        if (
            type(self.binary) is not RadixBilateralTripling
            or type(self.decimal) is not RadixBilateralTripling
        ):
            raise TypeError("bilateral source needs two issued radix borders")
        if not self.binary.producer_verified or not self.decimal.producer_verified:
            raise ValueError("unissued bilateral source border")
        if (self.binary.base, self.decimal.base) != (2, 10):
            raise ValueError("bilateral joint quotient needs base 2 and base 10")
        if (self.binary.index, self.binary.level) != (self.index, self.level):
            raise ValueError("binary border has wrong source identity")
        if (self.decimal.index, self.decimal.level) != (self.index, self.level):
            raise ValueError("decimal border has wrong source identity")
        j = min(self.binary.low_places, self.decimal.low_places)
        overlap = 1 << j
        # Decimal low residues and binary low residues share their 2-part.
        if self.binary.low_source % overlap != self.decimal.low_source % overlap:
            raise ArithmeticError("binary/decimal low source residues disagree")
        if self.binary.low_product % overlap != self.decimal.low_product % overlap:
            raise ArithmeticError("binary/decimal low successor residues disagree")

    @property
    def terminal_status(self) -> str:
        return "UNKNOWN"


@dataclass(frozen=True, slots=True)
class ThreePowerBilateralInteriorQuotient:
    bilateral: ThreePowerBilateralQuotient
    binary_middle: RefinedMiddleRelation
    decimal_middle: RefinedMiddleRelation
    # Local import inside constructors prevents an orbit/border import cycle.
    # These fields authenticate *one shared dyadic source level*, not an
    # independently guessed binary phase and decimal phase.
    binary_phase_bank: InwardTemporalPhaseBank | None = None
    decimal_phase_bank: InwardTemporalPhaseBank | None = None

    def __post_init__(self) -> None:
        if type(self.bilateral) is not ThreePowerBilateralQuotient:
            raise TypeError("interior needs the bilateral source occurrence")
        self.bilateral.__post_init__()
        for relation, border, bank in (
            (self.binary_middle, self.bilateral.binary, self.binary_phase_bank),
            (self.decimal_middle, self.bilateral.decimal, self.decimal_phase_bank),
        ):
            if (
                type(relation) is not RefinedMiddleRelation
                or relation.border is not border
                or not relation.source_authenticated
            ):
                raise ValueError("interior windows belong to another source border")
            if bank is not None and (
                not bank.producer_verified
                or bank.base != border.base
                or bank.level != border.level
                or not border.low_places
                <= bank.depth
                <= border.source_digits - border.high_places
            ):
                raise ValueError("inward phase belongs to another source occurrence")

    @property
    def partial_signed_fermat_contribution(self) -> int | None:
        """Signed contribution of known low binary bits, not the full fold."""
        if self.binary_phase_bank is None:
            return None
        return self.binary_phase_bank.partial_signed_fermat_contribution(
            self.bilateral.index
        )

    @property
    def terminal_status(self) -> str:
        return "UNKNOWN"


def demand_three_power_bilateral_interior(
    index: int,
    level: int,
    *,
    binary_windows: tuple[tuple[int, int], ...] = (),
    decimal_windows: tuple[tuple[int, int], ...] = (),
    low_binary_places: int = 12,
    low_decimal_places: int = 4,
    high_binary_places: int = 8,
    high_decimal_places: int = 4,
    max_work_units: int = 25_000_000,
    phase_binary_places: int | None = None,
    phase_decimal_places: int | None = None,
) -> ThreePowerBilateralInteriorQuotient:
    _validate_middle_windows_shape(binary_windows)
    _validate_middle_windows_shape(decimal_windows)
    for depth, bound in (
        (phase_binary_places, MAX_BINARY_WINDOW_PRECISION),
        (phase_decimal_places, MAX_DECIMAL_WINDOW_PRECISION),
    ):
        if depth is not None and (type(depth) is not int or not 1 <= depth <= bound):
            raise ValueError("phase depth exceeds source precision budget")
    bilateral = demand_three_power_bilateral_quotient(
        index,
        level,
        low_binary_places=low_binary_places,
        low_decimal_places=low_decimal_places,
        high_binary_places=high_binary_places,
        high_decimal_places=high_decimal_places,
        max_work_units=max_work_units,
    )
    from number_compiler.sequences.power_numbers.three_power_inward_phase_bank import (
        demand_inward_temporal_phase_bank,
    )

    def conditioned(
        border: RadixBilateralTripling,
        windows: tuple[tuple[int, int], ...],
        places: int | None,
    ) -> tuple[RefinedMiddleRelation, InwardTemporalPhaseBank | None]:
        if places is None:
            return refine_middle_source_windows(border, windows), None
        if type(places) is not int or places < border.low_places:
            raise ValueError(
                "phase depth must include the authenticated low radix border"
            )
        # Never overlap the leading radial block. A small source can have no
        # unknown gap at all; the requested phase is then clipped at the top.
        depth = min(places, border.source_digits - border.high_places)
        if depth < border.low_places:
            raise ValueError("no legal interior for the temporal bank")
        bank = demand_inward_temporal_phase_bank(border.base, border.level, depth)
        if bank.source_prefix % (border.base**border.low_places) != border.low_source:
            raise ArithmeticError("positional temporal bank contradicts the low border")
        combined = list(windows)
        if depth > border.low_places:
            combined.append((border.low_places, depth - border.low_places))
        # Merge overlapping exact windows before composing their actions.
        # This preserves source-bounded cost and does not convert an unknown
        # interval into a fabricated harmonic packet.
        intervals: list[tuple[int, int]] = []
        for start, width in sorted(combined):
            if type(start) is not int or type(width) is not int or width <= 0:
                raise ValueError("invalid phase-conditioned window")
            if intervals and start <= intervals[-1][1]:
                intervals[-1] = (intervals[-1][0], max(intervals[-1][1], start + width))
            else:
                intervals.append((start, start + width))
        merged = tuple((lo, hi - lo) for lo, hi in intervals)
        relation = refine_middle_source_windows(border, merged)
        # Exact cross-check of the composed action at the known phase boundary.
        if depth > border.low_places:
            bank_action = bank.transfer_between(border.low_places, depth)
            if bank_action[border.low_carry] != bank.exact_ingress_at(depth):
                raise ArithmeticError("position-bank carry transfer failed")
        return relation, bank

    binary_middle, binary_phase_bank = conditioned(
        bilateral.binary, binary_windows, phase_binary_places
    )
    decimal_middle, decimal_phase_bank = conditioned(
        bilateral.decimal, decimal_windows, phase_decimal_places
    )
    if binary_phase_bank is not None and decimal_phase_bank is not None:
        # Decimal 10**k carries an exact 2**k projection.  Both phase banks
        # are derived from one source level, so the overlap is a hard guard.
        overlap_bits = min(binary_phase_bank.depth, decimal_phase_bank.depth)
        binary_projection = binary_phase_bank.source_prefix % (1 << overlap_bits)
        decimal_projection = decimal_phase_bank.source_prefix % (1 << overlap_bits)
        if binary_projection != decimal_projection:
            raise ArithmeticError("positionwise binary/decimal CRT phase conflict")
        if 3 * binary_projection % (1 << overlap_bits) != (
            3 * decimal_projection % (1 << overlap_bits)
        ):
            raise ArithmeticError("positionwise tripling output CRT phase conflict")
    return ThreePowerBilateralInteriorQuotient(
        bilateral,
        binary_middle,
        decimal_middle,
        binary_phase_bank,
        decimal_phase_bank,
    )


def demand_three_power_inward_phase_quotient(
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
    max_work_units: int = 25_000_000,
) -> ThreePowerBilateralInteriorQuotient:
    """Join true inward temporal phases with both high/low radix borders.

    This selects carry transfer alternatives by the proved 2/5-adic source
    orbit at each *requested* position; unknown remainder gaps still retain
    all admissible alternatives, and the terminal prime bit remains UNKNOWN.
    """
    return demand_three_power_bilateral_interior(
        index,
        level,
        binary_windows=binary_windows,
        decimal_windows=decimal_windows,
        low_binary_places=low_binary_places,
        low_decimal_places=low_decimal_places,
        high_binary_places=high_binary_places,
        high_decimal_places=high_decimal_places,
        max_work_units=max_work_units,
        phase_binary_places=phase_binary_places,
        phase_decimal_places=phase_decimal_places,
    )


def demand_three_power_bilateral_quotient(
    index: int,
    level: int,
    *,
    low_binary_places: int = 12,
    low_decimal_places: int = 4,
    high_binary_places: int = 8,
    high_decimal_places: int = 4,
    max_work_units: int = 25_000_000,
) -> ThreePowerBilateralQuotient:
    for width in (
        low_binary_places,
        low_decimal_places,
        high_binary_places,
        high_decimal_places,
    ):
        if type(width) is not int or not 1 <= width <= 32:
            raise ValueError("bilateral border width must be in 1..32")
    if type(index) is not int or not 1 <= index <= 16:
        raise ValueError("invalid Fermat index for bounded bilateral demand")
    if type(level) is not int or not 1 <= level < (1 << index):
        raise ValueError("invalid Fermat source level")
    with GrowthArithmeticEvaluator(
        ResourceLedger(),
        max_work_units=max_work_units,
    ) as evaluator:
        k = 1 << level
        binary_port = demand_three_power_multiradix_port(
            index, level, 2, low_binary_places
        )
        decimal_port = demand_three_power_multiradix_port(
            index, level, 10, low_decimal_places
        )
        lower = RadialSturmianClock(HomogeneousGrowthScale(k, 0))
        upper = RadialSturmianClock(HomogeneousGrowthScale(k + 1, 0))
        b_source = lower.leading_radix(evaluator, 2, high_binary_places)
        b_target = upper.leading_radix(evaluator, 2, high_binary_places)
        d_source = lower.leading_radix(evaluator, 10, high_decimal_places)
        d_target = upper.leading_radix(evaluator, 10, high_decimal_places)
    return ThreePowerBilateralQuotient(
        index,
        level,
        _build_radix_border(
            index,
            level,
            binary_port,
            high_binary_places,
            b_source.value,
            b_source.word_length,
            b_target.value,
            b_target.word_length,
        ),
        _build_radix_border(
            index,
            level,
            decimal_port,
            high_decimal_places,
            d_source.value,
            d_source.word_length,
            d_target.value,
            d_target.word_length,
        ),
    )


__all__ = [
    "CertifiedMiddleWindow",
    "RadixBilateralTripling",
    "RefinedMiddleRelation",
    "ThreePowerBilateralInteriorQuotient",
    "ThreePowerBilateralQuotient",
    "carry_h5",
    "demand_three_power_bilateral_interior",
    "demand_three_power_bilateral_quotient",
    "demand_three_power_inward_phase_quotient",
    "digit_transfer",
    "refine_middle_source_windows",
    "unknown_middle_transfer_set",
]
