"""Exact reverse/add innovation moments and demand-driven carry/borrow ports.

This module distinguishes three kinds of authority:

* A ``SkewMoment`` is a *formal* upper-triangular temporal matrix.  Its
  arithmetic may be squared in logarithmic time, but that is not a proof the
  same innovations will occur on an unvisited reverse/add successor.
* A ``SourceBoundMoment`` checks the moment against supplied numerical
  endpoints. Matching endpoint seams allow observation composition, but the
  value does not authenticate a physical path or authorize execution.
* ``ReverseInnovationBank`` is a diagnostic observer, not a transition oracle.
  In particular, agreement of carry, borrow, Walsh, F5, and LT/GT masks is
  deliberately insufficient for successor admission.

No successor is computed by looking up an observed future tape.  The production
Q19 scheduler remains the authority for a completed endpoint.
"""

from __future__ import annotations

from dataclasses import dataclass, fields, is_dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    apply_carry_fn,
    compose_carry_fn,
    value_carry_fn,
)
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.arithmetic.fields.skew_moments import SkewMoment
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys

if TYPE_CHECKING:
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def _require_int(value: int, description: str, minimum: int = 0) -> int:
    if type(value) is not int or value < minimum:
        raise ValueError(f"{description} must be an integer >= {minimum}")
    return value


def _reverse_decimal(value: int) -> int:
    _require_int(value, "reverse source")
    result = 0
    while value:
        value, digit = divmod(value, 10)
        result = result * 10 + digit
    return result


def _decimal_borrow_tape(minuend: int, subtrahend: int, width: int) -> tuple[int, int]:
    """Fold a fixed-width LSD-first decimal subtraction borrow tape."""
    mask = debt = 0
    for index in range(width):
        minuend, a_digit = divmod(minuend, 10)
        subtrahend, b_digit = divmod(subtrahend, 10)
        debt = int(a_digit < b_digit + debt)
        mask |= debt << index
    return mask, debt


def _integer_payload_bits(value: object) -> int:
    """Count exact integer payload bits in a finite record, without recursion."""
    pending = [value]
    total = 0
    while pending:
        current = pending.pop()
        if type(current) is int:
            total += current.bit_length()
        elif isinstance(current, tuple):
            pending.extend(current)
        elif is_dataclass(current):
            pending.extend(getattr(current, item.name) for item in fields(current))
    return total


def _decimal_digit_budget_bit_bound(max_digits: int) -> int:
    """Bit bound above which an integer surely exceeds ``max_digits``.

    Since log2(10) < 1661/500, this conservative integer bound rejects huge
    inputs before the repeated-division decimal decoder runs. At most a tiny
    boundary band reaches the exact post-decode digit check.
    """
    return (1661 * max_digits + 499) // 500


@dataclass(frozen=True, slots=True)
class SourceBoundMoment:
    """Endpoint-consistent reverse/add interval observation.

    This value checks the arithmetic relation between supplied endpoints and
    its exact skew moment. It does not authenticate that a physical path joins
    those endpoints and must never be used as an execution-authority token.
    """

    source: int
    target: int
    moment: SkewMoment
    source_width: int
    target_width: int

    def __post_init__(self) -> None:
        _require_int(self.source, "action source")
        _require_int(self.target, "action target")
        if type(self.moment) is not SkewMoment or self.moment.modulus is not None:
            raise ValueError("physical actions require exact, non-modular moments")
        _require_int(self.source_width, "source width", 1)
        _require_int(self.target_width, "target width", 1)
        if self.target_width - self.source_width < 0:
            raise ValueError("reverse/add width cannot shrink")
        if self.target_width - self.source_width > self.moment.duration:
            raise ValueError("reverse/add width growth exceeds time span")
        if self.moment.apply(self.source, _reverse_decimal(self.source)) != (
            self.target,
            _reverse_decimal(self.target),
        ):
            raise ValueError("moment and endpoint observations do not agree")

    @classmethod
    def from_endpoints(
        cls, source: int, target: int, *, steps: int
    ) -> SourceBoundMoment:
        """Describe supplied endpoints, not certify that their path exists.

        A caller may pair this observation with independently issued endpoint
        evidence. In isolation, this constructor does not provide transition
        authority.
        """
        _require_int(source, "source")
        _require_int(target, "target")
        _require_int(steps, "steps")
        width_source = len(digits_lsd(source, 10))
        width_target = len(digits_lsd(target, 10))
        u = _reverse_decimal(target) - _reverse_decimal(source)
        v = target - source - steps * _reverse_decimal(source)
        return cls(source, target, SkewMoment(steps, u, v), width_source, width_target)

    @classmethod
    def primitive(cls, source: int) -> SourceBoundMoment:
        """Derive and check the complete primitive from the original source."""
        target = source + _reverse_decimal(source)
        return cls.from_endpoints(source, target, steps=1)

    def then(self, after: SourceBoundMoment) -> SourceBoundMoment:
        """Compose two endpoint-consistent observations with matching seams."""
        if type(after) is not SourceBoundMoment or self.target != after.source:
            raise ValueError("source/target temporal seam mismatch")
        if self.target_width != after.source_width:
            raise ValueError("width temporal seam mismatch")
        return SourceBoundMoment(
            self.source,
            after.target,
            self.moment.then(after.moment),
            self.source_width,
            after.target_width,
        )

    def square_if_adjacent(self, after: SourceBoundMoment) -> SourceBoundMoment:
        """Join an adjacent observation of equal duration; no repeat is assumed."""
        if self.moment.duration != after.moment.duration:
            raise ValueError("squared action requires equal temporal spans")
        return self.then(after)

    @property
    def growth(self) -> int:
        return self.target_width - self.source_width


@dataclass(frozen=True, slots=True)
class ModulusCarryBorrow:
    """Independent modular carry, innovation borrow, and XOR observer."""

    modulus: int
    carry: int
    innovation_borrow: int | None
    xor: int | None

    def __post_init__(self) -> None:
        _require_int(self.modulus, "observer modulus", 2)
        if self.carry not in (0, 1):
            raise ValueError("carry must be Boolean")
        if self.innovation_borrow is None:
            if self.xor is not None:
                raise ValueError("XOR requires a certified previous innovation")
        elif self.innovation_borrow not in (0, 1) or self.xor != (
            self.carry ^ self.innovation_borrow
        ):
            raise ValueError("borrow/XOR observer is inconsistent")


def _walsh64(mask: int) -> tuple[int, ...]:
    """Walsh-Hadamard transform of 64 Boolean low-coordinate mask bits."""
    values = [1 if not (mask >> index) & 1 else -1 for index in range(64)]
    stride = 1
    while stride < 64:
        for start in range(0, 64, 2 * stride):
            for index in range(start, start + stride):
                a, b = values[index], values[index + stride]
                values[index], values[index + stride] = a + b, a - b
        stride *= 2
    return tuple(values)


@dataclass(frozen=True, slots=True)
class ReverseInnovationBank:
    """One coupled, sign-preserving pair/carry/innovation observation.

    Every position is LSD-first, and every LT/EQ/GT domain classifies the
    **symmetric sum** ``s[i] = d[i] + d[w-1-i]`` in 0..18, NOT a comparison
    of the individual digits.  Five disjoint domains preserve the high/low
    distinction used by the Q19/F5 successor grammar.  The carry tape is the
    forward physical accumulator carry ``c[i+1]`` at bit ``i``.

    ``borrow_mask`` is the magnitude-oriented subtraction tape of
    ``abs(rev(X)-rev(previous))``; ``innovation_sign`` records its orientation.
    ``raw_borrow_mask`` is the borrow tape of the un-swapped subtraction
    ``rev(X)-rev(previous)``.  Neither may silently replace the other.

    The reflected XOR and zero/nine masks are **conditional successor ports**.
    ``next_eq_nongrowth_mask`` only applies when the current step does not
    grow.  Its bits describe next-step pair coefficients, not current EQ.
    """

    width: int
    carry_mask: int
    lt_mask: int
    eq_mask: int
    gt_mask: int
    first_non9_from_lsd: int | None
    carry_transfer: CarryFn
    borrow_mask: int | None
    xor_mask: int | None
    modular: tuple[ModulusCarryBorrow, ...]
    xor_walsh64: tuple[int, ...] | None
    f5_xor: int | None
    lt_low_mask: int
    lt_high_mask: int
    gt_low_mask: int
    gt_high_mask: int
    reflected_carry_xor_mask: int
    next_eq_nongrowth_mask: int | None
    successor_zero_mask: int
    successor_nine_mask: int
    borrow_identity_gate_mask: int | None
    innovation_sign: int | None
    raw_borrow_mask: int | None
    raw_xor_mask: int | None
    innovation_width: int | None
    future_raw_borrow_mask: int
    future_borrow_mask: int
    future_innovation_sign: int
    future_xor_mask: int
    future_raw_xor_mask: int
    future_xor_walsh64: tuple[int, ...]
    future_f5_xor: int

    @classmethod
    def observe(
        cls,
        source: int,
        *,
        previous: int | None = None,
        moduli: tuple[int, ...] = (2, 3, 5, 7, 9, 11, 27, 49, 99),
        max_digits: int = 8192,
        ledger: ResourceLedger | None = None,
    ) -> ReverseInnovationBank:
        _require_int(source, "bank source")
        _require_int(max_digits, "bank digit budget", 1)
        if previous is not None:
            _require_int(previous, "previous temporal source")
        if len(set(moduli)) != len(moduli) or any(
            type(mod) is not int or mod < 2 for mod in moduli
        ):
            raise ValueError("moduli must be distinct integers >=2")
        if ledger is not None and type(ledger) is not ResourceLedger:
            raise TypeError("temporal stencil ledger has the wrong owner")
        bit_limit = _decimal_digit_budget_bit_bound(max_digits)
        if source.bit_length() > bit_limit:
            raise ValueError("carry/borrow bank exceeds the digit budget")
        if previous is not None and previous.bit_length() > bit_limit:
            raise ValueError("previous innovation source exceeds the digit budget")
        if ledger is not None:
            ledger.bump(
                _reverse_add_keys.REVERSE_Q19_TEMPORAL_STENCIL_OPERAND_BITS,
                source.bit_length()
                + (0 if previous is None else previous.bit_length()),
            )
        digits = digits_lsd(source, 10)
        w = len(digits)
        if w > max_digits:
            raise ValueError("carry/borrow bank exceeds the digit budget")
        digit_work = 0
        carry_mask = lt_low = lt_high = eq = gt_low = gt_high = 0
        first_non9: int | None = None
        carry = 0
        transfer = CarryFn.ID
        # Keep incoming as well as outgoing carries for the two reflected
        # ports.  This is a linear finite audit only; the symbolic publisher
        # retains the underlying Q19 carry-transfer SLP.
        carries = [0]
        pair_sums: list[int] = []
        zero = nine = 0
        for index, digit in enumerate(digits):
            digit_work += 1
            pair = digit + digits[w - 1 - index]
            pair_sums.append(pair)
            if first_non9 is None and pair != 9:
                first_non9 = index
            bit = 1 << index
            if pair <= 4:
                lt_low |= bit
            elif pair <= 8:
                lt_high |= bit
            elif pair == 9:
                eq |= bit
            elif pair <= 14:
                gt_low |= bit
            else:
                gt_high |= bit
            incoming = carry
            effect = value_carry_fn(pair, 10)
            transfer = compose_carry_fn(effect, transfer)
            carry = apply_carry_fn(effect, carry)
            carries.append(carry)
            carry_mask |= carry * bit
            emitted = pair + incoming - 10 * carry
            if emitted == 0:
                zero |= bit
            elif emitted == 9:
                nine |= bit
        growth = carries[-1]
        reflected_xor = eq_birth = identity_gates = 0
        for index, pair in enumerate(pair_sums):
            digit_work += 1
            bit = 1 << index
            # These ingresses are distinct: do not replace the symmetric
            # two-port relation by a single guessed backwards carry.
            if carries[index] ^ carries[w - 1 - index]:
                reflected_xor |= bit
                if pair % 5 == 4:
                    eq_birth |= bit
            rho, eta = carries[w - index], carries[w - 1 - index]
            if (digits[index] == 0 and rho == eta == 0) or (
                digits[index] == 9 and rho == eta == 1
            ):
                identity_gates |= bit

        # Produce the innovation borrow of the *next* reversal difference
        # directly from this source's carry/paired-digit stencil.  This is
        # NOT computed from a pre-solved future integer.  On nongrowth the
        # 0/9 identity-reset law predicts every bit; growth needs the shifted
        # reversal alignment (the new high 1 becomes the new low digit).
        next_digits = [
            pair + carries[index] - 10 * carries[index + 1]
            for index, pair in enumerate(pair_sums)
        ]
        digit_work += w
        if growth:
            next_digits.append(1)
        rev_next = list(reversed(next_digits))
        rev_current = list(reversed(digits)) + [0] * growth
        future_raw_borrow = 0
        debt = 0
        is_zero_difference = True
        for index, (a_digit, b_digit) in enumerate(zip(rev_next, rev_current)):
            digit_work += 1
            new_debt = int(a_digit < b_digit + debt)
            difference_digit = a_digit - b_digit - debt + 10 * new_debt
            is_zero_difference &= difference_digit == 0
            debt = new_debt
            future_raw_borrow |= debt << index
        future_sign = -1 if debt else 0 if is_zero_difference else 1
        # Subtract in the oriented direction for the magnitude bank.
        high_digits, low_digits = (
            (rev_next, rev_current) if future_sign >= 0 else (rev_current, rev_next)
        )
        future_borrow = 0
        debt = 0
        for index, (a_digit, b_digit) in enumerate(zip(high_digits, low_digits)):
            digit_work += 1
            debt = int(a_digit < b_digit + debt)
            future_borrow |= debt << index
        if debt:
            raise AssertionError("future innovation magnitude had terminal borrow")
        if not growth:
            # Unlike reading the next number, this independently certifies
            # the proven reflected carry/zero-nine XOR borrow stencil.
            predicted_borrow = 0
            incoming_borrow = 0
            for index in range(w):
                rho = carries[w - index]
                identity = bool(identity_gates & (1 << index))
                incoming_borrow = incoming_borrow if identity else rho
                predicted_borrow |= incoming_borrow << index
            if predicted_borrow != future_raw_borrow:
                raise AssertionError("nongrowth XOR borrow gate lost a carry port")
        future_xor = carry_mask ^ future_borrow
        future_raw_xor = carry_mask ^ future_raw_borrow

        reverse_current = _reverse_decimal(source)
        reverse_prev = None if previous is None else _reverse_decimal(previous)
        sign: int | None = None
        borrow_mask: int | None = None
        raw_borrow_mask: int | None = None
        xor_mask: int | None = None
        raw_xor_mask: int | None = None
        innovation_width: int | None = None
        if reverse_prev is not None:
            innovation_width = max(w, len(digits_lsd(reverse_prev, 10)))
            sign = (reverse_current > reverse_prev) - (reverse_current < reverse_prev)
            high, low = (
                max(reverse_current, reverse_prev),
                min(reverse_current, reverse_prev),
            )
            raw_high, raw_low = reverse_current, reverse_prev
            borrow_mask, oriented_debt = _decimal_borrow_tape(
                high, low, innovation_width
            )
            raw_borrow_mask, raw_debt = _decimal_borrow_tape(
                raw_high, raw_low, innovation_width
            )
            digit_work += 2 * innovation_width
            if raw_debt != int(sign < 0) or oriented_debt:
                raise AssertionError("signed innovation borrow exit is inconsistent")
            xor_mask = carry_mask ^ borrow_mask
            raw_xor_mask = carry_mask ^ raw_borrow_mask

        modular = []
        for modulus in moduli:
            digit_work += 1
            kappa = int(source % modulus + reverse_current % modulus >= modulus)
            if reverse_prev is None:
                lam = None
            else:
                high, low = (
                    max(reverse_current, reverse_prev),
                    min(reverse_current, reverse_prev),
                )
                lam = int(high % modulus < low % modulus)
            modular.append(
                ModulusCarryBorrow(
                    modulus, kappa, lam, None if lam is None else kappa ^ lam
                )
            )
        result = cls(
            w,
            carry_mask,
            lt_low | lt_high,
            eq,
            gt_low | gt_high,
            first_non9,
            transfer,
            borrow_mask,
            xor_mask,
            tuple(modular),
            None if xor_mask is None else _walsh64(xor_mask),
            None
            if xor_mask is None
            else sum(
                ((xor_mask >> i) & 1) * pow(2, i, 5)
                for i in range(max(w, innovation_width or w))
            )
            % 5,
            lt_low,
            lt_high,
            gt_low,
            gt_high,
            reflected_xor,
            eq_birth if not growth else None,
            zero,
            nine,
            identity_gates if not growth else None,
            sign,
            raw_borrow_mask,
            raw_xor_mask,
            innovation_width,
            future_raw_borrow,
            future_borrow,
            future_sign,
            future_xor,
            future_raw_xor,
            _walsh64(future_xor),
            sum(((future_xor >> i) & 1) * pow(2, i, 5) for i in range(w + growth)) % 5,
        )
        if ledger is not None:
            ledger.bump(
                _reverse_add_keys.REVERSE_Q19_TEMPORAL_STENCIL_DIGIT_OPERATIONS,
                digit_work,
            )
            ledger.bump(
                _reverse_add_keys.REVERSE_Q19_TEMPORAL_STENCIL_OUTPUT_FIELDS,
                len(fields(result)),
            )
            ledger.bump(
                _reverse_add_keys.REVERSE_Q19_TEMPORAL_STENCIL_OUTPUT_BITS,
                _integer_payload_bits(result),
            )
        return result

    @property
    def growth(self) -> int:
        """Source-width growth bit (terminal physical addition carry)."""
        return (self.carry_mask >> (self.width - 1)) & 1

    @property
    def five_band_masks(self) -> tuple[int, int, int, int, int]:
        """Full-width (LT-low, LT-high, EQ, GT-low, GT-high) masks."""
        return (
            self.lt_low_mask,
            self.lt_high_mask,
            self.eq_mask,
            self.gt_low_mask,
            self.gt_high_mask,
        )

    @property
    def low_high_comparisons(self) -> tuple[int, int, int, int, int, int]:
        """LT/EQ/GT *pair* domains separately on the two spatial halves.

        Unlike the obsolete individual-digit comparison, both mirrored halves
        classify the same pair coefficients, so each bit is reflected rather
        than swapping LT with GT.  Use ``five_band_masks`` for fine domains.
        """
        low_bits = (1 << ((self.width + 1) // 2)) - 1
        high_bits = ((1 << self.width) - 1) ^ low_bits
        return (
            self.lt_mask & low_bits,
            self.eq_mask & low_bits,
            self.gt_mask & low_bits,
            self.lt_mask & high_bits,
            self.eq_mask & high_bits,
            self.gt_mask & high_bits,
        )

    @property
    def and_or_masks(self) -> tuple[int, int] | None:
        if self.borrow_mask is None:
            return None
        return self.carry_mask & self.borrow_mask, self.carry_mask | self.borrow_mask

    def masks_partition(self) -> bool:
        full = (1 << self.width) - 1
        bands = self.five_band_masks
        return (
            (self.lt_mask | self.eq_mask | self.gt_mask) == full
            and self.lt_mask == self.lt_low_mask | self.lt_high_mask
            and self.gt_mask == self.gt_low_mask | self.gt_high_mask
            and sum(mask.bit_count() for mask in bands) == self.width
            and (
                self.xor_mask is None
                or (
                    self.borrow_mask is not None
                    and self.xor_mask == self.carry_mask ^ self.borrow_mask
                )
            )
            and (
                self.raw_xor_mask is None
                or (
                    self.raw_borrow_mask is not None
                    and self.raw_xor_mask == self.carry_mask ^ self.raw_borrow_mask
                )
            )
        )


def source_bound_modular_moments(
    term: ReverseAddPoweredTerm,
    *,
    modulus: int,
) -> SkewMoment:
    """Project U,V directly from the Q19 output's carry-ported SLP.

    The source image publisher is authoritative.  Unlike exact numeric
    materialization, this demand does not stream expanded output digits or
    construct the resulting integer.  The two-input carry fold also computes
    the reversed normalized output, including the optional new high '1'.
    This is not an orbit-period certificate and cannot authorize time skips.
    """
    from number_compiler.sequences.reverse_add.pair_numeric_ports import (
        project_q19_numeric,
    )
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
    from number_compiler.sequences.reverse_add.source_images import ReverseImagePayload

    if type(term) is not ReverseAddPoweredTerm or term.base != 10:
        raise TypeError("modular moments require a decimal powered term")
    _require_int(modulus, "moment modulus", 2)
    if (term.seed, term.generation, term.base) != term._binding:
        raise ValueError("reverse/add temporal moment source was rebound")
    source = term.seed % modulus
    source_reverse = _reverse_decimal(term.seed) % modulus
    if not term.generation:
        return SkewMoment(0, 0, 0, modulus)
    if term.seed == 0:
        # Zero is a proved fixed point: 0 + reverse10(0) = 0.
        # The scheduler's positive-decimal Q19 image need not exist here.
        return SkewMoment(term.generation, 0, 0, modulus)
    workspace = term._source_workspace()
    workspace.width()
    if workspace._image is None:
        raise AssertionError("completed Q19 source image was not published")
    core = workspace.scheduler._source_image_core()
    view = core.view(workspace._image)
    payload = view.payload
    if type(payload) is not ReverseImagePayload or payload.pair_output is None:
        raise ValueError("source image has no completed Q19 occurrence")
    if payload.pair_output.temporal_steps != term.generation:
        raise ValueError("Q19 temporal duration disagrees with source request")
    owner = workspace.adapter._q19_owner
    if owner is None or workspace.adapter._q19_source is not workspace.actions.source(
        workspace.source
    ):
        raise ValueError("Q19 occurrence is missing its authenticated source owner")
    endpoint = project_q19_numeric(owner, payload.pair_output, modulus=modulus)
    u = (endpoint.reverse_target_mod - source_reverse) % modulus
    v = (endpoint.target_mod - source - term.generation * source_reverse) % modulus
    return SkewMoment(term.generation, u, v, modulus)


def source_bound_temporal_matrix(
    term: ReverseAddPoweredTerm, *, max_bits: int = 16384
) -> SourceBoundMoment:
    """Project the authenticated Q19 endpoint into a *numerical* skew matrix.

    Endpoint production stays exclusively with ``ReverseAddPoweredTerm``.  A
    bit budget is checked *before* requesting output digits, and this function
    does not independently iterate any physical reverse/add successors.
    """
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

    if type(term) is not ReverseAddPoweredTerm or term.base != 10:
        raise TypeError("reverse/add matrix requires a decimal powered term")
    _require_int(max_bits, "matrix exact-bit budget", 1)
    # Check the source-bound maximum width before constructing its scheduler.
    # This may conservatively refuse some admissible outputs, but does not
    # allocate a large completed image to discover a known-inadequate budget.
    if (3322 * term.maximum_width + 999) // 1000 > max_bits:
        raise ValueError("reverse/add matrix exceeds the conservative bit cap")
    target = term.materialize(max_bits=max_bits)
    return SourceBoundMoment.from_endpoints(term.seed, target, steps=term.generation)


__all__ = [
    "ModulusCarryBorrow",
    "ReverseInnovationBank",
    "SkewMoment",
    "SourceBoundMoment",
    "source_bound_modular_moments",
    "source_bound_temporal_matrix",
]
