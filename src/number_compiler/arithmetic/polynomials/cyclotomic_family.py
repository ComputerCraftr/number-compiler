"""Family-specific observers built on the shared cyclotomic digit algebra."""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from typing import TypedDict

from number_compiler.arithmetic.carry.carry_normalization import NormalizationDefect
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.arithmetic.polynomials.cyclotomic_factor import (
    cyclotomic_factors_mod_prime,
)
from number_compiler.arithmetic.polynomials.digit_cyclotomic import CyclotomicDigitBlock
from number_compiler.arithmetic.polynomials.polynomial import polynomial_affine


class _ComponentOptions(TypedDict):
    order: int
    modulus: int
    power: int
    factor: Sequence[int] | None


@dataclass(frozen=True, slots=True)
class NormalizationCyclotomicComponent:
    """One cyclotomic component of the exact boundary-aware carry identity."""

    base: int
    length: int
    difference: CyclotomicDigitBlock
    carry: CyclotomicDigitBlock
    boundary: CyclotomicDigitBlock
    factor_times_carry: CyclotomicDigitBlock
    recovered_carry: CyclotomicDigitBlock | None

    @property
    def identity_holds(self) -> bool:
        return self.difference.equivalent(self.factor_times_carry.add(self.boundary))

    @property
    def normalization_factor_is_unit(self) -> bool:
        return self.carry.linear_factor_is_unit(self.base)

    @property
    def carry_recovered_exactly(self) -> bool:
        return self.recovered_carry is not None and self.recovered_carry.equivalent(
            self.carry
        )


def normalization_component(
    defect: NormalizationDefect,
    *,
    order: int,
    modulus: int,
    power: int = 1,
    factor: Sequence[int] | None = None,
) -> NormalizationCyclotomicComponent:
    """Project a :class:`NormalizationDefect` into one source-digit quotient."""
    length = int(defect.length)
    kwargs: _ComponentOptions = {
        "order": int(order),
        "modulus": int(modulus),
        "power": int(power),
        "factor": factor,
    }
    difference = CyclotomicDigitBlock.from_coefficients(
        defect.difference_lsf,
        length=length + 1,
        **kwargs,
    )
    carry = CyclotomicDigitBlock.from_coefficients(
        defect.carry_quotient_lsf,
        length=length,
        **kwargs,
    )
    boundary = CyclotomicDigitBlock.from_coefficients(
        defect.boundary_term_lsf,
        length=length + 1,
        **kwargs,
    )
    factor_times_carry = carry.apply_linear_factor(defect.base).with_length(length + 1)
    recovered = None
    if difference.linear_factor_is_unit(defect.base):
        recovered = difference.subtract(boundary).divide_linear_factor(
            defect.base,
            result_length=length,
        )
    result = NormalizationCyclotomicComponent(
        int(defect.base),
        length,
        difference,
        carry,
        boundary,
        factor_times_carry,
        recovered,
    )
    if not result.identity_holds or (
        recovered is not None and not result.carry_recovered_exactly
    ):
        raise AssertionError(result)
    return result


@dataclass(frozen=True, slots=True)
class FamilyCyclotomicStep:
    """Common exact digit/raw/normalization view for one family transition."""

    family: str
    source_value: int
    target_value: int
    source: CyclotomicDigitBlock
    raw: CyclotomicDigitBlock
    normalized: CyclotomicDigitBlock
    normalization: NormalizationCyclotomicComponent
    algebraic_raw: CyclotomicDigitBlock
    accelerated: CyclotomicDigitBlock | None = None
    valuation: int = 0

    @property
    def raw_operator_exact(self) -> bool:
        return self.raw.equivalent(self.algebraic_raw)

    @property
    def exact(self) -> bool:
        return self.raw_operator_exact and self.normalization.identity_holds


def _complete_nonnegative_normalization(
    coefficients: Sequence[int], base: int
) -> tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...], NormalizationDefect]:
    """Normalize a nonnegative raw field and drain the terminal carry to zero."""
    from number_compiler.arithmetic.carry.carry_normalization import (
        linear_normalization_fields,
        normalization_defect,
    )

    coeffs = list(map(int, coefficients))
    if any(value < 0 for value in coeffs):
        raise ValueError(
            "complete linear normalization expects nonnegative coefficients"
        )
    while True:
        digits, carries = linear_normalization_fields(tuple(coeffs), base=int(base))
        if carries[-1] == 0:
            break
        coeffs.append(0)
    defect = normalization_defect(tuple(coeffs), digits, carries, base=int(base))
    return tuple(coeffs), tuple(digits), tuple(carries), defect


def reverse_add_cyclotomic_step(
    value: int,
    *,
    base: int,
    order: int,
    modulus: int,
    power: int = 1,
    factor: Sequence[int] | None = None,
) -> FamilyCyclotomicStep:
    """Exact reverse-add digit/pair/normalization component for one step."""
    value, base = int(value), int(base)
    digits = digits_lsd(value, base)
    kwargs: _ComponentOptions = {
        "order": int(order),
        "modulus": int(modulus),
        "power": int(power),
        "factor": factor,
    }
    source = CyclotomicDigitBlock.from_coefficients(
        digits, length=len(digits), **kwargs
    )
    pair = tuple(digits[i] + digits[-1 - i] for i in range(len(digits)))
    raw = CyclotomicDigitBlock.from_coefficients(pair, length=len(pair), **kwargs)
    algebraic = source.symmetric_pair()
    padded_raw, out_digits, _carries, defect = _complete_nonnegative_normalization(
        pair, base
    )
    normalized = CyclotomicDigitBlock.from_coefficients(
        out_digits,
        length=len(out_digits),
        **kwargs,
    )
    target = sum(int(digit) * base**index for index, digit in enumerate(out_digits))
    component = normalization_component(defect, **kwargs)
    raw_padded = CyclotomicDigitBlock.from_coefficients(
        padded_raw,
        length=len(padded_raw),
        **kwargs,
    )
    if not raw_padded.equivalent(raw):
        raise AssertionError((raw, raw_padded))
    result = FamilyCyclotomicStep(
        "reverse-add",
        value,
        target,
        source,
        raw,
        normalized,
        component,
        algebraic,
    )
    if not result.exact:
        raise AssertionError(result)
    return result


def collatz_cyclotomic_step(
    value: int,
    *,
    base: int,
    order: int,
    modulus: int,
    power: int = 1,
    factor: Sequence[int] | None = None,
) -> FamilyCyclotomicStep:
    """Exact odd Collatz ``3n+1`` component; binary also exposes acceleration."""
    value, base = int(value), int(base)
    if value <= 0 or not (value & 1):
        raise ValueError(value)
    digits = digits_lsd(value, base)
    multiplier_digits = digits_lsd(3, base)
    raw_coefficients = polynomial_affine(digits, multiplier_digits, (1,))
    kwargs: _ComponentOptions = {
        "order": int(order),
        "modulus": int(modulus),
        "power": int(power),
        "factor": factor,
    }
    source = CyclotomicDigitBlock.from_coefficients(
        digits, length=len(digits), **kwargs
    )
    raw = CyclotomicDigitBlock.from_coefficients(
        raw_coefficients, length=len(raw_coefficients), **kwargs
    )
    algebraic = source.radix_affine(multiplier=3, addend=1, base=base)
    padded_raw, out_digits, _carries, defect = _complete_nonnegative_normalization(
        raw_coefficients, base
    )
    normalized = CyclotomicDigitBlock.from_coefficients(
        out_digits, length=len(out_digits), **kwargs
    )
    raw_padded = CyclotomicDigitBlock.from_coefficients(
        padded_raw, length=len(padded_raw), **kwargs
    )
    if not raw_padded.equivalent(raw):
        raise AssertionError((raw, raw_padded))
    full = 3 * value + 1
    if sum(d * base**i for i, d in enumerate(out_digits)) != full:
        raise AssertionError((value, base, out_digits, full))
    valuation = v2_positive(full)
    target = full >> valuation
    accelerated = None
    if base == 2:
        accelerated = normalized.shift_positions(
            -valuation,
            result_length=max(1, len(out_digits) - valuation),
        )
        target_component = CyclotomicDigitBlock.from_coefficients(
            digits_lsd(target, 2),
            length=len(digits_lsd(target, 2)),
            **kwargs,
        )
        if not accelerated.equivalent(target_component):
            raise AssertionError((value, valuation, accelerated, target_component))
    component = normalization_component(defect, **kwargs)
    result = FamilyCyclotomicStep(
        "collatz",
        value,
        target,
        source,
        raw,
        normalized,
        component,
        algebraic,
        accelerated,
        valuation,
    )
    if not result.exact:
        raise AssertionError(result)
    return result


@dataclass(frozen=True, slots=True)
class CollatzPiecewiseCyclotomicStep:
    """Exact self-selected physical Collatz successor in one cyclotomic module.

    Even sources use the normalized spatial shift ``z^-1`` directly.  Odd
    sources use the shared affine ``(1+z)x+1`` raw map and the same canonical
    normalization theorem as every other radix operation.  ``component_closed``
    says only whether this particular source/target pair is represented
    exactly; global quotient closure must still be proved separately.
    """

    source_value: int
    target_value: int
    branch: str
    source: CyclotomicDigitBlock
    target: CyclotomicDigitBlock
    algebraic_target: CyclotomicDigitBlock
    odd_detail: FamilyCyclotomicStep | None = None

    @property
    def exact(self) -> bool:
        return self.target.equivalent(self.algebraic_target) and (
            self.odd_detail is None or self.odd_detail.exact
        )


def collatz_piecewise_cyclotomic_step(
    value: int,
    *,
    order: int,
    modulus: int,
    power: int = 1,
    factor: Sequence[int] | None = None,
) -> CollatzPiecewiseCyclotomicStep:
    """Apply the ordinary even/odd Collatz successor with no supplied branch."""
    value = int(value)
    if value <= 0:
        raise ValueError(value)
    kwargs: _ComponentOptions = {
        "order": int(order),
        "modulus": int(modulus),
        "power": int(power),
        "factor": factor,
    }
    source_digits = digits_lsd(value, 2)
    source = CyclotomicDigitBlock.from_coefficients(
        source_digits, length=len(source_digits), **kwargs
    )
    if value & 1:
        detail = collatz_cyclotomic_step(value, base=2, **kwargs)
        target_value = 3 * value + 1
        target = detail.normalized
        # Normalization is semantically part of the odd branch; the exact
        # target component comes from the shared normalization identity, not an
        # externally supplied parity/valuation symbol.
        algebraic_target = detail.normalized
        result = CollatzPiecewiseCyclotomicStep(
            value,
            target_value,
            "multiply_3_add_1",
            source,
            target,
            algebraic_target,
            detail,
        )
    else:
        target_value = value >> 1
        target_digits = digits_lsd(target_value, 2)
        target = CyclotomicDigitBlock.from_coefficients(
            target_digits, length=len(target_digits), **kwargs
        )
        algebraic_target = source.shift_positions(-1, result_length=len(target_digits))
        result = CollatzPiecewiseCyclotomicStep(
            value,
            target_value,
            "divide_2",
            source,
            target,
            algebraic_target,
            None,
        )
    if not result.exact:
        raise AssertionError(result)
    return result


def _signed_binary_digits(value: int, width: int, sign: int) -> tuple[int, ...]:
    value, width, sign = int(value), int(width), int(sign)
    scale = 1 << width
    if sign == -1 and value == scale:
        return (-1,) + (0,) * (width - 1)
    return digits_lsd(value, 2, width)


def mersenne_cyclotomic_step(
    value: int,
    exponent: int,
    *,
    coefficient_modulus: int,
    factor_index: int | None = None,
) -> FamilyCyclotomicStep:
    """Project one trace-square in ``Phi_p`` or one finite-field factor.

    This arithmetic operation has no initial seed, recurrence horizon or
    primality acceptance criterion.
    """
    from number_compiler.arithmetic.carry.carry_normalization import (
        end_around_normalization_defect,
        normalization_digits_lsf,
    )
    from number_compiler.arithmetic.polynomials.digit_convolution import (
        cyclic_binary_square_add_projection,
    )

    value, p, q = int(value), int(exponent), int(coefficient_modulus)
    modulus = (1 << p) - 1
    if p < 2 or not 0 <= value < modulus:
        raise ValueError((value, p))
    factor = None
    if factor_index is not None:
        factors = cyclotomic_factors_mod_prime(p, q)
        factor = factors[int(factor_index)]
    kwargs: _ComponentOptions = {"order": p, "modulus": q, "power": 1, "factor": factor}
    source_digits = digits_lsd(value, 2, p)
    source = CyclotomicDigitBlock.from_coefficients(source_digits, length=p, **kwargs)
    projection = cyclic_binary_square_add_projection(value, p, -2)
    raw = CyclotomicDigitBlock.from_coefficients(projection.field, length=p, **kwargs)
    algebraic = source.square().add_constant(-2)
    target_digits = normalization_digits_lsf(projection.normalization)
    normalized = CyclotomicDigitBlock.from_coefficients(
        target_digits, length=p, **kwargs
    )
    defect = end_around_normalization_defect(projection.field, projection.normalization)
    component = normalization_component(defect, **kwargs)
    result = FamilyCyclotomicStep(
        "mersenne",
        value,
        projection.residue,
        source,
        raw,
        normalized,
        component,
        algebraic,
    )
    if not result.exact:
        raise AssertionError(result)
    return result


def fermat_cyclotomic_step(
    value: int,
    index: int,
    *,
    coefficient_modulus: int,
    factor_index: int | None = None,
    local_power: int | None = None,
) -> FamilyCyclotomicStep:
    """One squaring component in the negacyclic Fermat digit ring.

    For odd coefficient primes, ``factor_index`` selects an irreducible factor
    of ``Phi_(2N)``.  For coefficient modulus 2, ``local_power<=N`` selects the
    exact repeated-root factor ``Phi_2**local_power=(z+1)**local_power`` of
    ``z**N+1`` in characteristic two.
    """
    from number_compiler.arithmetic.carry.carry_normalization import (
        end_around_normalization_defect,
        normalization_digits_lsf,
    )
    from number_compiler.arithmetic.polynomials.digit_convolution import (
        negacyclic_binary_square_projection,
    )

    value, n, q = int(value), int(index), int(coefficient_modulus)
    if n < 1:
        raise ValueError(n)
    width = 1 << n
    integer_modulus = (1 << width) + 1
    if not 0 <= value < integer_modulus:
        raise ValueError((value, n))
    if q == 2:
        power = width if local_power is None else int(local_power)
        if not 1 <= power <= width:
            raise ValueError((power, width))
        order = 2
        factor = None
    else:
        order = 2 * width
        power = 1
        factor = None
        if factor_index is not None:
            factor = cyclotomic_factors_mod_prime(order, q)[int(factor_index)]
    kwargs: _ComponentOptions = {
        "order": order,
        "modulus": q,
        "power": power,
        "factor": factor,
    }
    source_digits = _signed_binary_digits(value, width, -1)
    source = CyclotomicDigitBlock.from_coefficients(
        source_digits, length=width, **kwargs
    )
    projection = negacyclic_binary_square_projection(value, width)
    raw = CyclotomicDigitBlock.from_coefficients(
        projection.field, length=width, **kwargs
    )
    algebraic = source.square()
    target_digits = normalization_digits_lsf(projection.normalization)
    normalized = CyclotomicDigitBlock.from_coefficients(
        target_digits, length=width, **kwargs
    )
    defect = end_around_normalization_defect(projection.field, projection.normalization)
    component = normalization_component(defect, **kwargs)
    result = FamilyCyclotomicStep(
        "fermat",
        value,
        projection.residue,
        source,
        raw,
        normalized,
        component,
        algebraic,
    )
    if not result.exact:
        raise AssertionError(result)
    return result


__all__ = [
    "CollatzPiecewiseCyclotomicStep",
    "FamilyCyclotomicStep",
    "NormalizationCyclotomicComponent",
    "collatz_cyclotomic_step",
    "collatz_piecewise_cyclotomic_step",
    "fermat_cyclotomic_step",
    "mersenne_cyclotomic_step",
    "normalization_component",
    "reverse_add_cyclotomic_step",
]
