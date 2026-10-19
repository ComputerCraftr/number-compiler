"""Analysis-only power-of-two radix coordinates for Fermat/Mersenne words.

A huge radix can collapse the *digit count* dramatically.  This module charges
where the information moves: the symbolic radix exponent and the bit width of
nonzero coefficients.  It is intentionally not imported by the production
sequence compiler because the resulting multiplication coefficients can be as
wide as the binary word it replaces.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.fields.radix import bit_width


@dataclass(frozen=True, slots=True)
class PowerRadixWordMetrics:
    family: str
    parameter: int
    radix_exponent: int
    digit_count: int
    runs: tuple[tuple[str, int], ...]
    nonzero_digit_payload_bits: int
    radix_parameter_bits: int
    run_length_bits: int
    exact_description_bits: int


def _run_length_bits(runs: tuple[tuple[str, int], ...]) -> int:
    return sum(bit_width(count) for _symbol, count in runs)


def mersenne_power_radix_metrics(
    exponent: int, radix_exponent: int
) -> PowerRadixWordMetrics:
    p, k = int(exponent), int(radix_exponent)
    if p < 2 or k <= 0:
        raise ValueError((p, k))
    q, r = divmod(p, k)
    if r == 0:
        runs: tuple[tuple[str, int], ...] = (("MAX", q),)
        payload = k  # B-1
        digits = q
    else:
        # (2^r-1) B^q + (B^q-1)
        runs = (("TOP", 1),) + ((("MAX", q),) if q else ())
        payload = r + (k if q else 0)
        digits = q + 1
    rbits = bit_width(k)
    lbits = _run_length_bits(runs)
    # Token alphabet is constant; charge radix exponent, run lengths and actual
    # coefficient payloads instead of pretending MAX/TOP are free integers.
    description = rbits + lbits + payload + 2 * len(runs)
    return PowerRadixWordMetrics(
        "mersenne",
        p,
        k,
        digits,
        runs,
        payload,
        rbits,
        lbits,
        description,
    )


def fermat_power_radix_metrics(
    index: int, radix_exponent: int
) -> PowerRadixWordMetrics:
    n, k = int(index), int(radix_exponent)
    if n < 0 or k <= 0:
        raise ValueError((n, k))
    exponent = 1 << n
    q, r = divmod(exponent, k)
    if q == 0:
        # Whole term is one digit 2^E+1.
        runs: tuple[tuple[str, int], ...] = (("VALUE", 1),)
        payload = exponent + 1
        digits = 1
    elif r == 0:
        if q == 1:
            runs = (("ONE", 2),)
        else:
            runs = (("ONE", 1), ("ZERO", q - 1), ("ONE", 1))
        payload = 2
        digits = q + 1
    else:
        # 2^r B^q + 1.
        runs = (("TOP", 1),) + ((("ZERO", q - 1),) if q > 1 else ()) + (("ONE", 1),)
        payload = r + 1
        digits = q + 1
    rbits = bit_width(k)
    lbits = _run_length_bits(runs)
    description = rbits + lbits + payload + 2 * len(runs)
    return PowerRadixWordMetrics(
        "fermat",
        n,
        k,
        digits,
        runs,
        payload,
        rbits,
        lbits,
        description,
    )


def materialize_mersenne_power_radix_digits(
    exponent: int, radix_exponent: int
) -> tuple[int, ...]:
    p, k = int(exponent), int(radix_exponent)
    if p < 2 or k <= 0:
        raise ValueError((p, k))
    base = 1 << k
    value = (1 << p) - 1
    out: list[int] = []
    while value:
        value, digit = divmod(value, base)
        out.append(digit)
    return tuple(out)


def materialize_fermat_power_radix_digits(
    index: int, radix_exponent: int
) -> tuple[int, ...]:
    n, k = int(index), int(radix_exponent)
    if n < 0 or k <= 0:
        raise ValueError((n, k))
    base = 1 << k
    value = (1 << (1 << n)) + 1
    out: list[int] = []
    while value:
        value, digit = divmod(value, base)
        out.append(digit)
    return tuple(out)


__all__ = [
    "PowerRadixWordMetrics",
    "fermat_power_radix_metrics",
    "materialize_fermat_power_radix_digits",
    "materialize_mersenne_power_radix_digits",
    "mersenne_power_radix_metrics",
]
