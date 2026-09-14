"""Exact term rendering, independent of command parsing and execution."""

from __future__ import annotations

import sys
from collections.abc import Iterable
from dataclasses import asdict

from number_compiler.api.number_api import (
    AntihydraTermPayload,
    FermatTermPayload,
    FormulaTermPayload,
    MersenneTermPayload,
    PoweredCollatzTermPayload,
    PoweredReverseAddTermPayload,
    ProjectedNumberTerm,
)
from number_compiler.arithmetic.contracts.input_validation import (
    require_integer as _integer,
)
from number_compiler.arithmetic.fields.symbolic_extent import (
    Extent,
    ReverseAddExtent,
    extent_json_value,
)

_DIGITS = "0123456789abcdefghijklmnopqrstuvwxyz"


def _metrics_json(term: ProjectedNumberTerm) -> dict[str, object]:
    """Separate immutable construction descriptors from observed runtime work."""
    payload = asdict(term.metrics)
    payload["width"] = extent_json_value(term.metrics.width)
    payload["metrics_scope"] = "construction_and_projection_descriptors"
    if term.family == "prime":
        payload["prime_scheduler_counters"] = dict(
            term.metrics.prime_scheduler_counters
        )
        payload["prime_scheduler_metrics_scope"] = "query_before_disposal"
    if isinstance(
        term.payload, (PoweredReverseAddTermPayload, PoweredCollatzTermPayload)
    ):
        payload["execution_metrics"] = asdict(term.payload.power_metrics())
        payload["execution_metrics_scope"] = "current_powered_term_ledger_snapshot"
    elif isinstance(term.payload, AntihydraTermPayload):
        payload["execution_metrics"] = term.payload.power_metrics()
        payload["execution_metrics_scope"] = "current_arithmetic_term_ledger_snapshot"
    else:
        payload["execution_metrics"] = None
        payload["execution_metrics_scope"] = "unavailable_for_this_family"
    return payload


def _radix_string_from_lsd(digits: Iterable[int], base: int) -> str:
    base = _integer(base, "text output base", 2, len(_DIGITS))
    encoded = [_DIGITS[_integer(d, "output digit", 0, base - 1)] for d in digits]
    return "".join(reversed(encoded)) or "0"


def _power_of_two_radix_string(
    digits: Iterable[int],
    source_base: int,
    output_base: int,
) -> str:
    """Regroup a digit stream using a bounded carry, without an endpoint int."""
    source_base = _integer(source_base, "source radix", 2)
    output_base = _integer(output_base, "text output base", 2, len(_DIGITS))
    if source_base & (source_base - 1) or output_base & (output_base - 1):
        raise ValueError("digit regrouping requires power-of-two radices")
    source_bits, target_bits = (
        source_base.bit_length() - 1,
        output_base.bit_length() - 1,
    )
    accumulator = available = 0
    encoded: list[str] = []
    for digit in digits:
        accumulator |= _integer(digit, "output digit", 0, source_base - 1) << available
        available += source_bits
        while available >= target_bits:
            encoded.append(_DIGITS[accumulator & (output_base - 1)])
            accumulator >>= target_bits
            available -= target_bits
    if available:
        encoded.append(_DIGITS[accumulator])
    while len(encoded) > 1 and encoded[-1] == "0":
        encoded.pop()
    return "".join(reversed(encoded)) or "0"


def _radix_string(value: int, base: int) -> str:
    value = _integer(value, "output value", 0)
    base = _integer(base, "text output base", 2, len(_DIGITS))
    if value == 0:
        return "0"
    if base in (2, 8, 16):
        return format(value, {2: "b", 8: "o", 16: "x"}[base])
    if base == 10:
        previous_limit = sys.get_int_max_str_digits()
        try:
            sys.set_int_max_str_digits(0)
            return str(value)
        finally:
            sys.set_int_max_str_digits(previous_limit)
    out: list[str] = []
    while value:
        value, digit = divmod(value, base)
        out.append(_DIGITS[digit])
    return "".join(reversed(out))


def _render_value(term: ProjectedNumberTerm, *, output_base: int, max_bits: int) -> str:
    output_base = _integer(output_base, "--output-base", 2, len(_DIGITS))
    max_bits = _integer(max_bits, "--max-output-bits", 1)
    bit_extent: Extent
    if isinstance(term.payload, PoweredReverseAddTermPayload):
        powered = term.payload.term
        upper_bound = powered.maximum_width * (powered.base - 1).bit_length()
        # An admitted symbolic upper bound needs no separate exact-width
        # query before the explicit endpoint lowering. Tight caps retain the
        # existing exact-width decision.
        bit_extent = (
            upper_bound if upper_bound <= max_bits else powered.estimated_bit_length
        )
    else:
        bit_extent = term.estimated_bit_length
    if isinstance(bit_extent, ReverseAddExtent):
        bit_extent = bit_extent.materialize()
    if bit_extent > max_bits:
        raise ValueError(f"output exceeds --max-output-bits ({max_bits})")

    if (
        isinstance(term.payload, (FormulaTermPayload, PoweredReverseAddTermPayload))
        and term.source_radix == output_base
    ):
        if not 2 <= output_base <= len(_DIGITS):
            raise ValueError("text output base must be between 2 and 36")
        if isinstance(term.payload, PoweredReverseAddTermPayload):
            return _radix_string_from_lsd(term.payload.iter_digits(), output_base)
        return (
            "".join(_DIGITS[d] for d in term.payload.iter_digits(reverse=True)) or "0"
        )

    if not output_base & (output_base - 1):
        chunk_bits = output_base.bit_length() - 1
        if isinstance(term.payload, FermatTermPayload):
            exponent = term.payload.spec.exponent_extent.materialize(
                max_power=max_bits.bit_length(),
            )
            whole, remainder = divmod(exponent, chunk_bits)
            if not whole:
                return _DIGITS[(1 << remainder) + 1]
            return _DIGITS[1 << remainder] + "0" * (whole - 1) + "1"
        if isinstance(term.payload, MersenneTermPayload):
            whole, remainder = divmod(term.payload.spec.exponent, chunk_bits)
            prefix = _DIGITS[(1 << remainder) - 1] if remainder else ""
            return prefix + _DIGITS[output_base - 1] * whole
        if isinstance(term.payload, PoweredCollatzTermPayload):
            # The physical term's native image is binary, independently of
            # the user's requested Collatz digit-view radix.
            return _power_of_two_radix_string(
                term.payload.term.iter_digits(), 2, output_base
            )
        source_base = term.source_radix
        if (
            isinstance(term.payload, (FormulaTermPayload, PoweredReverseAddTermPayload))
            and source_base is not None
            and not source_base & (source_base - 1)
        ):
            return _power_of_two_radix_string(
                term.payload.iter_digits(), source_base, output_base
            )

    return _radix_string(term.materialize(max_bits=max_bits), output_base)
