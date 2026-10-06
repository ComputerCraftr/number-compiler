"""Exact term rendering, independent of command parsing and execution."""

from __future__ import annotations

import sys
from collections.abc import Iterable
from dataclasses import asdict, fields

from number_compiler.api.number_api import (
    AntihydraTermPayload,
    CommaTermPayload,
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
from number_compiler.arithmetic.fields.radix import iter_digits_lsd
from number_compiler.arithmetic.fields.symbolic_extent import (
    CoordinatePresentation,
    Extent,
    extent_json_value,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.output_stream_metrics import closing_output_stream
from number_compiler.sequences.reverse_add.extent import ReverseAddExtent

_DIGITS = "0123456789abcdefghijklmnopqrstuvwxyz"
_DIGIT_BYTES = _DIGITS.encode("ascii")


def _term_ledger(term: ProjectedNumberTerm) -> ResourceLedger | None:
    """Return an existing runtime ledger without constructing an execution owner."""
    owner = term.payload
    if isinstance(owner, (PoweredReverseAddTermPayload, PoweredCollatzTermPayload)):
        return owner.term._ledger
    if isinstance(owner, (AntihydraTermPayload, CommaTermPayload)):
        return owner.term.ledger
    return None


def _metrics_json(
    term: ProjectedNumberTerm,
    *,
    coordinate: CoordinatePresentation | None = None,
) -> dict[str, object]:
    """Separate immutable construction descriptors from observed runtime work."""
    # Projection descriptors are immutable. Do not recursively copy scheduler
    # counters only to replace that copy with their JSON mapping below.
    descriptors = fields(term.metrics)
    payload = {field.name: getattr(term.metrics, field.name) for field in descriptors}
    payload["descriptor_reporting"] = {
        "field_reads": len(descriptors),
        "counter_items_copied": len(term.metrics.prime_scheduler_counters),
    }
    payload["width"] = (
        None
        if term.metrics.width is None
        else extent_json_value(term.metrics.width, coordinate=coordinate)
    )
    payload["metrics_scope"] = "construction_and_projection_descriptors"
    payload["prime_scheduler_counters"] = dict(term.metrics.prime_scheduler_counters)
    if term.family == "prime":
        payload["prime_scheduler_metrics_scope"] = "query_before_disposal"
    from number_compiler.resources.temporal_diagnostics import (
        collect_temporal_diagnostics_snapshot,
    )

    ledger = _term_ledger(term)
    if ledger is not None:
        payload["execution_metrics"] = asdict(
            collect_temporal_diagnostics_snapshot(ledger)
        )
        payload["execution_metrics_scope"] = "current_query_ledger_snapshot"
    else:
        payload["execution_metrics"] = None
        payload["execution_metrics_scope"] = "unavailable_for_this_family"
    from number_compiler.resources.process_cache import process_cache_stats

    shared = process_cache_stats()
    payload["process_cache"] = None if shared is None else asdict(shared)
    payload["process_cache_scope"] = "process_aggregate_not_query_work"
    return payload


def _radix_string_from_lsd(digits: Iterable[int], base: int) -> str:
    base = _integer(base, "text output base", 2, len(_DIGITS))
    with closing_output_stream(digits) as stream:
        encoded = bytearray(
            _DIGIT_BYTES[_integer(d, "output digit", 0, base - 1)] for d in stream
        )
    encoded.reverse()
    return encoded.decode("ascii") or "0"


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
    encoded = bytearray()
    with closing_output_stream(digits) as stream:
        for digit in stream:
            accumulator |= (
                _integer(digit, "output digit", 0, source_base - 1) << available
            )
            available += source_bits
            while available >= target_bits:
                encoded.append(_DIGIT_BYTES[accumulator & (output_base - 1)])
                accumulator >>= target_bits
                available -= target_bits
    if available:
        encoded.append(_DIGIT_BYTES[accumulator])
    while len(encoded) > 1 and encoded[-1] == ord("0"):
        encoded.pop()
    encoded.reverse()
    return encoded.decode("ascii") or "0"


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
    encoded = bytearray(_DIGIT_BYTES[digit] for digit in iter_digits_lsd(value, base))
    encoded.reverse()
    return encoded.decode("ascii")


def _render_value(term: ProjectedNumberTerm, *, output_base: int, max_bits: int) -> str:
    output_base = _integer(output_base, "--output-base", 2, len(_DIGITS))
    max_bits = _integer(max_bits, "--max-output-bits", 1)
    ledger = _term_ledger(term)
    if ledger is None:
        return _render_value_body(term, output_base=output_base, max_bits=max_bits)
    for name in ("emitted_digits", "failures", "integer_conversion_operand_bits"):
        ledger.bump("cli_render_" + name, 0)
    ledger.bump("cli_render_requests")
    try:
        result = _render_value_body(term, output_base=output_base, max_bits=max_bits)
    except BaseException:
        ledger.bump("cli_render_failures")
        raise
    ledger.bump("cli_render_emitted_digits", len(result))
    return result


def _render_value_body(
    term: ProjectedNumberTerm, *, output_base: int, max_bits: int
) -> str:
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
    elif isinstance(term.payload, PoweredCollatzTermPayload):
        upper_bound = term.payload.term.maximum_width
        bit_extent = (
            upper_bound if upper_bound <= max_bits else term.payload.term.width()
        )
    elif isinstance(term.payload, CommaTermPayload):
        upper_bound = term.payload.estimated_bit_length
        bit_extent = (
            upper_bound
            if upper_bound <= max_bits
            else term.payload.materialize(max_bits=max_bits).bit_length()
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

    value = term.materialize(max_bits=max_bits)
    ledger = _term_ledger(term)
    if ledger is not None:
        ledger.bump("cli_render_integer_conversion_operand_bits", value.bit_length())
    return _radix_string(value, output_base)
