"""Bounded process reuse for complete guarded Collatz mixed actions.

The index is intentionally coarse (the low sixteen source bits). Every
candidate carries its full source-cylinder residue, complete joint action, and
parity grammar; the receiving source must pass the full powered guard before
an action is returned. The index itself is never semantic authority.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, cast

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.process_cache import (
    MISSING,
    CacheRecordIssuerMismatch,
    ImmutableValue,
    get_process_cache,
)
from number_compiler.sequences.collatz.mixed_clock_macros import (
    _MIXED_ACTION_CACHE_ISSUER,
    MAX_MIXED_ACTION_SYMBOLS,
    MixedClockMacro,
    _mixed_cache_payload,
    _restore_mixed_cache_payload,
    _validate_mixed_cache_publication,
    validate_mixed_clock_macro,
)

_ISSUER = _MIXED_ACTION_CACHE_ISSUER
_VERSION = "collatz-complete-mixed-action-v2"
_INDEX_BITS = 16
_MAX_RECORDS_PER_PREFIX = 8
_MIXED_RECORD_SIZE = 17


class MixedActionTailNotAdmitted(Exception):
    """A cached action shares the exact cylinder but leaves an oversized tail."""


if TYPE_CHECKING:
    from number_compiler.sequences.collatz.source_cylinder_cache import (
        CollatzDyadicMacros,
    )


def lookup_mixed_action(
    macros: CollatzDyadicMacros,
    source: int,
    physical_ticks: int,
    scratch: RunArithmeticWorkspace,
    *,
    include_width: bool,
    minimum_physical_ticks: int | None = None,
) -> MixedClockMacro | None:
    """Retrieve and admit a complete mixed action before source discovery."""
    if (
        type(source) is not int
        or source <= 0
        or type(physical_ticks) is not int
        or physical_ticks < 0
        or type(include_width) is not bool
        or type(scratch) is not RunArithmeticWorkspace
        or (
            minimum_physical_ticks is not None
            and (type(minimum_physical_ticks) is not int or minimum_physical_ticks < 0)
        )
    ):
        raise ValueError("mixed action cache lookup coordinates are malformed")
    if not getattr(macros, "shared_cache", False):
        return None
    bump = macros._bump
    bump("mixed_lookups")
    prefix = source & ((1 << _INDEX_BITS) - 1)
    bump("mixed_key_operand_bits", source.bit_length() + prefix.bit_length())
    cache = get_process_cache()
    if not cache.enabled:
        bump("mixed_bypasses")
        bump("mixed_misses")
        return None
    try:
        scratch.require_bits(8 * (source.bit_length() + _INDEX_BITS + 32))
        lease = cache.acquire("collatz-mixed-action-index", _VERSION, (prefix,))
    except BlockContextBudgetExceeded:
        bump("mixed_bypasses")
        bump("mixed_misses")
        return None
    with lease:
        try:
            bucket = lease.get_issued(("macro",), _ISSUER)
        except CacheRecordIssuerMismatch:
            bump("mixed_invalid_records")
            bump("failed_work")
            raise
    if bucket is MISSING:
        bump("mixed_misses")
        return None
    bump("mixed_retrieved")
    try:
        records = _decode_mixed_action_bucket(bucket)
    except ValueError:
        bump("mixed_invalid_records")
        bump("failed_work")
        raise
    payload_bits = _mixed_bucket_operand_bits(records)
    bump("mixed_validation_operand_bits", payload_bits)
    # Publication stores a canonical descending order. Validate it once and
    # consume the already-ranked tuple directly on warm lookup; sorting here
    # would repeat publication work on every hit.
    root_tail_rejection = False
    for payload in records:
        action_ticks = _mixed_record_physical_ticks(payload)
        if action_ticks > physical_ticks:
            bump("mixed_rejected_fit")
            continue
        if include_width and source != payload[12]:
            bump("mixed_inapplicable")
            continue
        if minimum_physical_ticks is not None and action_ticks < minimum_physical_ticks:
            try:
                scratch.require_bits(8 * (source.bit_length() + payload[0] + 32))
            except BlockContextBudgetExceeded:
                bump("mixed_bypasses")
                bump("mixed_misses")
                return None
            bump("mixed_validation_operand_bits", source.bit_length() + payload[0])
            if _mixed_record_admits_source(source, payload):
                bump("mixed_root_tail_rejections")
                root_tail_rejection = True
            else:
                bump("mixed_inapplicable")
            continue
        try:
            scratch.require_bits(16 * (source.bit_length() + payload_bits + 32))
        except BlockContextBudgetExceeded:
            bump("mixed_bypasses")
            bump("mixed_misses")
            return None
        bump("mixed_validation_operand_bits", _mixed_record_operand_bits(payload))
        try:
            macro = _restore_mixed_cache_payload(
                source,
                payload,
                include_width=include_width,
                issued_by=_ISSUER,
            )
        except (TypeError, ValueError):
            bump("mixed_invalid_records")
            bump("failed_work")
            raise
        if macro is None:
            bump("mixed_inapplicable")
            continue
        if macro.physical_ticks > physical_ticks:
            bump("mixed_rejected_fit")
            continue
        validate_mixed_clock_macro(macro)
        bump("mixed_admitted")
        bump(
            "mixed_validation_operand_bits",
            macro.fields.gain.bit_length()
            + macro.fields.offset.bit_length()
            + macro.fields.sum_gain.bit_length()
            + macro.fields.sum_offset.bit_length()
            + macro.source.bit_length()
            + macro.endpoint.bit_length(),
        )
        return macro
    if root_tail_rejection:
        raise MixedActionTailNotAdmitted
    return None


def remember_mixed_action(
    macros: CollatzDyadicMacros,
    macro: MixedClockMacro,
    scratch: RunArithmeticWorkspace,
) -> bool:
    """Retain a just-admitted exact grammar/action under the process cap."""
    if type(scratch) is not RunArithmeticWorkspace:
        raise TypeError("mixed action publication needs its execution scratch")
    validate_mixed_clock_macro(macro)
    if not getattr(macros, "shared_cache", False):
        return False
    bump = macros._bump
    cache = get_process_cache()
    if not cache.enabled:
        # This is optional retention.  Do not construct a cache key, exact
        # power, cylinder residue, or serialized payload when process reuse is
        # disabled.
        bump("mixed_bypasses")
        return False
    if not 16 <= macro.normalized_symbols <= MAX_MIXED_ACTION_SYMBOLS:
        bump("mixed_bypasses")
        return False
    if macro.width_blank is None:
        raise ValueError("mixed action publication requires its width summary")
    prefix = macro.source & ((1 << _INDEX_BITS) - 1)
    fields = macro.fields
    residue_bit_bound = min(fields.steps, macro.source.bit_length())
    payload_bits_bound = (
        sum(
            max(1, value.bit_length())
            for value in (
                fields.steps,
                fields.gain,
                fields.offset,
                fields.sum_gain,
                fields.sum_offset,
                fields.previous_gain,
                fields.previous_offset,
                macro.odd_symbols,
                len(macro.motif),
                macro.repetitions,
                macro.source,
                macro.endpoint,
                *macro.width_blank.as_tuple(),
            )
        )
        + max(1, residue_bit_bound)
        + len(macro.motif)
    )
    try:
        # Reserve before computing the exact 3**odd_symbols guard or the
        # source residue.  The largest temporaries are bounded by the current
        # payload, one 2**steps modulus, and the exact gain (at most 2 bits per
        # odd event); these are deliberately charged as construction scratch,
        # not reported as retained payload work.
        scratch.require_bits(
            8
            * (
                payload_bits_bound
                + fields.steps
                + 2 * macro.odd_symbols
                + _INDEX_BITS
                + 32
            )
        )
    except BlockContextBudgetExceeded:
        bump("mixed_bypasses")
        return False
    validation_bits = _validate_mixed_cache_publication(macro)
    bump("mixed_validation_operand_bits", validation_bits)
    payload = _mixed_cache_payload(macro)
    payload_bits = _mixed_record_operand_bits(payload)
    bump("mixed_payload_operand_bits", payload_bits)
    try:
        lease = cache.acquire("collatz-mixed-action-index", _VERSION, (prefix,))
    except BlockContextBudgetExceeded:
        bump("mixed_bypasses")
        return False
    try:

        def merge(existing: object) -> tuple[object, str]:
            if existing is MISSING:
                records: tuple[tuple[int, ...], ...] = ()
            else:
                records = _decode_mixed_action_bucket(existing)
                existing_bits = _mixed_bucket_operand_bits(records)
                # Count the actual retained candidate fields inspected. The
                # count is deliberately separate from the scratch upper bound
                # below, which reserves room for candidate merge and sorting.
                bump("mixed_validation_operand_bits", existing_bits)
                scratch.require_bits(
                    8 * (existing_bits + payload_bits + _INDEX_BITS + 32)
                )
            if payload in records:
                return MISSING, "duplicate"
            retained, disposition = _merge_mixed_action_records(records, payload)
            if disposition != "retained":
                return MISSING, disposition
            return cast(ImmutableValue, retained), disposition

        with lease:
            stored, disposition = lease.update_issued(("macro",), _ISSUER, merge)
    except BlockContextBudgetExceeded:
        bump("mixed_bypasses")
        return False
    except CacheRecordIssuerMismatch:
        bump("mixed_invalid_records")
        bump("failed_work")
        raise
    except ValueError:
        bump("mixed_invalid_records")
        bump("failed_work")
        raise
    if disposition == "duplicate":
        # An identical exact action is already retained in this bucket.
        return True
    if disposition == "pruned":
        # The cap retained larger complete actions, so this candidate was not
        # published and must not be reported as reusable.
        bump("mixed_bypasses")
        return False
    if disposition != "retained":
        bump("mixed_bypasses")
        return False
    if not stored:
        bump("mixed_bypasses")
        return False
    bump("mixed_publications")
    return True


def applied_mixed_action(macros: CollatzDyadicMacros) -> None:
    """Count a retrieved action only after its exact consumer used it."""
    macros._bump("mixed_applied_hits")


def _decode_mixed_action_bucket(payload: object) -> tuple[tuple[int, ...], ...]:
    if (
        type(payload) is not tuple
        or not 1 <= len(payload) <= _MAX_RECORDS_PER_PREFIX
        or any(
            type(record) is not tuple
            or len(record) != _MIXED_RECORD_SIZE
            or any(type(value) is not int for value in record)
            for record in payload
        )
    ):
        raise ValueError("mixed action cache bucket is malformed")
    records = cast(tuple[tuple[int, ...], ...], payload)
    for index in range(1, len(records)):
        if _mixed_record_order(records[index - 1]) <= _mixed_record_order(
            records[index]
        ):
            raise ValueError("mixed action cache bucket is not canonical")
    return records


def _mixed_record_operand_bits(record: tuple[int, ...]) -> int:
    return sum(max(1, value.bit_length()) for value in record)


def _mixed_bucket_operand_bits(records: tuple[tuple[int, ...], ...]) -> int:
    return sum(_mixed_record_operand_bits(record) for record in records)


def _merge_mixed_action_records(
    records: tuple[tuple[int, ...], ...], payload: tuple[int, ...]
) -> tuple[tuple[tuple[int, ...], ...], str]:
    """Keep only the largest bounded actions, reporting a dropped candidate."""
    ranked = sorted((*records, payload), key=_mixed_record_order, reverse=True)
    retained = tuple(ranked[:_MAX_RECORDS_PER_PREFIX])
    if payload not in retained:
        return records, "pruned"
    return retained, "retained"


def _mixed_record_physical_ticks(record: tuple[int, ...]) -> int:
    return record[0] + record[8]


def _mixed_record_admits_source(source: int, record: tuple[int, ...]) -> bool:
    """Check the issuer-bound complete 2-adic cylinder without rebuilding it."""
    steps, residue = record[0], record[1]
    if not 16 <= steps <= MAX_MIXED_ACTION_SYMBOLS:
        raise ValueError("mixed action cache span is outside its issued bound")
    if not 0 <= residue < 1 << steps:
        raise ValueError("mixed action cache source residue is malformed")
    return source % (1 << steps) == residue


def _mixed_record_order(
    record: tuple[int, ...],
) -> tuple[int, int, int, tuple[int, ...]]:
    """Rank larger actions first and use payload as a stable final tie-breaker."""
    return (
        _mixed_record_physical_ticks(record),
        record[0],
        -record[12],
        record,
    )
