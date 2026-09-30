"""Bounded reuse of complete, source-authenticated finite Mahler actions.

Exact predicate offsets and caps are occurrence data. A finite deck/safety/
harmonic quotient is insufficient authority for this cache. The caller first
authenticates its scheduler image; the complete source, law, extent, transfer
and consumer convention qualify the shared lease. No branch word is rebuilt.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, cast

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.consumer_pullback import (
    ExactRational,
    SaturatingAffineAction,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.process_cache import (
    MISSING,
    CacheRecordIssuerMismatch,
    ImmutableValue,
    get_process_cache,
)
from number_compiler.sequences.antihydra.machine import MACHINE_SHA256

if TYPE_CHECKING:
    from number_compiler.sequences.antihydra.arithmetic_images import (
        AntihydraArithmeticImageWorkspace,
    )


_ASSOCIATED_ACTION_PUBLISHER = object()


def _build_action(
    returns: int, source_residue: int, upper: int, intercept: int, lower: int
) -> SaturatingAffineAction:
    """The existing exact constructor over the admitted saturated transfer."""
    if returns and source_residue & 1:
        raise ValueError("Mahler source lost its centered odd first bit")
    if returns >= 2 and source_residue & 3:
        raise ValueError("Mahler source lost its centered 11 prefix")
    scale = ExactRational(upper, lower)
    centered_offset = ExactRational(upper + intercept - lower, lower)
    offset = ExactRational(-3) * centered_offset
    if returns >= 2:
        tail_offset = offset - (scale / ExactRational(9, 4)) * ExactRational(-15, 4)
        if tail_offset > ExactRational(0):
            raise ValueError("source Mahler tail lost its nonpositive offset")
    cap = (
        None
        if returns == 0
        else ExactRational(3, 4)
        if returns == 1
        else ExactRational(3, 2) * scale + offset
    )
    action = SaturatingAffineAction(scale, offset, cap)
    if returns >= 2 and (cap is None or cap >= ExactRational(0)):
        raise ArithmeticError("source Mahler cap lost its two-bit failure")
    return action


def _encode(action: SaturatingAffineAction) -> tuple[ImmutableValue, ...]:
    cap = action.cap
    return (
        action.scale.numerator,
        action.scale.denominator,
        action.offset.numerator,
        action.offset.denominator,
        None if cap is None else (cap.numerator, cap.denominator),
    )


def _decode(value: object) -> SaturatingAffineAction:
    if type(value) is not tuple or len(value) != 5:
        raise ValueError("Mahler cache contains another action sort")
    first, second, third, fourth, cap = value
    if any(type(part) is not int for part in (first, second, third, fourth)):
        raise TypeError("Mahler cached action requires exact integers")
    if second <= 0 or fourth <= 0:
        raise ValueError("Mahler cached action has invalid denominators")
    if first <= 0:
        raise ValueError("Mahler cached action requires positive scale")
    if cap is not None and (
        type(cap) is not tuple
        or len(cap) != 2
        or any(type(part) is not int for part in cap)
        or cap[1] <= 0
    ):
        raise ValueError("Mahler cached cap has another sort")
    # Only extents >=1024 enter this memo. The admitted centered 11 prefix
    # has already failed at return two; a decoded action must preserve it.
    if cap is None or cap[0] >= 0:
        raise ArithmeticError("cached Mahler cap lost its two-bit failure")
    return SaturatingAffineAction(
        ExactRational(first, second),
        ExactRational(third, fourth),
        None if cap is None else ExactRational(*cap),
    )


def _matches_admitted_transfer(
    action: SaturatingAffineAction,
    returns: int,
    upper: int,
    intercept: int,
    lower: int,
    ledger: ResourceLedger,
) -> bool:
    """Compare a decoded wire with the admitted transfer, without rebuilding it."""
    carry = upper + intercept - lower
    offset_numerator = -3 * carry
    cap_numerator = 3 * upper + 2 * offset_numerator
    scale = action.scale
    offset = action.offset
    cap = action.cap
    operand_bits = sum(
        abs(value).bit_length()
        for value in (
            upper,
            intercept,
            lower,
            carry,
            offset_numerator,
            cap_numerator,
            scale.numerator,
            scale.denominator,
            offset.numerator,
            offset.denominator,
        )
    )
    if cap is not None:
        operand_bits += sum(
            abs(value).bit_length()
            for value in (cap.numerator, cap.denominator, 2 * lower)
        )
    ledger.bump("mahler_hashlife_occurrence_validation_operand_bits", operand_bits)
    return (
        scale.numerator * lower == upper * scale.denominator
        and offset.numerator * lower == offset_numerator * offset.denominator
        and cap is not None
        and cap.numerator * (2 * lower) == cap_numerator * cap.denominator
        and returns >= 2
    )


def cached_associated_action(
    workspace: AntihydraArithmeticImageWorkspace,
) -> SaturatingAffineAction:
    """Consume the image authenticated by the scheduler projection boundary."""
    transfer = workspace.saturated_summary().transfer
    source = workspace.source_node(workspace.root_source)
    ledger = workspace.ledger
    ledger.bump("mahler_source_composed_image_reads")
    ledger.bump(
        "mahler_source_arithmetic_operand_bits",
        transfer.upper.bit_length()
        + abs(transfer.offset).bit_length()
        + transfer.lower.bit_length(),
    )
    normal = workspace.mahler_root_wire()
    if normal is not None:
        extent, offset_hat, cap_hat = normal
        denominator = 1 << (extent + 2)
        ledger.bump("mahler_hashlife_source_action_projections")
        return SaturatingAffineAction(
            ExactRational(transfer.upper, transfer.lower),
            ExactRational(offset_hat, denominator),
            None if cap_hat is None else ExactRational(cap_hat, denominator),
        )
    args = (
        workspace.returns,
        source.residue,
        transfer.upper,
        transfer.offset,
        transfer.lower,
    )
    if type(workspace.shared_cache) is not bool:
        raise TypeError("shared_cache must be a bool")
    for metric in (
        "occurrence_lookups",
        "occurrence_exact_hits",
        "occurrence_transported_hits",
        "occurrence_local_hits",
        "occurrence_process_hits",
        "occurrence_misses",
        "occurrence_publications",
        "occurrence_applied_hits",
        "occurrence_applied_parent_hits",
        "occurrence_admission_rejections",
        "occurrence_bypasses",
        "occurrence_disabled_bypasses",
        "occurrence_policy_bypasses",
        "failed_work",
    ):
        ledger.bump("mahler_hashlife_" + metric, 0)
    # These are decisions not to look up an outer-cache record, not misses
    # or capacity refusals. Disabled reuse takes precedence over size policy.
    if not workspace.shared_cache or workspace.returns < 1024:
        reason = "disabled" if not workspace.shared_cache else "policy"
        ledger.bump(f"mahler_hashlife_occurrence_{reason}_bypasses")
        return _build_action(*args)
    cache = get_process_cache()
    if not cache.enabled:
        ledger.bump("mahler_hashlife_occurrence_disabled_bypasses")
        return _build_action(*args)
    qualification = cast(
        tuple[ImmutableValue, ...],
        (
            MACHINE_SHA256,
            workspace.seed,
            workspace.returns,
            workspace.law.descriptor,
            source.residue,
            source.precision,
            source.lift,
            transfer.upper,
            transfer.offset,
            transfer.lower,
            "centered-parity-strict-margin-positive-infinity",
        ),
    )
    ledger.bump(
        "mahler_hashlife_occurrence_key_operand_bits",
        workspace.seed.bit_length()
        + workspace.returns.bit_length()
        + source.residue.bit_length()
        + source.precision.bit_length()
        + source.lift.bit_length()
        + transfer.upper.bit_length()
        + abs(transfer.offset).bit_length()
        + transfer.lower.bit_length(),
    )
    try:
        lease = cache.acquire(
            "mahler-associated-action", "complete-occurrence-v1", qualification
        )
    except BlockContextBudgetExceeded:
        ledger.bump("mahler_hashlife_occurrence_bypasses")
        return _build_action(*args)
    with lease:
        ledger.bump("mahler_hashlife_occurrence_lookups")
        try:
            found = lease.get_issued((), _ASSOCIATED_ACTION_PUBLISHER)
        except CacheRecordIssuerMismatch:
            ledger.bump("mahler_hashlife_occurrence_admission_rejections")
            ledger.bump("mahler_hashlife_failed_work")
            raise
        if found is not MISSING:
            try:
                action = _decode(found)
                if not _matches_admitted_transfer(
                    action, args[0], args[2], args[3], args[4], ledger
                ):
                    raise ValueError(
                        "Mahler cached action differs from the admitted transfer"
                    )
            except (TypeError, ValueError, ArithmeticError):
                ledger.bump("mahler_hashlife_occurrence_admission_rejections")
                ledger.bump("mahler_hashlife_failed_work")
                raise
            # The lease qualification includes the complete source, extent,
            # law, and admitted transfer, so this is exact and process-local
            # to the shared observer cache. Returning the action is its use.
            ledger.bump("mahler_hashlife_occurrence_process_hits")
            ledger.bump("mahler_hashlife_occurrence_exact_hits")
            ledger.bump("mahler_hashlife_occurrence_applied_hits")
            return action
        ledger.bump("mahler_hashlife_occurrence_misses")
        action = _build_action(*args)
        if lease.put_issued((), _encode(action), _ASSOCIATED_ACTION_PUBLISHER):
            ledger.bump("mahler_hashlife_occurrence_publications")
        else:
            ledger.bump("mahler_hashlife_occurrence_bypasses")
        return action
