"""Bounded reuse of exact Mahler actions derived from admitted images.

Exact predicate offsets and caps are payload, never finite-observer aliases.
The caller authenticates its scheduler image first; a process lease is then
qualified by every input to the pure action constructor and its pinned law.
Source occurrence authority is not transferred by this cache. No branch word
is rebuilt.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Final, cast

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.input_validation import is_exact_object_tuple
from number_compiler.arithmetic.fields.consumer_pullback import (
    ExactRational,
    SaturatingAffineAction,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import antihydra as _antihydra_keys
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
_ASSOCIATED_ACTION_CACHE_VERSION: Final[str] = "complete-action-v2-exact-inputs"


def build_action(
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
    if not is_exact_object_tuple(value) or len(value) != 5:
        raise ValueError("Mahler cache contains another action sort")
    first, second, third, fourth, cap = value
    if (
        type(first) is not int
        or type(second) is not int
        or type(third) is not int
        or type(fourth) is not int
    ):
        raise TypeError("Mahler cached action requires exact integers")
    if second <= 0 or fourth <= 0:
        raise ValueError("Mahler cached action has invalid denominators")
    if first <= 0:
        raise ValueError("Mahler cached action requires positive scale")
    cap_value: tuple[int, int] | None = None
    if cap is not None:
        if not is_exact_object_tuple(cap) or len(cap) != 2:
            raise ValueError("Mahler cached cap has another sort")
        cap_numerator, cap_denominator = cap
        if (
            type(cap_numerator) is not int
            or type(cap_denominator) is not int
            or cap_denominator <= 0
        ):
            raise ValueError("Mahler cached cap has another sort")
        cap_value = (cap_numerator, cap_denominator)
    # Only extents >=1024 enter this memo. The admitted centered 11 prefix
    # has already failed at return two; a decoded action must preserve it.
    if cap_value is None or cap_value[0] >= 0:
        raise ArithmeticError("cached Mahler cap lost its two-bit failure")
    return SaturatingAffineAction(
        ExactRational(first, second),
        ExactRational(third, fourth),
        ExactRational(*cap_value),
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
    ledger.bump(
        _antihydra_keys.MAHLER_HASHLIFE_ACTION_VALIDATION_OPERAND_BITS, operand_bits
    )
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
    # The scheduler projection has already authenticated this image.  Keep
    # consuming its published transfer directly; wrapping it as a saturated
    # aggregate creates a second observation of the same summary.
    transfer = workspace.summary().transfer
    source = workspace.source_node(workspace.root_source)
    ledger = workspace.ledger
    ledger.bump(_antihydra_keys.MAHLER_SOURCE_COMPOSED_IMAGE_READS)
    ledger.bump(
        _antihydra_keys.MAHLER_SOURCE_ARITHMETIC_OPERAND_BITS,
        transfer.upper.bit_length()
        + abs(transfer.offset).bit_length()
        + transfer.lower.bit_length(),
    )
    normal = workspace.mahler_root_wire()
    if normal is not None:
        extent, offset_hat, cap_hat = normal
        denominator = 1 << (extent + 2)
        ledger.bump(_antihydra_keys.MAHLER_HASHLIFE_SOURCE_ACTION_PROJECTIONS)
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
        "action_lookups",
        "action_exact_hits",
        "action_process_hits",
        "action_misses",
        "action_publications",
        "action_admission_rejections",
        "action_bypasses",
        "action_disabled_bypasses",
        "action_policy_bypasses",
        "action_key_operand_bits",
        "action_validation_operand_bits",
        "failed_work",
    ):
        ledger.bump("mahler_hashlife_" + metric, 0)
    # These are decisions not to look up an outer-cache record, not misses
    # or capacity refusals. Disabled reuse takes precedence over size policy.
    if not workspace.shared_cache or workspace.returns < 1024:
        reason = "disabled" if not workspace.shared_cache else "policy"
        ledger.bump(f"mahler_hashlife_action_{reason}_bypasses")
        return build_action(*args)
    cache = get_process_cache()
    if not cache.enabled:
        ledger.bump(_antihydra_keys.MAHLER_HASHLIFE_ACTION_DISABLED_BYPASSES)
        return build_action(*args)
    qualification = cast(
        tuple[ImmutableValue, ...],
        (
            MACHINE_SHA256,
            workspace.law.descriptor,
            args[0],
            args[1],
            transfer.upper,
            transfer.offset,
            transfer.lower,
            "centered-parity-strict-margin-positive-infinity",
        ),
    )
    ledger.bump(
        _antihydra_keys.MAHLER_HASHLIFE_ACTION_KEY_OPERAND_BITS,
        args[0].bit_length()
        + args[1].bit_length()
        + transfer.upper.bit_length()
        + abs(transfer.offset).bit_length()
        + transfer.lower.bit_length(),
    )
    try:
        lease = cache.acquire(
            "mahler-associated-action",
            _ASSOCIATED_ACTION_CACHE_VERSION,
            qualification,
        )
    except BlockContextBudgetExceeded:
        ledger.bump(_antihydra_keys.MAHLER_HASHLIFE_ACTION_BYPASSES)
        return build_action(*args)
    with lease:
        ledger.bump(_antihydra_keys.MAHLER_HASHLIFE_ACTION_LOOKUPS)
        try:
            found = lease.get_issued((), _ASSOCIATED_ACTION_PUBLISHER)
        except CacheRecordIssuerMismatch:
            ledger.bump(_antihydra_keys.MAHLER_HASHLIFE_ACTION_ADMISSION_REJECTIONS)
            ledger.bump(_antihydra_keys.MAHLER_HASHLIFE_FAILED_WORK)
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
                ledger.bump(_antihydra_keys.MAHLER_HASHLIFE_ACTION_ADMISSION_REJECTIONS)
                ledger.bump(_antihydra_keys.MAHLER_HASHLIFE_FAILED_WORK)
                raise
            # This immutable value is a pure action, not a source occurrence.
            # Exact constructor inputs qualify reuse; the caller has already
            # authenticated the receiving image at the projection boundary.
            ledger.bump(_antihydra_keys.MAHLER_HASHLIFE_ACTION_PROCESS_HITS)
            ledger.bump(_antihydra_keys.MAHLER_HASHLIFE_ACTION_EXACT_HITS)
            return action
        ledger.bump(_antihydra_keys.MAHLER_HASHLIFE_ACTION_MISSES)
        action = build_action(*args)
        if lease.put_issued((), _encode(action), _ASSOCIATED_ACTION_PUBLISHER):
            ledger.bump(_antihydra_keys.MAHLER_HASHLIFE_ACTION_PUBLICATIONS)
        else:
            ledger.bump(_antihydra_keys.MAHLER_HASHLIFE_ACTION_BYPASSES)
        return action
