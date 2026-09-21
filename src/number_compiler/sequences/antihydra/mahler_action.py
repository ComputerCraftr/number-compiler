"""Finite source Mahler consumer derived from the admitted arithmetic skew.

Centered arithmetic has offset +e/2; the Mahler affine part has offset -3e/2.
The source begins with centered bits 11, so its second cap is negative.  Every
later bit preserves negativity and has a positive cap.  Thus the tail acts
affinely on the entire image of this prefix; its individual caps are redundant.
This is a source-specific consumer restriction, never a successor identity.
"""

from __future__ import annotations

from operator import add, mul
from typing import TYPE_CHECKING

from number_compiler.arithmetic.fields.consumer_pullback import (
    AssociatedActionArena,
    AssociatedActionID,
    ExactRational,
    SaturatingAffineAction,
    ThresholdDemand,
)
from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer
from number_compiler.hashlife.execution.associated_action_images import (
    AssociatedActionSourceAdapter,
    AssociatedScalarSource,
)
from number_compiler.hashlife.execution.source_bound_images import SourceImageDemand
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.sequences.antihydra.runtime import authenticated_arithmetic_result

if TYPE_CHECKING:
    from number_compiler.sequences.antihydra.runtime import ArithmeticResult, Run


def rational_packet(value: ExactRational | None) -> dict[str, int] | None:
    if value is None:
        return None
    return {"numerator": value.numerator, "denominator": value.denominator}


def source_action(
    result: ArithmeticResult, arena: AssociatedActionArena
) -> AssociatedActionID:
    """Pull the associated action from retained support without a bit replay."""
    result.require_source()
    if arena.ledger is not result.ledger:
        raise ValueError("Mahler action requires its arithmetic source ledger")
    if result.returns == 0:
        return arena.identity
    first = result._term.segments[0].cylinder
    prefix_width = min(2, result.returns)
    if first.parity_word & ((1 << prefix_width) - 1):
        raise ValueError("Mahler source does not have the admitted centered 11 prefix")
    odd = arena.admit(
        SaturatingAffineAction(
            ExactRational(3, 2), ExactRational(-3, 2), ExactRational(3, 4)
        )
    )
    if result.returns == 1:
        return odd
    prefix = arena.compose(odd, odd)
    if result.returns == 2:
        return prefix
    transfer = SkewTransfer(1, 0, 1)
    for segment in result._term.segments:
        transfer = transfer.then(segment.cylinder.skew, multiply=mul, add=add)
        result.ledger.bump("mahler_source_cylinder_compositions")
        result.ledger.bump(
            "mahler_source_arithmetic_operand_bits",
            transfer.upper.bit_length()
            + abs(transfer.offset).bit_length()
            + transfer.lower.bit_length(),
        )
    scale = ExactRational(transfer.upper, transfer.lower)
    centered_offset = ExactRational(
        transfer.upper + transfer.offset - transfer.lower, transfer.lower
    )
    offset = ExactRational(-3) * centered_offset
    before = arena.semantic(prefix)
    tail_scale = scale / before.scale
    tail_offset = offset - tail_scale * before.offset
    if tail_offset > ExactRational(0):
        raise ValueError("source Mahler tail lost its nonpositive affine offset")
    # This uncapped tail is admitted only after the two-bit negative image.
    # It is not the standalone Mahler action of that tail at arbitrary inputs.
    tail = arena.admit(
        SaturatingAffineAction(tail_scale, tail_offset),
        logical_extent=result.returns - 2,
    )
    return arena.compose(prefix, tail)


def action_packet(
    result: ArithmeticResult,
    arena: AssociatedActionArena,
    action: AssociatedActionID,
    first_failure: int | None,
) -> dict[str, object]:
    semantic = arena.semantic(action)
    demand = semantic.pullback(ThresholdDemand())
    return {
        "source_binding": result.source_binding,
        "extent": result.returns,
        "bit_convention": "parity_of_centered_D_equals_a_minus_one",
        "scale": rational_packet(semantic.scale),
        "offset": rational_packet(semantic.offset),
        "cap": rational_packet(semantic.cap),
        "initial_margin": "positive_infinity",
        "pulled_threshold": {
            "possible": demand.possible,
            "strict": demand.strict,
            "threshold": rational_packet(demand.threshold),
        },
        "first_failure": first_failure,
        "first_failure_index_unit": "one_based_macro_return",
        "predicate": "Mahler_strict_margin_positivity",
        "all_time_claim": False,
    }


class MahlerWorkspace:
    """One source consumer; all action applications belong to TileScheduler."""

    def __init__(self, result: ArithmeticResult) -> None:
        result.require_source()
        self.result = result
        self.scheduler = TileScheduler.source_only(result.ledger)
        self.arena = AssociatedActionArena(result.ledger)
        try:
            self.action = source_action(result, self.arena)
            self.adapter = AssociatedActionSourceAdapter(self.arena)
            self.scheduler.register_source_image_adapter(self.adapter)
            threshold = ThresholdDemand()
            self.image = self.scheduler.source_image_demanded(
                self.adapter,
                AssociatedScalarSource(None, threshold),
                self.action,
                SourceImageDemand("threshold", (threshold,)),
            )
        except BaseException:
            self.scheduler.dispose_source_images()
            self.arena.close()
            result.ledger.bump("mahler_associated_publication_rollbacks")
            raise

    def validate(self, result: ArithmeticResult) -> None:
        if (
            result is not self.result
            or type(self.arena) is not AssociatedActionArena
            or type(self.scheduler) is not TileScheduler
            or type(self.adapter) is not AssociatedActionSourceAdapter
            or self.arena.ledger is not result.ledger
            or self.scheduler.ledger is not result.ledger
            or self.adapter.arena is not self.arena
        ):
            raise ValueError("Mahler consumer belongs to another source occurrence")
        scale = ExactRational(3**result.returns, 1 << result.returns)
        offset = ExactRational(3) * (
            ExactRational(7) * scale - ExactRational(result.h - 1)
        )
        cap = None if result.returns == 0 else ExactRational(3, 2) * scale + offset
        if self.arena.record(
            self.action
        ).logical_extent != result.returns or self.arena.semantic(
            self.action
        ) != SaturatingAffineAction(scale, offset, cap):
            raise ValueError("Mahler action lost its source cylinder binding")
        view = self.scheduler._source_image_core().view(self.image)
        if (
            view.binding.action != self.action
            or view.binding.source != AssociatedScalarSource(None, ThresholdDemand())
            or view.binding.extent != result.returns
            or view.failure_prefix != (2 if result.returns >= 2 else None)
        ):
            raise ValueError("Mahler image lost its source action binding")
        result.ledger.bump(
            "mahler_source_validation_operand_bits", result.h.bit_length()
        )

    def packet(self, result: ArithmeticResult) -> dict[str, object]:
        result.require_source()
        self.validate(result)
        failure = self.scheduler.source_first_failure(self.adapter, self.image)
        if failure is not None and type(failure) is not int:
            raise TypeError("Mahler first failure must be an exact return index")
        result.ledger.bump("mahler_associated_action_demands")
        return action_packet(result, self.arena, self.action, failure)


def associated_action(result: Run | ArithmeticResult) -> dict[str, object]:
    arithmetic = authenticated_arithmetic_result(result)
    source_binding = result.source_binding
    workspace = arithmetic._term.mahler_workspace
    if workspace is None:
        workspace = MahlerWorkspace(arithmetic)
        arithmetic._term.mahler_workspace = workspace
    packet = workspace.packet(arithmetic)
    packet["source_binding"] = source_binding
    return packet
