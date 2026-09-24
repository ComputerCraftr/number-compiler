"""Antihydra's return law and physical projection of shared dyadic images.

Source admission, precision transport, composition, and failure descent belong
to the shared scheduler engine.  This adapter only supplies the arithmetic law
and converts demanded bounded leaves to the existing guarded roof consumer.
"""

from __future__ import annotations

from collections.abc import Hashable, Iterator

from number_compiler.arithmetic.fields.consumer_pullback import (
    ExactRational,
    SaturatingAffineAction,
)
from number_compiler.arithmetic.fields.skew_transfer import integer_dyadic_fiber_action
from number_compiler.hashlife.execution.dyadic_return_images import (
    DyadicImageSummary,
    DyadicReturnActionID,
    DyadicReturnImageID,
    DyadicReturnImageWorkspace,
    DyadicReturnLaw,
    DyadicReturnSourceID,
    DyadicReturnSupportID,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.hashlife.execution.source_bound_images import (
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageProjection,
    SourceImageView,
)
from number_compiler.sequences.antihydra.blocks import ArithmeticCylinder

ANTIHYDRA_ARITHMETIC_LAW = DyadicReturnLaw(
    family="antihydra-arithmetic-source-image",
    semantic_version="antihydra-arithmetic-source-image-v2-dyadic",
    gains=(3, 3),
    offsets=(0, -1),
    weights=(2, -1),
)


class AntihydraArithmeticImageWorkspace(DyadicReturnImageWorkspace):
    """Pinned blank-tape arithmetic source; physical roofs remain demanded."""

    def __init__(self, ledger: ResourceLedger, returns: int) -> None:
        super().__init__(ledger, 8, returns, ANTIHYDRA_ARITHMETIC_LAW)

    @property
    def returns(self) -> int:
        return self.steps

    def validate(self) -> None:
        try:
            super().validate()
            if self.seed != 8 or self.law != ANTIHYDRA_ARITHMETIC_LAW:
                raise ValueError("another source law")
        except (ValueError, TypeError, AttributeError) as error:
            raise ValueError("Antihydra arithmetic source image was changed") from error

    def apply_composite(
        self,
        action: Hashable,
        source: SourceImageView,
        demand: SourceImageDemand | None,
    ) -> SourceImageCandidate | None:
        """Publish a complete return image from the admitted source cylinder.

        The shared direct constructor retains chronological support for this
        law. Guarded TM and directional consumers still need its bounded
        branch words, while ordinary arithmetic and Mahler consume the same
        complete image without asking the scheduler for midpoint images.
        """
        self.validate_action(action)
        self.validate_payload(source.payload)
        if (
            demand not in (None, SourceImageDemand("physical-summary"))
            or source.binding.action != self.identity
            or type(action) is not DyadicReturnActionID
        ):
            return super().apply_composite(action, source, demand)
        if self.action_node(action).width <= self.MAX_LEAF_STEPS:
            return super().apply_composite(action, source, demand)
        return self.complete_composite_candidate(action, source)

    def project(
        self, image: SourceImageView, demand: SourceImageDemand
    ) -> SourceImageProjection:
        if demand == SourceImageDemand("mahler-associated-action"):
            # The associated action is a consumer of this same admitted image.
            # Its first two centered bits are 11, although the physical h bits
            # are 00.  Their cap becomes negative at return two, so all later
            # source-selected steps act affinely on that prefix image.
            if (
                image.payload != self.root_payload
                or image.binding.source != self.root_source
                or image.binding.action != self.root_action
                or image.binding.extent != self.returns
                or self.seed != 8
                or self.law != ANTIHYDRA_ARITHMETIC_LAW
            ):
                raise ValueError("Mahler projection has another source image")
            transfer = self.saturated_summary().transfer
            if self.returns and self.source_node(self.root_source).residue & 1:
                raise ValueError("Mahler source lost its centered odd first bit")
            if self.returns >= 2 and self.source_node(self.root_source).residue & 3:
                raise ValueError("Mahler source lost its centered 11 prefix")
            scale = ExactRational(transfer.upper, transfer.lower)
            centered_offset = ExactRational(
                transfer.upper + transfer.offset - transfer.lower,
                transfer.lower,
            )
            offset = ExactRational(-3) * centered_offset
            if self.returns >= 2:
                # The first two odd associated steps have affine part
                # (9/4)x - 15/4.  The remaining source-selected tail must
                # retain nonpositive offset; then its positive cap is never
                # active on the negative two-bit prefix image.
                tail_offset = offset - (scale / ExactRational(9, 4)) * ExactRational(
                    -15, 4
                )
                if tail_offset > ExactRational(0):
                    raise ValueError("source Mahler tail lost its nonpositive offset")
            cap = (
                None
                if self.returns == 0
                else ExactRational(3, 4)
                if self.returns == 1
                else ExactRational(3, 2) * scale + offset
            )
            action = SaturatingAffineAction(scale, offset, cap)
            if self.returns >= 2 and (cap is None or cap >= ExactRational(0)):
                raise ArithmeticError("source Mahler cap lost its two-bit failure")
            self.ledger.bump("mahler_source_composed_image_reads")
            self.ledger.bump(
                "mahler_source_arithmetic_operand_bits",
                transfer.upper.bit_length()
                + abs(transfer.offset).bit_length()
                + transfer.lower.bit_length(),
            )
            return SourceImageProjection(action)
        return super().project(image, demand)

    def segments(self) -> Iterator[tuple[int, ArithmeticCylinder]]:
        for start, summary, word in self.leaf_summaries():
            transfer = summary.transfer
            chart = integer_dyadic_fiber_action(
                transfer, summary.residue, summary.width
            )
            output = chart.addend
            yield (
                start,
                ArithmeticCylinder(
                    summary.width,
                    summary.residue,
                    output,
                    summary.delta,
                    summary.minimum,
                    word,
                ),
            )


AntihydraArithmeticActionID = DyadicReturnActionID
AntihydraArithmeticImageID = DyadicReturnImageID
AntihydraArithmeticSourceID = DyadicReturnSourceID
AntihydraArithmeticSupportID = DyadicReturnSupportID
ArithmeticImageSummary = DyadicImageSummary

__all__ = [
    "ANTIHYDRA_ARITHMETIC_LAW",
    "AntihydraArithmeticActionID",
    "AntihydraArithmeticImageID",
    "AntihydraArithmeticImageWorkspace",
    "AntihydraArithmeticSourceID",
    "AntihydraArithmeticSupportID",
    "ArithmeticImageSummary",
]
