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
    compose_prefix_safety_values,
)
from number_compiler.arithmetic.fields.skew_transfer import (
    SkewTransfer,
    integer_dyadic_fiber_action,
)
from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.hashlife.execution.dyadic_return_images import (
    DyadicImageSummary,
    DyadicReturnActionID,
    DyadicReturnImageID,
    DyadicReturnImageWorkspace,
    DyadicReturnLaw,
    DyadicReturnSourceID,
    DyadicReturnSupportID,
)
from number_compiler.hashlife.execution.dyadic_return_runs import (
    RunArithmeticWorkspace,
    publish_exact_run_candidate,
)
from number_compiler.hashlife.execution.source_bound_images import (
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageProjection,
    SourceImageView,
)
from number_compiler.resources.ledger import ResourceLedger
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

    def _runs(
        self, h: int, width: int, scratch: RunArithmeticWorkspace | None = None
    ) -> Iterator[tuple[int, int, int]]:
        """Select centered maximal runs, retaining only the current exact source."""
        if scratch is None:
            with RunArithmeticWorkspace.for_ledger(
                self.ledger, self.counter_prefix
            ).scope() as local:
                yield from self._run_steps(h, width, local)
            return
        yield from self._run_steps(h, width, scratch)

    @staticmethod
    def _centered_source(h: int, scratch: RunArithmeticWorkspace) -> int:
        scratch.require_bits(8 * (h.bit_length() + 16))
        centered = h - 1
        if centered <= 0:
            raise ValueError("Antihydra run source must have positive centered value")
        return centered

    def _run_steps(
        self, h: int, width: int, scratch: RunArithmeticWorkspace
    ) -> Iterator[tuple[int, int, int]]:
        """Iterate run arithmetic inside an already reserved workspace scope."""
        d = self._centered_source(h, scratch)
        remaining = width
        while remaining:
            source_bits = d.bit_length()
            scratch.require_bits(8 * (source_bits + 16))
            bit = d & 1
            length = min(remaining, v2_positive(d + bit))
            scratch.require_bits(8 * (source_bits + 2 * length + 16))
            upper = 3**length
            d = upper * ((d + bit) >> length) - bit
            self._bump("temporal_run_actions")
            self._bump("temporal_one_run_pumps" if bit else "temporal_zero_run_pumps")
            self._bump(
                "temporal_run_operand_bits",
                source_bits + d.bit_length() + upper.bit_length(),
            )
            yield length, bit, d
            remaining -= length

    def _run_candidate(
        self, action: DyadicReturnActionID, source: SourceImageView
    ) -> SourceImageCandidate:
        node = self.action_node(action)
        source_id = source.binding.source
        if type(source_id) is not DyadicReturnSourceID:
            raise TypeError("Antihydra run source has another sort")
        admitted = self.source_node(source_id)
        if not admitted.exact or admitted.precision != node.width:
            raise ValueError("Antihydra run requires its complete exact source")
        self._bump("temporal_run_routes")
        with RunArithmeticWorkspace.for_ledger(
            self.ledger, self.counter_prefix
        ).scope() as scratch:
            scratch.require_bits(
                8
                * (
                    max(
                        admitted.residue.bit_length(),
                        admitted.precision + admitted.lift.bit_length()
                        if admitted.lift
                        else 0,
                    )
                    + 16
                )
            )
            source_h = self._source_value(admitted)
            endpoint_d = source_h - 1
            delta, minimum, odd_steps = 0, 0, 0
            for (
                length,
                run_delta,
                run_minimum,
                run_odds,
                endpoint_d,
            ) in self._punctured_steps(source_h, node.width, scratch):
                delta, minimum = compose_prefix_safety_values(
                    delta, minimum, run_delta, run_minimum
                )
                # Shared dyadic images count odd h, the complement of centered D.
                odd_steps += run_odds
            # Every centered branch has slope 3/2. Recover the branch affine
            # intercept from its exact source and endpoint once, rather than
            # repeatedly composing coefficients against the growing prefix.
            scratch.require_bits(8 * (source_h.bit_length() + 3 * node.width + 16))
            upper, lower = 3**node.width, 1 << node.width
            offset = (endpoint_d + 1) * lower - upper * source_h
            self._bump(
                "temporal_composition_operand_bits",
                upper.bit_length()
                + lower.bit_length()
                + abs(offset).bit_length()
                + source_h.bit_length()
                + endpoint_d.bit_length(),
            )
            transfer = SkewTransfer(upper, offset, lower)
            return publish_exact_run_candidate(
                self, action, source, transfer, odd_steps, delta, minimum
            )

    def _punctured_steps(
        self, h: int, width: int, scratch: RunArithmeticWorkspace
    ) -> Iterator[tuple[int, int, int, int, int]]:
        """Contract bounded source events inside the scheduler's exact leaf.

        A complete ``0**(q-1) 1`` occurrence has endpoint
        ``3**q * (D >> q) + (3**q+1)//2``, ledger delta ``3-q`` and
        minimum ``1-q``. Neither its event word nor a separate event cylinder
        is needed. Consecutive q=1 occurrences still share one powered odd
        run; a final incomplete zero run retains its own powered action.
        Long mixed sources remain owned by balanced scheduler composition.
        """
        d = self._centered_source(h, scratch)
        remaining = width
        while remaining:
            source_bits = d.bit_length()
            scratch.require_bits(8 * (source_bits + 16))
            if d & 1:
                # Preserve the homogeneous run quotient, including large runs.
                length = min(remaining, v2_positive(d + 1))
                scratch.require_bits(8 * (source_bits + 2 * length + 16))
                upper = 3**length
                d = upper * ((d + 1) >> length) - 1
                delta, minimum, odd_steps = 2 * length, 0, 0
                self._bump("temporal_one_run_pumps")
            else:
                zeros = v2_positive(d)
                length = min(remaining, zeros + 1)
                scratch.require_bits(8 * (source_bits + 2 * length + 16))
                upper = 3**length
                if length > zeros:
                    d = upper * (d >> length) + (upper + 1) // 2
                    delta, minimum, odd_steps = 3 - length, 1 - length, zeros
                    self._bump("temporal_punctured_event_actions")
                    self._bump("temporal_punctured_event_symbols", length)
                else:
                    d = upper * (d >> length)
                    delta, minimum, odd_steps = -length, -length, length
                    self._bump("temporal_zero_run_pumps")
            self._bump("temporal_run_actions")
            self._bump(
                "temporal_run_operand_bits",
                source_bits + d.bit_length() + upper.bit_length(),
            )
            yield length, delta, minimum, odd_steps, d
            remaining -= length

    def retain_chronological_support(self) -> bool:
        """Retain only the complete affine and ledger effect until explicit demand."""
        return False

    def _whole_initial_run(self, source: SourceImageView, width: int) -> bool:
        """Admit a homogeneous run from its low cylinder, without its value.

        For ``h=r+2**width*u`` and centered ``d=h-1``, a run of at least
        ``width`` symbols is exactly ``r in {0,1}`` with ``u>0``. At r=0
        the odd centered branch has ``d+1=h``; at r=1 the even branch has
        ``d=h-1``. Both tests depend only on the admitted cylinder ports.
        """
        source_id = source.binding.source
        if type(source_id) is not DyadicReturnSourceID:
            raise TypeError("Antihydra source has another sort")
        admitted = self.source_node(source_id)
        if not admitted.exact or admitted.precision != width or width <= 0:
            raise ValueError("Antihydra run selection requires its exact cylinder")
        self._bump(
            "temporal_run_selection_operand_bits",
            admitted.residue.bit_length()
            + admitted.lift.bit_length()
            + width.bit_length(),
        )
        return admitted.lift > 0 and admitted.residue in (0, 1)

    def apply_composite(
        self,
        action: Hashable,
        source: SourceImageView,
        demand: SourceImageDemand | None,
    ) -> SourceImageCandidate | None:
        """Publish one source-bound carry and ledger, without a branch itinerary."""
        self.validate_action(action)
        self.validate_payload(source.payload)
        if (
            demand not in (None, SourceImageDemand("physical-summary"))
            or source.binding.action != self.identity
            or type(action) is not DyadicReturnActionID
            or self.action_node(action).width == 0
        ):
            return super().apply_composite(action, source, demand)
        source_id = source.binding.source
        if type(source_id) is not DyadicReturnSourceID:
            raise TypeError("Antihydra source has another sort")
        width = self.action_node(action).width
        if self.source_node(source_id).exact and (
            width <= self.MAX_LEAF_STEPS or self._whole_initial_run(source, width)
        ):
            return self._run_candidate(action, source)
        # Mixed long sources use balanced coefficient composition. This keeps
        # precision work bounded without retaining chronological branch words.
        self._bump("temporal_balanced_routes")
        return self.complete_composite_candidate(action, source)

    def primitive_run_candidate(
        self, action: Hashable, source: SourceImageView
    ) -> SourceImageCandidate | None:
        source_id = source.binding.source
        if type(source_id) is not DyadicReturnSourceID:
            raise TypeError("Antihydra source has another sort")
        if (
            type(action) is DyadicReturnActionID
            and 0 < self.action_node(action).width <= self.MAX_LEAF_STEPS
            and self.source_node(source_id).exact
            and source.binding.action == self.identity
        ):
            return self._run_candidate(action, source)
        return None

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
            source_residue = self.source_node(self.root_source).residue
            if self.returns and source_residue & 1:
                raise ValueError("Mahler source lost its centered odd first bit")
            if self.returns >= 2 and source_residue & 3:
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
