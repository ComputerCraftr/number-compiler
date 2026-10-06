"""Collatz adapter for the shared dyadic return source-image engine."""

from __future__ import annotations

from collections.abc import Hashable, Iterator
from dataclasses import replace

from number_compiler.hashlife.execution.dyadic_return_images import (
    DyadicCycleSummary,
    DyadicImageSummary,
    DyadicReturnActionID,
    DyadicReturnCycle,
    DyadicReturnImageID,
    DyadicReturnImageWorkspace,
    DyadicReturnLaw,
    DyadicReturnSourceID,
    DyadicReturnSupportID,
)
from number_compiler.hashlife.execution.source_bound_images import (
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageView,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.tape_width import (
    CollatzTapeWidthSummary,
    cycle_width_summary,
)

COLLATZ_PHYSICAL_LAW = DyadicReturnLaw(
    family="collatz-physical-source-image",
    semantic_version="collatz-physical-source-image-v2-dyadic",
    gains=(1, 6),
    offsets=(0, 2),
    weights=(0, 1),
    cycle=DyadicReturnCycle((1, 4, 2)),
)
_TAPE_WIDTH_PORT = "collatz-tape-width-summary-v1"


class CollatzPhysicalImageWorkspace(DyadicReturnImageWorkspace):
    """Fixed physical Collatz steps using the shared dyadic law engine."""

    def __init__(
        self,
        ledger: ResourceLedger,
        seed: int,
        steps: int,
        *,
        retain_chronology: bool = True,
        shared_cache: bool = False,
        include_width_spine: bool = False,
    ) -> None:
        if type(retain_chronology) is not bool:
            raise TypeError("Collatz chronology choice must be Boolean")
        if type(shared_cache) is not bool:
            raise TypeError("shared cache flag must be Boolean")
        if type(include_width_spine) is not bool:
            raise TypeError("width-spine demand must be Boolean")
        self._shared_cache = shared_cache
        self._retain_chronology = retain_chronology
        self._include_width_spine = include_width_spine
        super().__init__(ledger, seed, steps, COLLATZ_PHYSICAL_LAW)

    def retain_chronological_support(self) -> bool:
        return self._retain_chronology

    @property
    def tape_width_summary(self) -> CollatzTapeWidthSummary | None:
        """Return only width data sealed in the root source-image publication."""
        view = self.scheduler._source_image_core().view(self.root_image)
        if (
            view.binding.source != self.root_source
            or view.binding.action != self.root_action
            or view.binding.extent != self.steps
        ):
            raise ValueError("Collatz width summary belongs to another root action")
        summaries: list[CollatzTapeWidthSummary] = []
        for port in view.binding.boundary_ports:
            if type(port) is tuple and len(port) == 2 and port[0] == _TAPE_WIDTH_PORT:
                summary = port[1]
                if type(summary) is not CollatzTapeWidthSummary:
                    raise ValueError("Collatz width publication has another sort")
                summaries.append(summary)
        if len(summaries) > 1:
            raise ValueError("Collatz root image has duplicate width summaries")
        if not summaries:
            return None
        summary = summaries[0]
        if (
            summary.source_width != self.seed.bit_length()
            or summary.physical_ticks != self.steps
        ):
            raise ValueError("Collatz width summary geometry differs from root action")
        return summary

    @staticmethod
    def _attach_tape_width_summary(
        candidate: SourceImageCandidate,
        summary: CollatzTapeWidthSummary,
    ) -> SourceImageCandidate:
        if type(candidate) is not SourceImageCandidate:
            raise TypeError("Collatz width summary needs a source-image candidate")
        if type(summary) is not CollatzTapeWidthSummary:
            raise TypeError("Collatz width summary has another output sort")
        return replace(
            candidate,
            boundary_ports=(*candidate.boundary_ports, (_TAPE_WIDTH_PORT, summary)),
        )

    def admitted_input_key(
        self, action: Hashable, source: SourceImageView
    ) -> Hashable | None:
        """Keep exact run contractions out of low-cylinder effect reuse.

        A balanced image describes the whole low-bit cylinder. The run
        constructor instead publishes a constant transfer for one exact
        source. Its result cannot be transported to another high fiber, even
        when their low bits and centered action agree.
        """
        key = super().admitted_input_key(action, source)
        if (
            type(key) is not tuple
            or not key
            or key[0] != "cylinder"
            or self._retain_chronology
        ):
            return key
        if type(action) is not DyadicReturnActionID:
            return key
        source_id = source.binding.source
        if type(source_id) is not DyadicReturnSourceID:
            return key
        admitted = self.source_node(source_id)
        if not admitted.exact:
            return key
        width = self.action_node(action).width
        source_bits = max(
            1,
            admitted.residue.bit_length(),
            admitted.lift.bit_length() + admitted.precision if admitted.lift else 0,
        )
        self._bump("temporal_reuse_routing_requests")
        self._bump("temporal_reuse_routing_operand_bits", width.bit_length())
        if width <= self.MAX_LEAF_STEPS or width > 2 * source_bits:
            return ("exact-run", admitted.residue, width, admitted.lift)
        from number_compiler.arithmetic.fields.two_adic import v2_positive
        from number_compiler.hashlife.execution.dyadic_return_runs import (
            RunArithmeticWorkspace,
        )

        # The complete homogeneous-run test depends only on the admitted low
        # cylinder, including its all-zero and all-one boundary cases.
        scratch = RunArithmeticWorkspace.for_ledger(self.ledger, "collatz_physical")
        with scratch.scope():
            scratch.require_bits(8 * (admitted.residue.bit_length() + 16))
            self._bump(
                "temporal_reuse_routing_operand_bits", admitted.residue.bit_length() + 1
            )
            run_ticks = (
                2 * v2_positive(admitted.residue + 1)
                if admitted.residue & 1
                else width
                if admitted.residue == 0
                else v2_positive(admitted.residue)
            )
        if width <= run_ticks:
            return ("exact-run", admitted.residue, width, admitted.lift)
        return key

    def apply_composite(
        self,
        action: object,
        source: SourceImageView,
        demand: SourceImageDemand | None,
    ) -> SourceImageCandidate | None:
        self.validate_action(action)
        self.validate_payload(source.payload)
        if demand is not None and (
            demand.name != "physical-summary" or demand.parameters
        ):
            return None
        compressed = self._compressed_cycle_candidate(action, source)
        if compressed is not None:
            return compressed
        contracted = self._run_candidate(action, source)
        if contracted is not None:
            return contracted
        if type(action) is not DyadicReturnActionID:
            raise TypeError("Collatz composite requires its action ID")
        if self.action_node(action).children is None:
            return None
        return self.complete_composite_candidate(action, source)

    def _compressed_cycle_candidate(
        self,
        action: object,
        source: SourceImageView,
    ) -> SourceImageCandidate | None:
        candidate = super()._compressed_cycle_candidate(action, source)
        if candidate is None:
            return None
        if source.binding.source != self.root_source or action != self.root_action:
            return candidate
        ports = candidate.boundary_ports
        if (
            type(ports) is not tuple
            or len(ports) != 7
            or ports[0] != self.law.descriptor
            or ports[1] != "singleton-cycle"
            or type(ports[3]) is not int
        ):
            raise ValueError("pinned Collatz cycle candidate lost its source phase")
        if type(action) is not DyadicReturnActionID:
            raise TypeError("pinned Collatz cycle requires an action ID")
        if self._include_width_spine:
            summary = cycle_width_summary(
                self.ledger, ports[3], self.action_node(action).width
            )
            return self._attach_tape_width_summary(candidate, summary)
        return candidate

    def primitive_run_candidate(
        self,
        action: object,
        source: SourceImageView,
    ) -> SourceImageCandidate | None:
        return self._run_candidate(action, source)

    def _run_candidate(
        self,
        action: object,
        source: SourceImageView,
    ) -> SourceImageCandidate | None:
        """Select maximal normalized runs for an admitted exact source."""
        if self.retain_chronological_support():
            return None
        if type(action) is not DyadicReturnActionID:
            return None
        source_id = source.binding.source
        if type(source_id) is not DyadicReturnSourceID:
            return None
        admitted = self.source_node(source_id)
        width = self.action_node(action).width
        if (
            not admitted.exact
            or source.binding.action != self.identity
            or admitted.precision != width
            or width <= 0
        ):
            return None
        from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer
        from number_compiler.arithmetic.fields.two_adic import v2_positive
        from number_compiler.hashlife.execution.dyadic_return_runs import (
            RunArithmeticWorkspace,
            publish_exact_run_candidate,
        )
        from number_compiler.sequences.collatz.temporal_run_quotient import (
            compile_collatz_temporal_run_quotient,
        )

        # Pick the constructor before any orbit discovery. High-entropy wide
        # sources retain balanced source-cylinder substitution; direct run
        # arithmetic has no all-source logarithmic construction bound.
        source_bits = max(
            1,
            admitted.residue.bit_length(),
            admitted.lift.bit_length() + admitted.precision if admitted.lift else 0,
        )
        scratch = RunArithmeticWorkspace.for_ledger(self.ledger, "collatz_physical")
        with scratch.scope():
            self._bump("temporal_routing_operand_bits", width.bit_length())
            if self.MAX_LEAF_STEPS < width <= 2 * source_bits:
                # Homogeneity through this width depends on the admitted low
                # cylinder alone. Decide the route before assembling its high
                # lift; a mixed cylinder will never use that exact integer.
                scratch.require_bits(8 * (admitted.residue.bit_length() + 16))
                run_ticks = (
                    2 * v2_positive(admitted.residue + 1)
                    if admitted.residue & 1
                    else width
                    if admitted.residue == 0
                    else v2_positive(admitted.residue)
                )
                self._bump(
                    "temporal_routing_operand_bits", admitted.residue.bit_length() + 1
                )
                if width > run_ticks:
                    self._bump("temporal_balanced_routes")
                    return None
            scratch.require_bits(8 * (source_bits + width.bit_length() + 16))
            self._bump("temporal_routing_operand_bits", source_bits)
            source_value = self._source_value(admitted)
            self._bump("temporal_run_routes")
        demand_width = (
            self._include_width_spine
            and source.binding.source == self.root_source
            and action == self.root_action
        )
        quotient = compile_collatz_temporal_run_quotient(
            source_value,
            width,
            ledger=self.ledger,
            shared_cache=self._shared_cache,
            include_width_spine=demand_width,
        )
        cycle = None
        if quotient.cycle_repetitions:
            # The run kernel only pumps at state 1. Recover its already-known
            # tail boundary from physical clock and final cycle phase; no
            # additional trajectory discovery is needed for optional audits.
            tail_phase = (1, 4, 2).index(quotient.endpoint)
            repetitions = quotient.cycle_repetitions
            from number_compiler.hashlife.execution.dyadic_return_transport import (
                cycle_phase_summaries,
            )

            cycle_safety, cycle_odd, remainder_safety, remainder_odd = (
                cycle_phase_summaries(self.law, 0, tail_phase)
            )
            tail_safety = cycle_safety.repeat(repetitions).then(remainder_safety)
            tail_odd = repetitions * cycle_odd + remainder_odd
            self._bump("cycle_safety_transformer_applications")
            self._bump("cycle_compressions")
            cycle = DyadicCycleSummary(
                width - 3 * repetitions - tail_phase,
                0,
                repetitions,
                tail_phase,
                tail_phase,
                tail_odd,
                tail_safety.delta,
                tail_safety.minimum,
            )
        # Constant transfer is valid only for this authenticated exact source.
        # It avoids retaining a growing affine prefix or chronological run list.
        candidate = publish_exact_run_candidate(
            self,
            action,
            source,
            SkewTransfer(0, quotient.endpoint, 1),
            quotient.odd_ticks,
            quotient.odd_ticks,
            0,
            cycle,
        )
        if (
            quotient.tape_width_summary is not None
            and source.binding.source == self.root_source
            and action == self.root_action
        ):
            candidate = self._attach_tape_width_summary(
                candidate, quotient.tape_width_summary
            )
        return candidate

    def segments(self) -> Iterator[tuple[int, int, int]]:
        return self.branch_segments()


CollatzPhysicalActionID = DyadicReturnActionID
CollatzPhysicalImageID = DyadicReturnImageID
CollatzPhysicalSourceID = DyadicReturnSourceID
CollatzPhysicalSupportID = DyadicReturnSupportID
PhysicalImageSummary = DyadicImageSummary


__all__ = [
    "COLLATZ_PHYSICAL_LAW",
    "CollatzPhysicalActionID",
    "CollatzPhysicalImageID",
    "CollatzPhysicalImageWorkspace",
    "CollatzPhysicalSourceID",
    "CollatzPhysicalSupportID",
    "PhysicalImageSummary",
]
