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
    SourceImageBinding,
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageView,
)
from number_compiler.hashlife.execution.source_image_seals import _typed_equal
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_contracts import (
    PayloadAuditContribution,
    PayloadAuditEntry,
    PayloadAuditStoreBinding,
    register_payload_audit_contract,
)
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


def _register_physical_image_audit(root: CollatzPhysicalImageWorkspace) -> None:
    register_payload_audit_contract(
        root.ledger,
        root,
        "collatz",
        (
            PayloadAuditStoreBinding(
                root.width_owner, "by_width", "dyadic_return_action_index"
            ),
        ),
        audit_collatz_physical_image_workspace,
    )


def audit_collatz_physical_image_workspace(
    ledger: object, root: object
) -> PayloadAuditContribution:
    """Validate Collatz root, law, and owned store before generic payload walks."""
    if (
        type(ledger) is not ResourceLedger
        or type(root) is not CollatzPhysicalImageWorkspace
    ):
        raise TypeError("Collatz physical-image audit received a foreign root")
    if root.ledger is not ledger or root._closed:
        return PayloadAuditContribution(
            (), (PayloadAuditEntry(root.width_owner, root),)
        )
    try:
        root._validate_law()
        if (
            root.law.descriptor != COLLATZ_PHYSICAL_LAW.descriptor
            or type(root.seed) is not int
            or root.seed < 0
            or type(root.steps) is not int
            or root.steps < 0
            or root._law_snapshot != root.law.descriptor
            or type(root._closed) is not bool
        ):
            raise ValueError("physical image root authority differs from Collatz")
    except (ArithmeticError, AttributeError, IndexError, TypeError, ValueError):
        return PayloadAuditContribution(
            (), (PayloadAuditEntry(root.width_owner, root),)
        )
    return PayloadAuditContribution()


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
        try:
            _register_physical_image_audit(self)
        except BaseException:
            self.dispose()
            raise

    def audit_image_binding(
        self,
        binding: SourceImageBinding,
        payload: Hashable,
        failure_prefix: Hashable | None,
    ) -> tuple[Hashable, ...]:
        """Validate exact Collatz image metadata and its optional width port."""
        if type(binding) is not SourceImageBinding:
            raise TypeError("Collatz image audit requires its exact binding")
        self.validate_source(binding.source)
        self.validate_action(binding.action)
        self.validate_payload(payload)
        source_id = binding.source
        action_id = binding.action
        if (
            type(source_id) is not DyadicReturnSourceID
            or type(action_id) is not DyadicReturnActionID
        ):
            raise TypeError("Collatz binding needs local source and action IDs")
        source = self.source_node(source_id)
        action = self.action_node(action_id)
        # Exact-source images retain the resolution of that authenticated
        # source even when a compressed cycle/composite spans more steps.
        # A non-exact cylinder image instead carries the temporal width that
        # its low-bit source prefix certifies. The identity action preserves
        # source precision in either case.
        expected_precision = (
            source.precision if source.exact or action.width == 0 else action.width
        )
        if (
            binding.family != self.family
            or binding.semantic_version != self.semantic_version
            or binding.extent != action.width
            or binding.orientation != 1
            or binding.radix != 2
            or binding.precision != expected_precision
            or failure_prefix is not None
        ):
            raise ValueError("Collatz source-image authority differs from root")
        if type(payload) is not DyadicReturnImageID:
            raise TypeError("Collatz source image has another payload")
        image = self.image_node(payload)
        if image.source != source_id or image.action != action_id:
            raise ValueError("Collatz source image payload differs from its binding")
        summary = image.summary
        self.validate_payload(payload)

        width_ports: list[tuple[object, ...]] = []
        for port in binding.boundary_ports:
            if (
                type(port) is tuple
                and port
                and type(port[0]) is str
                and port[0] == _TAPE_WIDTH_PORT
            ):
                if len(port) != 2:
                    raise ValueError("Collatz width port has an invalid shape")
                width_ports.append(port)
        if len(width_ports) > 1:
            raise ValueError("Collatz root has duplicate width ports")

        ordinary = tuple(
            port
            for port in binding.boundary_ports
            if all(port is not width_port for width_port in width_ports)
        )
        cycle = summary.cycle
        expected_transfer_port = (
            self.law.descriptor,
            summary.transfer.upper,
            summary.transfer.offset,
            summary.transfer.lower,
            summary.odd_steps,
        )
        valid_port = _typed_equal(ordinary, expected_transfer_port)
        if cycle is not None:
            expected_cycle_port = (
                self.law.descriptor,
                "singleton-cycle",
                cycle.entry_steps,
                cycle.cycle_phase,
                cycle.cycles,
                cycle.remainder,
                cycle.terminal_phase,
            )
            valid_port = valid_port or _typed_equal(ordinary, expected_cycle_port)
        if not valid_port:
            raise ValueError("Collatz image transfer/cycle port is inconsistent")

        if not width_ports:
            return ()
        if (
            not self._include_width_spine
            or source_id != self.root_source
            or action_id != self.root_action
            or not source.exact
        ):
            raise ValueError("unrequested Collatz width summary was published")
        numerator = summary.transfer.upper * self.seed + summary.transfer.offset
        endpoint, remainder = divmod(numerator, summary.transfer.lower)
        if remainder or endpoint < 0:
            raise ValueError("Collatz root transfer is not an exact endpoint")
        port = width_ports[0]
        width = port[1]
        if type(width) is not CollatzTapeWidthSummary:
            raise TypeError("Collatz width port has another summary sort")
        width.__post_init__()
        if (
            width.source_width != self.seed.bit_length()
            or width.target_width != endpoint.bit_length()
            or width.physical_ticks != self.steps
            or width.odd_steps != summary.odd_steps
            or width.normalized_symbols + width.odd_steps != self.steps
        ):
            raise ValueError("Collatz width port disagrees with its exact image")
        return (port, width, width.blank)

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
