"""Collatz adapter for the shared dyadic return source-image engine."""

from __future__ import annotations

from collections.abc import Hashable, Iterator
from dataclasses import replace

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
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
    _SourceNode,
)
from number_compiler.hashlife.execution.source_bound_images import (
    SourceImageBinding,
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageView,
)
from number_compiler.hashlife.execution.source_image_seals import _typed_equal
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.payload_contracts import (
    PayloadAuditContribution,
    PayloadAuditEntry,
    PayloadAuditStoreBinding,
    register_payload_audit_contract,
)
from number_compiler.sequences.collatz.boundary_macros import (
    CollatzBoundaryMacro,
    validate_boundary_macro,
)
from number_compiler.sequences.collatz.joint_temporal_action import (
    CollatzJointRunAction,
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
_JOINT_COCYCLE_PORT = "collatz-joint-temporal-action-v1"
_BOUNDARY_MACRO_PORT = "collatz-first-boundary-macro-v1"


def _boundary_macro_node_cost(_key: str, macro: CollatzBoundaryMacro) -> int:
    """Charge the retained immutable macro and its integer limbs."""
    if type(macro) is not CollatzBoundaryMacro:
        raise TypeError("Collatz boundary memo contains another value sort")
    payload = macro.structural_payload()
    return len(payload) + sum(
        (value.bit_length() + 63) // 64 for value in payload if type(value) is int
    )


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
        include_joint_cocycle: bool = False,
        include_innovation_tape: bool = False,
    ) -> None:
        if type(retain_chronology) is not bool:
            raise TypeError("Collatz chronology choice must be Boolean")
        if type(shared_cache) is not bool:
            raise TypeError("shared cache flag must be Boolean")
        if type(include_width_spine) is not bool:
            raise TypeError("width-spine demand must be Boolean")
        if type(include_joint_cocycle) is not bool:
            raise TypeError("joint-cocycle demand must be Boolean")
        if type(include_innovation_tape) is not bool:
            raise TypeError("innovation-tape demand must be Boolean")
        self._shared_cache = shared_cache
        self._retain_chronology = retain_chronology
        self._include_width_spine = include_width_spine
        self._include_joint_cocycle = include_joint_cocycle
        self._joint_action_snapshot: tuple[int, ...] | None = None
        self._include_innovation_tape = include_innovation_tape
        self._first_boundary_macro_snapshot: tuple[int, tuple[object, ...]] | None = (
            None
        )
        self._boundary_macro_memo: OwnedMemo[str, CollatzBoundaryMacro] | None = None
        self._boundary_route_snapshot: (
            tuple[
                DyadicReturnSourceID,
                DyadicReturnActionID,
                int,
                bool,
            ]
            | None
        ) = None
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
        from number_compiler.sequences.collatz.image_audit import audit_image_binding

        return audit_image_binding(
            self,
            binding,
            payload,
            failure_prefix,
            _TAPE_WIDTH_PORT,
            _JOINT_COCYCLE_PORT,
            _BOUNDARY_MACRO_PORT,
        )

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

    @property
    def joint_action(self) -> CollatzJointRunAction | None:
        """Return only the pre-demanded joint action sealed in the root image."""
        if not self._include_joint_cocycle:
            return None
        view = self.scheduler._source_image_core().view(self.root_image)
        if (
            view.binding.source != self.root_source
            or view.binding.action != self.root_action
            or view.binding.extent != self.steps
        ):
            raise ValueError("Collatz joint action belongs to another root request")
        payloads = tuple(
            port[1]
            for port in view.binding.boundary_ports
            if type(port) is tuple and len(port) == 2 and port[0] == _JOINT_COCYCLE_PORT
        )
        if len(payloads) != 1 or payloads[0] != self._joint_action_snapshot:
            raise BlockContextBudgetExceeded(
                "the admitted Collatz image has no completed joint action"
            )
        try:
            return CollatzJointRunAction._from_admitted_root_payload(payloads[0])
        except (TypeError, ValueError) as error:
            raise BlockContextBudgetExceeded(
                "the admitted Collatz image has an invalid joint action"
            ) from error

    @property
    def first_boundary_macro(self) -> tuple[int, CollatzBoundaryMacro] | None:
        """Return only the demanded macro sealed in this exact root image."""
        if not self._include_innovation_tape:
            return None
        view = self.scheduler._source_image_core().view(self.root_image)
        if (
            view.binding.source != self.root_source
            or view.binding.action != self.root_action
            or view.binding.extent != self.steps
        ):
            raise ValueError("Collatz boundary macro belongs to another root request")
        payloads = tuple(
            port[1]
            for port in view.binding.boundary_ports
            if type(port) is tuple
            and len(port) == 2
            and port[0] == _BOUNDARY_MACRO_PORT
        )
        if not payloads:
            if (
                self._first_boundary_macro_snapshot is not None
                or self._retained_boundary_macro() is not None
            ):
                raise ValueError("Collatz boundary macro snapshot was not published")
            return None
        if len(payloads) != 1 or not _typed_equal(
            payloads[0], self._first_boundary_macro_snapshot
        ):
            raise ValueError("Collatz boundary macro publication is detached")
        payload = payloads[0]
        if (
            type(payload) is not tuple
            or len(payload) != 2
            or type(payload[0]) is not int
            or type(payload[1]) is not tuple
        ):
            raise ValueError("Collatz boundary macro publication has another sort")
        macro = self._retained_boundary_macro()
        if macro is None or not _typed_equal(macro.structural_payload(), payload[1]):
            raise ValueError("Collatz boundary macro occurrence was altered")
        if payload[0] + macro.physical_ticks > self.steps:
            raise ValueError("Collatz boundary macro exceeds its root request")
        return payload[0], macro

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

    def _attach_joint_action(
        self,
        candidate: SourceImageCandidate,
        action: CollatzJointRunAction,
    ) -> SourceImageCandidate:
        if type(candidate) is not SourceImageCandidate:
            raise TypeError("Collatz joint action needs a source-image candidate")
        if type(action) is not CollatzJointRunAction:
            raise TypeError("Collatz joint action has another occurrence sort")
        action.__post_init__()
        if (
            not self._include_joint_cocycle
            or action.source != self.seed
            or action.physical_ticks != self.steps
        ):
            raise ValueError(
                "Collatz joint action does not belong to this root request"
            )
        payload = action.root_port_payload()
        if self._joint_action_snapshot not in (None, payload):
            raise ValueError("conflicting Collatz root joint actions")
        self._joint_action_snapshot = payload
        return replace(
            candidate,
            boundary_ports=(*candidate.boundary_ports, (_JOINT_COCYCLE_PORT, payload)),
        )

    def _attach_boundary_macro(
        self,
        candidate: SourceImageCandidate,
        occurrence: tuple[int, int, int, str],
        macro: CollatzBoundaryMacro,
    ) -> SourceImageCandidate:
        if type(candidate) is not SourceImageCandidate:
            raise TypeError("Collatz boundary macro needs a source-image candidate")
        if (
            type(occurrence) is not tuple
            or len(occurrence) != 4
            or type(occurrence[0]) is not int
            or occurrence[0] < 0
            or type(occurrence[1]) is not int
            or type(occurrence[2]) is not int
            or type(occurrence[3]) is not str
        ):
            raise ValueError("Collatz boundary macro occurrence is malformed")
        start_tick, boundary_source, physical_ticks, family = occurrence
        validate_boundary_macro(macro)
        if (
            macro.source != boundary_source
            or macro.physical_ticks != physical_ticks
            or macro.family != family
        ):
            raise ValueError("Collatz boundary macro differs from its run witness")
        if candidate.extent != self.steps:
            raise ValueError("Collatz boundary macro candidate has another extent")
        if type(candidate.payload) is not DyadicReturnImageID:
            raise TypeError("Collatz boundary macro candidate has another image ID")
        image = self.image_node(candidate.payload)
        if image.source != self.root_source or image.action != self.root_action:
            raise ValueError("Collatz boundary macro candidate is not the exact root")
        if (
            not self._include_innovation_tape
            or macro.source <= 0
            or (start_tick == 0 and macro.source != self.seed)
            or start_tick + macro.physical_ticks > self.steps
        ):
            raise ValueError(
                "Collatz boundary macro differs from its run witness: "
                "outside its demanded root"
            )
        payload = (start_tick, macro.structural_payload())
        if self._first_boundary_macro_snapshot not in (None, payload):
            raise ValueError("conflicting Collatz boundary macro witnesses")
        memo = self._boundary_macro_memo
        if memo is None:
            owner = self.ledger.register(
                f"collatz-boundary-macro-occurrences-{self.ledger.owner_count}",
                "query_memo",
            )
            memo = OwnedMemo(
                self.ledger,
                owner,
                node_cost=_boundary_macro_node_cost,
            )
            self._boundary_macro_memo = memo
        memo["root"] = macro
        self._first_boundary_macro_snapshot = payload
        return replace(
            candidate,
            boundary_ports=(*candidate.boundary_ports, (_BOUNDARY_MACRO_PORT, payload)),
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
        observer_consumer = (
            "collatz-boundary-observer-v1"
            if self._include_innovation_tape
            and source_id == self.root_source
            and action == self.root_action
            else None
        )
        source_bits = max(
            1,
            admitted.residue.bit_length(),
            admitted.lift.bit_length() + admitted.precision if admitted.lift else 0,
        )
        self._bump("temporal_reuse_routing_requests")
        self._bump("temporal_reuse_routing_operand_bits", width.bit_length())
        if width <= self.MAX_LEAF_STEPS or width > 2 * source_bits:
            return self._exact_run_key(admitted, width, observer_consumer)
        from number_compiler.arithmetic.fields.two_adic import v2_positive
        from number_compiler.hashlife.execution.dyadic_return_runs import (
            RunArithmeticWorkspace,
        )

        # The complete homogeneous-run test depends only on the admitted low
        # cylinder, including its all-zero and all-one boundary cases.
        scratch = RunArithmeticWorkspace.for_ledger(self.ledger, "collatz_physical")
        with scratch.scope():
            scratch.require_bits(
                8 * (admitted.residue.bit_length() + 4 * width.bit_length() + 32)
            )
            self._bump(
                "temporal_reuse_routing_operand_bits", admitted.residue.bit_length() + 1
            )
            self._bump("boundary_macro_plan_checks")
            self._bump(
                "boundary_macro_plan_operand_bits",
                admitted.residue.bit_length()
                + admitted.lift.bit_length()
                + width.bit_length(),
            )
            boundary_plan = self._has_admitted_boundary_macro(admitted, width)
            self._boundary_route_snapshot = (
                source_id,
                action,
                width,
                boundary_plan,
            )
            if boundary_plan:
                return self._exact_run_key(admitted, width, observer_consumer)
            run_ticks = (
                2 * v2_positive(admitted.residue + 1)
                if admitted.residue & 1
                else width
                if admitted.residue == 0
                else v2_positive(admitted.residue)
            )
        if width <= run_ticks:
            return self._exact_run_key(admitted, width, observer_consumer)
        return key

    def _exact_run_key(
        self, source: _SourceNode, width: int, consumer: str | None = None
    ) -> tuple[object, ...]:
        if type(source) is not _SourceNode or not source.exact:
            raise TypeError("exact Collatz run key requires an exact source node")
        return (
            "exact-run",
            self.law.descriptor,
            source.residue,
            source.precision,
            width,
            source.lift,
            consumer,
        )

    @staticmethod
    def _source_modulo(source: _SourceNode, modulus: int) -> int:
        """Read a small exact-source residue without assembling its full value."""
        return (
            source.residue + source.lift * pow(2, source.precision, modulus)
        ) % modulus

    def _has_admitted_boundary_macro(self, source: _SourceNode, width: int) -> bool:
        """Classify two-repeat source guards from bounded residues only."""
        if type(source) is not _SourceNode or not source.exact:
            return False
        if (
            width >= 7
            and self._source_modulo(source, 160) == 4
            and (
                source.residue > 4
                or source.lift > 0
                and (
                    source.precision >= 3
                    or (source.lift << source.precision) + source.residue > 4
                )
            )
        ):
            return True
        if width >= 9 and self._source_modulo(source, 160) == 94:
            return True
        if self._source_modulo(source, 20) == 6:
            return width >= 5 and self._source_modulo(source, 80) == 26
        return (
            (self._include_innovation_tape or self._include_joint_cocycle)
            and width >= 4
            and self._source_modulo(source, 20) == 19
            and self._source_modulo(source, 4) == 3
        )

    def _take_boundary_route_snapshot(
        self,
        source_id: DyadicReturnSourceID,
        action_id: DyadicReturnActionID,
        width: int,
    ) -> bool | None:
        snapshot = self._boundary_route_snapshot
        if snapshot is None:
            return None
        self._boundary_route_snapshot = None
        if snapshot[:3] != (source_id, action_id, width):
            return None
        return snapshot[3]

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
        joint_root = (
            self._include_joint_cocycle
            and source.binding.source == self.root_source
            and action == self.root_action
        )
        compressed = (
            None if joint_root else self._compressed_cycle_candidate(action, source)
        )
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
        if self._include_joint_cocycle:
            raise BlockContextBudgetExceeded(
                "joint accumulator for a compressed cycle exceeds its exact run path"
            )
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
        boundary_route: bool | None = None
        if self.MAX_LEAF_STEPS < width <= 2 * source_bits:
            boundary_route = self._take_boundary_route_snapshot(
                source_id, action, width
            )
            if boundary_route is None:
                boundary_route = self._has_admitted_boundary_macro(admitted, width)
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
                if width > run_ticks and (not boundary_route):
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
        demand_joint = (
            self._include_joint_cocycle
            and source.binding.source == self.root_source
            and action == self.root_action
        )
        demand_innovation = (
            self._include_innovation_tape
            and source.binding.source == self.root_source
            and action == self.root_action
        )
        quotient = compile_collatz_temporal_run_quotient(
            source_value,
            width,
            ledger=self.ledger,
            shared_cache=self._shared_cache,
            include_width_spine=demand_width,
            include_joint_cocycle=demand_joint,
            include_innovation_tape=demand_innovation,
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
        if demand_joint:
            if quotient.joint_action is None:
                raise BlockContextBudgetExceeded(
                    "Collatz constructor did not publish its requested joint action"
                )
            candidate = self._attach_joint_action(candidate, quotient.joint_action)
        if demand_innovation and quotient.first_boundary_macro is not None:
            if quotient.first_boundary is None:
                raise ValueError(
                    "Collatz macro result has no source occurrence witness"
                )
            candidate = self._attach_boundary_macro(
                candidate,
                quotient.first_boundary,
                quotient.first_boundary_macro,
            )
        return candidate

    def segments(self) -> Iterator[tuple[int, int, int]]:
        return self.branch_segments()

    def _retained_boundary_macro(self) -> CollatzBoundaryMacro | None:
        memo = self._boundary_macro_memo
        if memo is None:
            return None
        return memo.get("root")

    def _release_boundary_macro_state(self) -> None:
        memo = self._boundary_macro_memo
        try:
            if memo is not None:
                memo.dispose()
        finally:
            self._boundary_macro_memo = None
            self._first_boundary_macro_snapshot = None
            self._boundary_route_snapshot = None

    def _rollback_construction(self) -> None:
        try:
            super()._rollback_construction()
        finally:
            self._release_boundary_macro_state()

    def dispose(self) -> None:
        try:
            super().dispose()
        finally:
            self._release_boundary_macro_state()


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
