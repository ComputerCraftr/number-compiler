"""Collatz adapter for the shared dyadic return source-image engine."""

from __future__ import annotations

from collections.abc import Hashable, Iterator
from dataclasses import replace
from typing import Final

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
from number_compiler.resources.construction_scope import RuntimeConstruction
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.lifecycle import cleanup_all
from number_compiler.resources.payload_contracts import (
    PayloadAuditContribution,
    PayloadAuditEntry,
    PayloadAuditStoreBinding,
    register_payload_audit_contract,
)
from number_compiler.sequences.collatz.border_identity import (
    BoundaryOccurrence,
    is_boundary_occurrence,
)
from number_compiler.sequences.collatz.border_return_grammar import (
    BorderReturnMacro,
    validate_border_return_macro,
)
from number_compiler.sequences.collatz.boundary_macros import (
    CollatzBoundaryMacro,
    validate_boundary_macro,
)
from number_compiler.sequences.collatz.innovation_port_moore import (
    InnovationTapeObservation,
)
from number_compiler.sequences.collatz.innovation_tape_contract import (
    SIGNED_INNOVATION_TAPE_TAG,
)
from number_compiler.sequences.collatz.innovation_temporal_tape import (
    _retained_node_count,
)
from number_compiler.sequences.collatz.joint_temporal_action import (
    CollatzJointRunAction,
)
from number_compiler.sequences.collatz.physical_boundary_route import (
    exact_source_bit_length,
    has_admitted_boundary_macro,
    release_d8_rows_if_unleased,
)
from number_compiler.sequences.collatz.tape_width import (
    CollatzTapeWidthSummary,
    cycle_width_summary,
)

COLLATZ_PHYSICAL_SEMANTIC_VERSION: Final[str] = (
    "collatz-physical-source-image-v2-dyadic"
)

COLLATZ_PHYSICAL_LAW = DyadicReturnLaw(
    family="collatz-physical-source-image",
    semantic_version=COLLATZ_PHYSICAL_SEMANTIC_VERSION,
    gains=(1, 6),
    offsets=(0, 2),
    weights=(0, 1),
    cycle=DyadicReturnCycle((1, 4, 2)),
)
_TAPE_WIDTH_PORT: Final[str] = "collatz-tape-width-summary-v1"
_JOINT_COCYCLE_PORT: Final[str] = "collatz-joint-temporal-action-v1"
_BOUNDARY_MACRO_PORT: Final[str] = "collatz-first-boundary-macro-v1"
_INNOVATION_TAPE_PORT: Final[str] = SIGNED_INNOVATION_TAPE_TAG
_GLOBAL_INNOVATION_OBSERVER_TAG: Final[str] = "collatz-global-innovation-observer-v2"
_BOUNDARY_OBSERVER_TAG: Final[str] = "collatz-boundary-observer-v1"
_BoundaryMacroSnapshot = tuple[int, tuple[object, ...]]


def _boundary_macro_node_cost(
    _key: str, macro: CollatzBoundaryMacro | BorderReturnMacro
) -> int:
    """Charge the full nested structural payload and all retained integer limbs."""
    if type(macro) not in (CollatzBoundaryMacro, BorderReturnMacro):
        raise TypeError("Collatz boundary memo contains another value sort")
    return _retained_node_count(macro.structural_payload())


def _innovation_observation_node_cost(
    _key: str, observation: InnovationTapeObservation
) -> int:
    """Charge a retained immutable finite-prefix observer summary."""
    if (
        type(observation) is not InnovationTapeObservation
        or not observation.producer_issued
    ):
        raise TypeError("Collatz innovation memo contains another value sort")
    return _retained_node_count((_key, observation))


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
            or (
                root._innovation_modulus is not None
                and (
                    type(root._innovation_modulus) is not int
                    or not 3 <= root._innovation_modulus <= 4096
                    or root._innovation_modulus % 2 == 0
                    or not root._include_innovation_tape
                )
            )
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
        innovation_modulus: int | None = None,
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
        if innovation_modulus is not None and (
            type(innovation_modulus) is not int
            or not 3 <= innovation_modulus <= 4096
            or innovation_modulus % 2 == 0
            or not include_innovation_tape
        ):
            raise ValueError("complete innovation tape needs an admitted odd modulus")
        self._shared_cache = shared_cache
        self._retain_chronology = retain_chronology
        self._include_width_spine = include_width_spine
        self._include_joint_cocycle = include_joint_cocycle
        self._joint_action_snapshot: tuple[int, ...] | None = None
        self._include_innovation_tape = include_innovation_tape
        self._innovation_modulus = innovation_modulus
        self._first_boundary_macro_snapshot: _BoundaryMacroSnapshot | None = None
        self._boundary_macro_memo: (
            OwnedMemo[str, CollatzBoundaryMacro | BorderReturnMacro] | None
        ) = None
        self._innovation_observation_snapshot: tuple[object, ...] | None = None
        self._innovation_observation_memo: (
            OwnedMemo[str, InnovationTapeObservation] | None
        ) = None
        self._boundary_route_snapshot: (
            tuple[
                DyadicReturnSourceID,
                DyadicReturnActionID,
                int,
                bool,
            ]
            | None
        ) = None
        with RuntimeConstruction(ledger):
            super().__init__(ledger, seed, steps, COLLATZ_PHYSICAL_LAW)
            _register_physical_image_audit(self)

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
            _INNOVATION_TAPE_PORT,
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
    def first_boundary_macro(
        self,
    ) -> tuple[int, CollatzBoundaryMacro | BorderReturnMacro] | None:
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

    @property
    def innovation_observation(self) -> InnovationTapeObservation | None:
        """Return only the full observer attached to this exact root image."""
        if self._innovation_modulus is None:
            return None
        if not self._include_innovation_tape:
            raise ValueError("complete innovation observation was not demanded")
        view = self.scheduler._source_image_core().view(self.root_image)
        if (
            view.binding.source != self.root_source
            or view.binding.action != self.root_action
            or view.binding.extent != self.steps
        ):
            raise ValueError("Collatz innovation observation belongs to another root")
        payloads = tuple(
            port
            for port in view.binding.boundary_ports
            if type(port) is tuple
            and len(port) == 3
            and port[0] == _INNOVATION_TAPE_PORT
        )
        if not payloads:
            if (
                self._innovation_observation_snapshot is not None
                or self._retained_innovation_observation() is not None
            ):
                raise ValueError("Collatz innovation observation was not published")
            return None
        if len(payloads) != 1:
            raise ValueError("Collatz innovation publication is detached")
        port = payloads[0]
        handle, modulus = port[1], port[2]
        if (
            type(handle) is not DyadicReturnImageID
            or not _typed_equal(handle, self.root_payload)
            or type(modulus) is not int
            or modulus != self._innovation_modulus
        ):
            raise ValueError("Collatz innovation publication has another root handle")
        observation = self._retained_innovation_observation()
        if (
            type(observation) is not InnovationTapeObservation
            or not observation.producer_issued
            or not _typed_equal(
                observation.structural_payload(),
                self._innovation_observation_snapshot,
            )
            or observation.source != self.seed
            or observation.modulus != modulus
            or observation.physical_ticks != self.steps
        ):
            raise ValueError("Collatz innovation observation occurrence was altered")
        return observation

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
        occurrence: BoundaryOccurrence,
        macro: CollatzBoundaryMacro | BorderReturnMacro,
    ) -> SourceImageCandidate:
        if type(candidate) is not SourceImageCandidate:
            raise TypeError("Collatz boundary macro needs a source-image candidate")
        if not is_boundary_occurrence(occurrence):
            raise ValueError("Collatz boundary macro occurrence is malformed")
        start_tick, boundary_source, physical_ticks, identity = occurrence
        if type(macro) is BorderReturnMacro:
            validate_border_return_macro(macro)
        elif type(macro) is CollatzBoundaryMacro:
            validate_boundary_macro(macro)
        else:
            raise TypeError("Collatz boundary macro has another authority")
        if (
            macro.source != boundary_source
            or macro.physical_ticks != physical_ticks
            or macro.identity != identity
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
            with RuntimeConstruction(self.ledger):
                owner = self.ledger.register(
                    f"collatz-boundary-macro-occurrences-{self.ledger.owner_count}",
                    "query_memo",
                )
                memo = OwnedMemo(
                    self.ledger,
                    owner,
                    node_cost=_boundary_macro_node_cost,
                )
                memo["root"] = macro
            self._boundary_macro_memo = memo
        else:
            memo["root"] = macro
        self._first_boundary_macro_snapshot = payload
        return replace(
            candidate,
            boundary_ports=(*candidate.boundary_ports, (_BOUNDARY_MACRO_PORT, payload)),
        )

    def _attach_innovation_observation(
        self,
        candidate: SourceImageCandidate,
        observation: InnovationTapeObservation,
    ) -> SourceImageCandidate:
        if type(candidate) is not SourceImageCandidate:
            raise TypeError("Collatz innovation summary needs a source-image candidate")
        if (
            type(observation) is not InnovationTapeObservation
            or not observation.producer_issued
        ):
            raise TypeError("Collatz innovation summary has another authority")
        if (
            not self._include_innovation_tape
            or self._innovation_modulus != observation.modulus
            or observation.source != self.seed
            or observation.physical_ticks != self.steps
            or candidate.extent != self.steps
            or type(candidate.payload) is not DyadicReturnImageID
        ):
            raise ValueError("Collatz innovation summary differs from its root request")
        image = self.image_node(candidate.payload)
        if image.source != self.root_source or image.action != self.root_action:
            raise ValueError(
                "Collatz innovation summary is not attached to the exact root"
            )
        payload = observation.structural_payload()
        if self._innovation_observation_snapshot not in (None, payload):
            raise ValueError("conflicting Collatz innovation summaries")
        memo = self._innovation_observation_memo
        if memo is None:
            with RuntimeConstruction(self.ledger):
                owner = self.ledger.register(
                    f"collatz-innovation-observations-{self.ledger.owner_count}",
                    "query_memo",
                )
                memo = OwnedMemo(
                    self.ledger,
                    owner,
                    node_cost=_innovation_observation_node_cost,
                )
                memo["root"] = observation
            self._innovation_observation_memo = memo
        else:
            memo["root"] = observation
        self._innovation_observation_snapshot = payload
        return replace(
            candidate,
            boundary_ports=(
                *candidate.boundary_ports,
                (_INNOVATION_TAPE_PORT, candidate.payload, observation.modulus),
            ),
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
        observer_consumer: Hashable | None = None
        if (
            self._include_innovation_tape
            and source_id == self.root_source
            and action == self.root_action
        ):
            observer_consumer = (
                (_GLOBAL_INNOVATION_OBSERVER_TAG, self._innovation_modulus)
                if self._innovation_modulus is not None
                else (_BOUNDARY_OBSERVER_TAG,)
            )
        source_bits = exact_source_bit_length(admitted)
        self._bump("temporal_reuse_routing_requests")
        self._bump("temporal_reuse_routing_operand_bits", width.bit_length())
        if width <= self.MAX_LEAF_STEPS or width > 2 * source_bits:
            return self._exact_run_key(admitted, width, observer_consumer)
        from number_compiler.arithmetic.fields.two_adic import v2_positive
        from number_compiler.hashlife.execution.dyadic_return_runs import (
            RunArithmeticWorkspace,
        )

        # Homogeneity depends on the admitted low cylinder, including 0/1 cases.
        scratch = RunArithmeticWorkspace.for_ledger(self.ledger, "collatz_physical")
        with scratch.scope():
            scratch.require_bits(
                8 * (admitted.residue.bit_length() + 4 * width.bit_length() + 32)
            )
            self._bump(
                "temporal_reuse_routing_operand_bits", admitted.residue.bit_length() + 1
            )
            boundary_plan = has_admitted_boundary_macro(
                admitted,
                width,
                include_innovation_tape=self._include_innovation_tape,
                include_joint_cocycle=self._include_joint_cocycle,
                allow_border_return=source_id == self.root_source,
                ledger=self.ledger,
                scratch=scratch,
            )
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
        self, source: _SourceNode, width: int, consumer: Hashable | None = None
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
            (self._include_joint_cocycle or self._include_innovation_tape)
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
        is_root_action = source_id == self.root_source and action == self.root_action
        from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer
        from number_compiler.arithmetic.fields.two_adic import v2_positive
        from number_compiler.hashlife.execution.dyadic_return_runs import (
            RunArithmeticWorkspace,
            publish_exact_run_candidate,
        )
        from number_compiler.sequences.collatz.temporal_mixed_execution import (
            MixedRouteNotAdmitted,
        )
        from number_compiler.sequences.collatz.temporal_run_quotient import (
            compile_collatz_temporal_run_quotient,
        )

        # Choose before discovery; wide high-entropy sources retain balanced
        # source-cylinder substitution rather than unbounded direct runs.
        source_bits = exact_source_bit_length(admitted)
        boundary_route: bool | None = None
        require_mixed_prefix = False
        scratch = RunArithmeticWorkspace.for_ledger(self.ledger, "collatz_physical")
        if self.MAX_LEAF_STEPS < width <= 2 * source_bits:
            boundary_route = self._take_boundary_route_snapshot(
                source_id, action, width
            )
            if boundary_route is None:
                with scratch.scope():
                    boundary_route = has_admitted_boundary_macro(
                        admitted,
                        width,
                        include_innovation_tape=self._include_innovation_tape,
                        include_joint_cocycle=self._include_joint_cocycle,
                        allow_border_return=source_id == self.root_source,
                        ledger=self.ledger,
                        scratch=scratch,
                    )
        with scratch.scope():
            self._bump("temporal_routing_operand_bits", width.bit_length())
            if self.MAX_LEAF_STEPS < width <= 2 * source_bits:
                # Decide homogeneity from the low cylinder before assembling
                # its high lift; mixed cylinders never use that integer.
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
                    require_mixed_prefix = (
                        width >= 16 and source_bits >= 64 and is_root_action
                    )
                    if not require_mixed_prefix:
                        self._bump("temporal_balanced_routes")
                        return None
            scratch.require_bits(8 * (source_bits + width.bit_length() + 16))
            self._bump("temporal_routing_operand_bits", source_bits)
            if is_root_action:
                # The pinned root is exact; rebuilding its lift only to route
                # would materialize an equivalent wide integer.
                source_value = self.seed
            else:
                source_value = self._source_value(admitted)
        demand_width = self._include_width_spine and is_root_action
        demand_joint = self._include_joint_cocycle and is_root_action
        demand_innovation = self._include_innovation_tape and is_root_action
        try:
            quotient = compile_collatz_temporal_run_quotient(
                source_value,
                width,
                ledger=self.ledger,
                shared_cache=self._shared_cache,
                include_width_spine=demand_width,
                include_joint_cocycle=demand_joint,
                include_innovation_tape=demand_innovation,
                require_mixed_prefix=require_mixed_prefix,
                innovation_modulus=(
                    self._innovation_modulus if demand_innovation else None
                ),
            )
        except MixedRouteNotAdmitted:
            self._bump("temporal_balanced_routes")
            return None
        self._bump("temporal_run_routes")
        cycle = None
        if quotient.cycle_repetitions:
            # Recover the known state-1 tail from clock and cycle phase; no
            # trajectory discovery is needed for optional audits.
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
        # This exact source admits constant transfer without a retained prefix.
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
        if quotient.innovation_observation is not None:
            candidate = self._attach_innovation_observation(
                candidate, quotient.innovation_observation
            )
        return candidate

    def segments(self) -> Iterator[tuple[int, int, int]]:
        return self.branch_segments()

    def _retained_boundary_macro(
        self,
    ) -> CollatzBoundaryMacro | BorderReturnMacro | None:
        memo = self._boundary_macro_memo
        if memo is None:
            return None
        return memo.get("root")

    def _retained_innovation_observation(self) -> InnovationTapeObservation | None:
        memo = self._innovation_observation_memo
        if memo is None:
            return None
        return memo.get("root")

    def _release_boundary_macro_state(self) -> None:
        memo = self._boundary_macro_memo
        if memo is not None:
            memo.dispose()
        self._boundary_macro_memo = None
        self._first_boundary_macro_snapshot = None
        self._boundary_route_snapshot = None

    def _release_innovation_observation_state(self) -> None:
        memo = self._innovation_observation_memo
        if memo is not None:
            memo.dispose()
        self._innovation_observation_memo = None
        self._innovation_observation_snapshot = None

    def _release_d8_temporal_rows(self) -> None:
        release_d8_rows_if_unleased(self.ledger, CollatzPhysicalImageWorkspace)

    def _cleanup_all_states(self, *, include_base: bool) -> None:
        base_cleanup = (super()._rollback_construction,) if include_base else ()
        cleanup_all(
            (
                *base_cleanup,
                self._release_boundary_macro_state,
                self._release_innovation_observation_state,
                self._release_d8_temporal_rows,
            )
        )

    def _rollback_construction(self) -> None:
        self._cleanup_all_states(include_base=True)

    def dispose(self) -> None:
        self._cleanup_all_states(include_base=not self._closed)


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
