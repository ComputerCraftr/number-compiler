"""Typed publication of Collatz source-image observation ports."""

from __future__ import annotations

from dataclasses import replace
from typing import TYPE_CHECKING, Final

from number_compiler.hashlife.execution.dyadic_return_images import (
    DyadicReturnActionID,
    DyadicReturnImageID,
    DyadicReturnSourceID,
    _ImageNode,
)
from number_compiler.hashlife.execution.source_bound_images import SourceImageCandidate
from number_compiler.resources.construction_scope import RuntimeConstruction
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.sequences.collatz.border_identity import (
    BoundaryOccurrence,
    BoundaryOccurrenceProducerStamp,
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
from number_compiler.sequences.collatz.tape_width import CollatzTapeWidthSummary

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.temporal_source_morphism import (
        PointedCollatzSource,
    )

_TAPE_WIDTH_PORT: Final[str] = "collatz-tape-width-summary-v1"
_JOINT_COCYCLE_PORT: Final[str] = "collatz-joint-temporal-action-v1"
_BOUNDARY_MACRO_PORT: Final[str] = "collatz-first-boundary-macro-v1"
_INNOVATION_TAPE_PORT = SIGNED_INNOVATION_TAPE_TAG


def _boundary_macro_node_cost(
    _key: str, macro: CollatzBoundaryMacro | BorderReturnMacro
) -> int:
    """Charge nested boundary structure and all retained integer limbs."""
    if type(macro) not in (CollatzBoundaryMacro, BorderReturnMacro):
        raise TypeError("Collatz boundary memo contains another value sort")
    return _retained_node_count(macro.structural_payload())


def _innovation_observation_node_cost(
    _key: str, observation: InnovationTapeObservation
) -> int:
    """Charge an immutable finite-prefix observer summary."""
    if (
        type(observation) is not InnovationTapeObservation
        or not observation.producer_issued
    ):
        raise TypeError("Collatz innovation memo contains another value sort")
    return _retained_node_count((_key, observation))


class CollatzPhysicalImagePublication:
    """Mixin for publishing typed, source-bound image observation ports."""

    ledger: ResourceLedger
    seed: int
    steps: int
    root_source: DyadicReturnSourceID
    root_action: DyadicReturnActionID
    _include_joint_cocycle: bool
    _joint_action_snapshot: tuple[int, ...] | None
    _include_innovation_tape: bool
    _innovation_modulus: int | None
    _first_boundary_macro_snapshot: tuple[int, tuple[object, ...]] | None
    _boundary_macro_memo: (
        OwnedMemo[str, CollatzBoundaryMacro | BorderReturnMacro] | None
    )
    _innovation_observation_snapshot: tuple[object, ...] | None
    _innovation_observation_memo: OwnedMemo[str, InnovationTapeObservation] | None
    _root_source_owner: PointedCollatzSource | None

    def image_node(self, image: DyadicReturnImageID) -> _ImageNode:
        raise NotImplementedError

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
        producer_stamp: BoundaryOccurrenceProducerStamp,
        macro: CollatzBoundaryMacro | BorderReturnMacro,
    ) -> SourceImageCandidate:
        if type(candidate) is not SourceImageCandidate:
            raise TypeError("Collatz boundary macro needs a source-image candidate")
        if not is_boundary_occurrence(occurrence):
            raise ValueError("Collatz boundary macro occurrence is malformed")
        if type(
            producer_stamp
        ) is not BoundaryOccurrenceProducerStamp or not producer_stamp.certifies(
            self.seed, self.steps, occurrence, macro
        ):
            raise ValueError("Collatz boundary occurrence lacks producer authority")
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
