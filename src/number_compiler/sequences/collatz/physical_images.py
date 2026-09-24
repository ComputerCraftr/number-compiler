"""Collatz adapter for the shared dyadic return source-image engine."""

from __future__ import annotations

from collections.abc import Iterator

from number_compiler.hashlife.execution.dyadic_return_images import (
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

COLLATZ_PHYSICAL_LAW = DyadicReturnLaw(
    family="collatz-physical-source-image",
    semantic_version="collatz-physical-source-image-v2-dyadic",
    gains=(1, 6),
    offsets=(0, 2),
    weights=(0, 1),
    cycle=DyadicReturnCycle((1, 4, 2)),
)


class CollatzPhysicalImageWorkspace(DyadicReturnImageWorkspace):
    """Fixed physical Collatz steps using the shared dyadic law engine."""

    def __init__(
        self,
        ledger: ResourceLedger,
        seed: int,
        steps: int,
        *,
        retain_chronology: bool = True,
    ) -> None:
        if type(retain_chronology) is not bool:
            raise TypeError("Collatz chronology choice must be Boolean")
        self._retain_chronology = retain_chronology
        super().__init__(ledger, seed, steps, COLLATZ_PHYSICAL_LAW)

    def retain_chronological_support(self) -> bool:
        return self._retain_chronology

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
        if type(action) is not DyadicReturnActionID:
            raise TypeError("Collatz composite requires its action ID")
        if self.action_node(action).children is None:
            return None
        return self.complete_composite_candidate(action, source)

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
