"""Immutable output-handle shape and its issue-time metadata binding."""

from __future__ import annotations

from dataclasses import dataclass, field

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken


@dataclass(frozen=True, slots=True)
class ReversePairOutputOccurrence:
    """Exact target pair grammar issued by one request-local output owner."""

    owner: ArenaToken
    root: int
    temporal_steps: int
    pair_width: int
    output_width: int
    growth: int
    q19_domain: int
    q19_f9: int
    _publication_binding: tuple[object, ...] | None = field(
        init=False, default=None, repr=False, compare=False
    )

    def __post_init__(self) -> None:
        if type(self.owner) is not ArenaToken:
            raise TypeError("pair output occurrence needs a scoped owner")
        if any(
            type(value) is not int
            for value in (
                self.root,
                self.temporal_steps,
                self.pair_width,
                self.output_width,
                self.growth,
                self.q19_domain,
                self.q19_f9,
            )
        ):
            raise TypeError("pair output metadata must use exact integers")
        if (
            self.root < 0
            or self.temporal_steps < 1
            or self.pair_width < 1
            or self.output_width < self.pair_width
            or self.growth < 0
            or self.q19_domain not in (-1, 0, 1)
            or not 0 <= self.q19_f9 < 9
        ):
            raise ValueError("invalid pair output occurrence metadata")

    @property
    def publication_binding(self) -> tuple[object, ...] | None:
        """Read the snapshot attached when this exact handle was published."""
        return self._publication_binding

    def bind_publication(self, snapshot: tuple[object, ...]) -> None:
        """Attach the canonical issue-time snapshot once, rejecting rebinding."""
        if type(snapshot) is not tuple or snapshot != occurrence_publication_snapshot(
            self
        ):
            raise ValueError("Q19 publication snapshot does not match this occurrence")
        current = self._publication_binding
        if current is not None and current != snapshot:
            raise ValueError("Q19 occurrence is already bound to another publication")
        object.__setattr__(self, "_publication_binding", snapshot)


def occurrence_publication_snapshot(
    occurrence: ReversePairOutputOccurrence,
) -> tuple[object, ...]:
    """Snapshot the exact owner and scalar fields retained when an occurrence issues."""
    return (
        occurrence.owner,
        occurrence.root,
        occurrence.temporal_steps,
        occurrence.pair_width,
        occurrence.output_width,
        occurrence.growth,
        occurrence.q19_domain,
        occurrence.q19_f9,
    )


__all__ = ["ReversePairOutputOccurrence", "occurrence_publication_snapshot"]
