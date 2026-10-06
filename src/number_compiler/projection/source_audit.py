"""Explicit source interface for auditing retained radix projections."""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import MutableMapping
from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.scoped_handles import ExactSource

if TYPE_CHECKING:
    from number_compiler.projection.lazy_radix import RadixProjection
    from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class RadixProjectionAuditSource:
    """Read-only view of one original source and its retained consumers."""

    owner: RadixProjectionSourceAuditor
    source: ExactSource
    steps: int
    seed_digits: tuple[int, ...]
    projections: MutableMapping[int, RadixProjection]


class RadixProjectionSourceAuditor(ABC):
    """A family supplies its exact source authority without shared imports."""

    __slots__ = ()

    @abstractmethod
    def radix_projection_audit_source(
        self, ledger: ResourceLedger
    ) -> RadixProjectionAuditSource | None:
        """Return metadata only for this family's live, exact source owner."""


def checked_projection_audit_source(
    owner: RadixProjectionSourceAuditor, ledger: ResourceLedger
) -> RadixProjectionAuditSource | None:
    """Reject copied or malformed views before they can authorize a projection."""
    view = owner.radix_projection_audit_source(ledger)
    if view is None:
        return None
    if (
        type(view) is not RadixProjectionAuditSource
        or view.owner is not owner
        or type(view.source) is not ExactSource
        or type(view.steps) is not int
        or view.steps < 0
        or type(view.seed_digits) is not tuple
        or any(type(digit) is not int for digit in view.seed_digits)
        or view.seed_digits != view.source.digits
    ):
        raise ValueError("radix projection audit source is not bound to its owner")
    return view
