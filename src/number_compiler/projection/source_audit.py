"""Explicit source interface for auditing retained radix projections."""

from __future__ import annotations

from abc import ABC, abstractmethod
from collections.abc import MutableMapping
from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from number_compiler.projection.lazy_radix import RadixProjection


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

    @property
    def resource_ledger(self) -> ResourceLedger:
        """Expose the ledger that owns this audited source's projections."""
        ledger = getattr(self, "_ledger", None)
        if type(ledger) is not ResourceLedger:
            raise TypeError("radix projection source has no owned resource ledger")
        return ledger

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
