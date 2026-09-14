"""Domain-neutral exact binary self-branching dispatcher.

Several compiler domains have the same control shape: the current semantic
state must derive one binary branch itself, with optional fail-closed outcomes
for a natural gcd split or an unavailable discriminator.  The arithmetic
payload of the branches remains domain-specific.

This module deliberately stores no supplied branch itinerary.  A caller first
constructs :class:`BinaryBranchDecision` from its current state, then dispatches
through :class:`BinaryPiecewiseHandler`.  The handler executes exactly one
branch callback.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import TypeVar

T = TypeVar("T")
_VALID_KINDS = frozenset({"ZERO", "ONE", "SPLIT", "UNKNOWN"})


@dataclass(frozen=True, slots=True)
class BinaryBranchDecision:
    """One self-derived binary branch decision.

    ``ZERO`` and ``ONE`` are the two ordinary branches.  ``SPLIT`` carries a
    natural nontrivial gcd packet.  ``UNKNOWN`` is fail-closed and must not be
    converted to either ordinary branch by the dispatcher.
    """

    kind: str
    method: str
    gcd_packet: int | None = None
    candidate_derived: bool = True

    def __post_init__(self) -> None:
        kind = str(self.kind).upper()
        object.__setattr__(self, "kind", kind)
        if kind not in _VALID_KINDS:
            raise ValueError(kind)
        if not self.method:
            raise ValueError("binary branch decision requires a method")
        if kind == "SPLIT":
            if self.gcd_packet is None or int(self.gcd_packet) <= 1:
                raise ValueError(self.gcd_packet)
            object.__setattr__(self, "gcd_packet", int(self.gcd_packet))
        elif self.gcd_packet is not None:
            raise ValueError((kind, self.gcd_packet))

    @classmethod
    def zero(
        cls, method: str, *, candidate_derived: bool = True
    ) -> BinaryBranchDecision:
        return cls("ZERO", method, candidate_derived=candidate_derived)

    @classmethod
    def one(
        cls, method: str, *, candidate_derived: bool = True
    ) -> BinaryBranchDecision:
        return cls("ONE", method, candidate_derived=candidate_derived)

    @classmethod
    def split(
        cls,
        method: str,
        gcd_packet: int,
        *,
        candidate_derived: bool = True,
    ) -> BinaryBranchDecision:
        return cls("SPLIT", method, int(gcd_packet), candidate_derived)

    @classmethod
    def unknown(
        cls,
        method: str,
        *,
        candidate_derived: bool = True,
    ) -> BinaryBranchDecision:
        return cls("UNKNOWN", method, candidate_derived=candidate_derived)

    @property
    def is_binary(self) -> bool:
        return self.kind in ("ZERO", "ONE")


@dataclass(frozen=True, slots=True)
class BinaryPiecewiseHandler:
    """Shared exact control skeleton for self-branching binary morphisms.

    The handler has no branch-discovery logic and no domain arithmetic.  It
    simply enforces that exactly the callback corresponding to a previously
    derived decision executes.  This prevents branch provenance/itineraries
    from becoming semantic state while allowing Collatz and Frobenius section
    machines to share one control implementation.
    """

    domain: str

    def __post_init__(self) -> None:
        if not str(self.domain):
            raise ValueError("binary handler domain must be nonempty")
        object.__setattr__(self, "domain", str(self.domain))

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("binary-piecewise-handler", self.domain)

    def dispatch(
        self,
        decision: BinaryBranchDecision,
        *,
        zero_branch: Callable[[BinaryBranchDecision], T],
        one_branch: Callable[[BinaryBranchDecision], T],
        split_branch: Callable[[BinaryBranchDecision], T],
        unknown_branch: Callable[[BinaryBranchDecision], T],
    ) -> T:
        if not isinstance(decision, BinaryBranchDecision):
            raise TypeError(type(decision))
        if decision.kind == "ZERO":
            return zero_branch(decision)
        if decision.kind == "ONE":
            return one_branch(decision)
        if decision.kind == "SPLIT":
            return split_branch(decision)
        if decision.kind == "UNKNOWN":
            return unknown_branch(decision)
        raise AssertionError(decision.kind)


__all__ = ["BinaryBranchDecision", "BinaryPiecewiseHandler"]
