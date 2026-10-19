"""Immutable identities and packets for fresh-prime successor actions."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Final

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle

PRIME_SUCCESSOR_ACTION_TAG: Final[str] = "prime-successor-action-v1"
PRIME_SUCCESSOR_WHEEL_VERSION: Final[str] = "successor-wheel-v2"


@dataclass(frozen=True, slots=True)
class PrimeSuccessorActionDescriptor:
    parent_factors: tuple[int, ...]
    parent_period: int
    fresh_prime: int
    forbidden_residues: tuple[int, ...]

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            PRIME_SUCCESSOR_ACTION_TAG,
            self.parent_factors,
            self.parent_period,
            self.fresh_prime,
            self.forbidden_residues,
        )


@dataclass(frozen=True, slots=True)
class PrimeSuccessorActionID(ArenaHandle):
    """Arena-scoped action identity; foreign integer IDs cannot alias."""


@dataclass(frozen=True, slots=True)
class PrimeSuccessorDescriptorID(ArenaHandle):
    """Small source authority for an arena-interned parent descriptor."""


@dataclass(frozen=True, slots=True)
class PrimeSuccessorActionNode:
    copies: int
    width: int
    phase_shift: int
    before: PrimeSuccessorActionID | None
    after: PrimeSuccessorActionID | None

    @property
    def primitive(self) -> bool:
        return self.width > 0 and self.before is None and self.after is None

    @property
    def identity(self) -> bool:
        return self.width == 0


@dataclass(frozen=True, slots=True)
class PrimeSuccessorPortEffect:
    entering_phase: int
    outgoing_phase: int
    parent_survivors: int
    deleted_survivors: int
    surviving_values: int


@dataclass(frozen=True, slots=True)
class PrimeSuccessorActionMetrics:
    action_nodes: int
    composition_entries: int
    demanded_ports: int
    progression_states: int
    work: int
    retained_entries: int
    retained_nodes: int
    parent_gap_positions_materialized: int = 0


@dataclass(frozen=True, slots=True)
class PrimeSuccessorSource:
    descriptor: PrimeSuccessorDescriptorID
    entering_phase: int


@dataclass(frozen=True, slots=True)
class PrimeSuccessorImagePayload:
    descriptor: PrimeSuccessorDescriptorID
    action: PrimeSuccessorActionID
    entering_phase: int
    outgoing_phase: int
    parent_survivors: int
    deleted_survivors: int
    surviving_values: int


@dataclass(frozen=True, slots=True)
class PrimeSuccessorActionAuditSnapshot:
    """Fresh, immutable view for the prime payload-authority audit."""

    ledger: object
    rank: object
    rank_ledger: object
    factor_source: object
    rank_authority: object
    descriptor: object
    descriptor_authority: object
    parent_depth: object
    admitted_successor: object
    descriptor_id: object
    closed: object
    stores_valid: bool
    node_owner: int
    normal_form_owner: int
    port_owner: int
    nodes: tuple[tuple[int, PrimeSuccessorActionNode], ...]
    normal_forms: tuple[tuple[int, PrimeSuccessorActionID], ...]
    ports: tuple[
        tuple[tuple[PrimeSuccessorActionID, int], PrimeSuccessorPortEffect], ...
    ]
    next_node: object
    identity: object
    base: object


__all__ = [
    "PRIME_SUCCESSOR_ACTION_TAG",
    "PRIME_SUCCESSOR_WHEEL_VERSION",
    "PrimeSuccessorActionAuditSnapshot",
    "PrimeSuccessorActionDescriptor",
    "PrimeSuccessorActionID",
    "PrimeSuccessorActionMetrics",
    "PrimeSuccessorActionNode",
    "PrimeSuccessorDescriptorID",
    "PrimeSuccessorImagePayload",
    "PrimeSuccessorPortEffect",
    "PrimeSuccessorSource",
]
