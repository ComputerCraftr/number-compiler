"""Immutable borrowed views for explicit higher-summary payload audits."""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.actions.field_actions import FieldCellActionID

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.higher_semantic import (
        HigherSemanticArena,
    )
    from number_compiler.hashlife.execution.continuations.higher_summary_records import (
        ContextBinding,
        HigherSummaryID,
        SummaryRecord,
        UnaryBinding,
    )
    from number_compiler.hashlife.execution.continuations.higher_types import (
        HigherActionSchema,
    )
    from number_compiler.hashlife.execution.field_images import SourceCellArena
    from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class HigherSummaryAuditSnapshot:
    """Read-only views and exact stores retained by one summary arena."""

    ledger: ResourceLedger
    owner: ArenaToken
    semantics: HigherSemanticArena
    sources: SourceCellArena
    schema: HigherActionSchema
    node_owner: int
    node_store: object
    nodes: Sequence[SummaryRecord]
    key_owner: int
    key_store: object
    keys: Mapping[SummaryRecord, int]
    binding_owner: int
    binding_store: object
    bindings: Mapping[UnaryBinding | ContextBinding, HigherSummaryID]
    runtime_binding_owner: int
    runtime_binding_store: object
    runtime_bindings: Mapping[UnaryBinding | ContextBinding, HigherSummaryID]
    blank_identity_owner: int
    blank_identity_store: object
    blank_identities: Mapping[tuple[FieldCellActionID, int], bool]
    runtime_composition_owner: int
    runtime_composition_store: object
    runtime_compositions: Mapping[
        tuple[HigherSummaryID, HigherSummaryID], HigherSummaryID
    ]


__all__ = ["HigherSummaryAuditSnapshot"]
