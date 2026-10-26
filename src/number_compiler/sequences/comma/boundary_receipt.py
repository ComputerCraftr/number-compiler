"""Authenticated source and result contracts for comma boundary returns."""

from __future__ import annotations

from collections.abc import Hashable, Mapping, Sequence
from dataclasses import dataclass
from typing import TYPE_CHECKING, Final, TypeVar

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.hashlife.execution.source_image_inventory import SourceImageID
from number_compiler.sequences.comma.action_arena import (
    CommaActionArena,
    CommaActionArenaAuditSnapshot,
    CommaActionRecord,
)
from number_compiler.sequences.comma.arithmetic import decimal_sector
from number_compiler.sequences.comma.boundary_quotient import (
    PERIOD,
    BoundaryState,
    MacroTemplate,
    boundary_state_signature,
)

if TYPE_CHECKING:
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.resources.stores import LedgerDict, LedgerList
    from number_compiler.sequences.comma.future_provider import (
        SemanticFutureProvider,
        SemanticFutureProviderLease,
        UnrankedChildSelection,
    )
    from number_compiler.sequences.comma.power import CommaTerm
    from number_compiler.sequences.comma.semantic_branch import SemanticMacroChild

SOURCE: Final[int] = 20
_OccurrenceRecord = TypeVar("_OccurrenceRecord")
_BOUNDARY_SELECTION_RECEIPT_SEAL = object()


@dataclass(frozen=True, slots=True)
class BoundarySelectionReceiptID(ArenaHandle):
    """Term-owned reference to one issued selection receipt."""


def issue_boundary_selection_receipt_entry(
    ledger: ResourceLedger,
    receipt: BoundarySelectionReceipt,
    token: ArenaToken,
    kind: str,
    local_id: int,
    receipts: LedgerDict[BoundarySelectionReceiptID, BoundarySelectionReceipt],
    seals: LedgerDict[BoundarySelectionReceiptID, BoundarySelectionReceipt],
    receipt_owner: int,
    seal_owner: int,
) -> BoundarySelectionReceiptID:
    """Store one exact receipt/seal pair and return its owner-bound handle."""
    if type(receipt) is not BoundarySelectionReceipt:
        raise TypeError("comma receipt issuance requires its exact receipt sort")
    receipt.validate_shape()
    identifier = BoundarySelectionReceiptID(token, kind, local_id)
    ledger.reserve_many(((receipt_owner, 1, 1), (seal_owner, 1, 1)))
    try:
        receipts[identifier] = receipt
        seals[identifier] = receipt
    except BaseException as error:
        try:
            rollback_boundary_selection_receipt_entry(
                ledger,
                identifier,
                receipt,
                receipts,
                seals,
                receipt_owner,
                seal_owner,
            )
        except BaseException as rollback_error:
            raise rollback_error from error
        raise
    return identifier


def resolve_boundary_selection_receipt_entry(
    identifier: BoundarySelectionReceiptID,
    token: ArenaToken,
    kind: str,
    receipts: LedgerDict[BoundarySelectionReceiptID, BoundarySelectionReceipt],
    seals: LedgerDict[BoundarySelectionReceiptID, BoundarySelectionReceipt],
) -> BoundarySelectionReceipt:
    """Resolve and validate one receipt without exposing the owning term."""
    if type(identifier) is not BoundarySelectionReceiptID:
        raise TypeError("comma cursor requires a boundary receipt handle")
    identifier.validate(token, kind)
    try:
        receipt = receipts[identifier]
        seal = seals[identifier]
    except KeyError as exc:
        raise ValueError("comma boundary receipt is foreign or stale") from exc
    if type(receipt) is not BoundarySelectionReceipt or seal is not receipt:
        raise ValueError("comma boundary receipt lost its publication seal")
    receipt.validate_shape()
    return receipt


@dataclass(frozen=True, slots=True, eq=False, init=False)
class BoundarySelectionReceipt:
    """Small issued selection binding retained with one returned occurrence."""

    selection: UnrankedChildSelection
    artifact_sha256: str
    source_state: BoundaryState
    source_exponent: int
    source_value: int
    source_index: int
    source_extent: int
    target_state: BoundaryState
    target_exponent: int
    target_value: int
    transitions: int
    _selection_binding: UnrankedChildSelection
    _snapshot: tuple[object, ...]
    _seal: object

    def __init__(
        self,
        selection: UnrankedChildSelection,
        artifact_sha256: str,
        source_state: BoundaryState,
        source_exponent: int,
        source_value: int,
        source_index: int,
        source_extent: int,
        target_state: BoundaryState,
        target_exponent: int,
        target_value: int,
        transitions: int,
        *,
        _seal: object,
    ) -> None:
        if _seal is not _BOUNDARY_SELECTION_RECEIPT_SEAL:
            raise TypeError("use a checked semantic selection to issue a receipt")
        for name, value in (
            ("selection", selection),
            ("artifact_sha256", artifact_sha256),
            ("source_state", source_state),
            ("source_exponent", source_exponent),
            ("source_value", source_value),
            ("source_index", source_index),
            ("source_extent", source_extent),
            ("target_state", target_state),
            ("target_exponent", target_exponent),
            ("target_value", target_value),
            ("transitions", transitions),
        ):
            object.__setattr__(self, name, value)
        object.__setattr__(self, "_selection_binding", selection)
        object.__setattr__(self, "_snapshot", self._current_snapshot())
        object.__setattr__(self, "_seal", _seal)
        self.validate_shape()

    def _current_snapshot(self) -> tuple[object, ...]:
        return (
            self.selection.source_class,
            self.selection.fork_coefficient,
            self.selection.ordered_child_classes,
            self.selection.selected_slot,
            self.artifact_sha256,
            boundary_state_signature(self.source_state),
            self.source_exponent,
            self.source_value,
            self.source_index,
            self.source_extent,
            boundary_state_signature(self.target_state),
            self.target_exponent,
            self.target_value,
            self.transitions,
        )

    def validate_shape(self) -> None:
        from number_compiler.sequences.comma.future_authority import (
            valid_artifact_digest,
        )
        from number_compiler.sequences.comma.future_provider import (
            UnrankedChildSelection,
        )

        if (
            self._seal is not _BOUNDARY_SELECTION_RECEIPT_SEAL
            or type(self.selection) is not UnrankedChildSelection
            or self._selection_binding is not self.selection
            or not self.selection.is_issued()
            or not valid_artifact_digest(self.artifact_sha256)
            or type(self.source_state) is not BoundaryState
            or type(self.target_state) is not BoundaryState
            or any(
                type(value) is not int
                for value in (
                    self.source_exponent,
                    self.source_value,
                    self.source_index,
                    self.source_extent,
                    self.target_exponent,
                    self.target_value,
                    self.transitions,
                )
            )
            or self.source_exponent < 5
            or self.source_value < SOURCE
            or self.source_index < 1
            or self.source_extent < 0
            or self.target_exponent < 5
            or self.target_value < SOURCE
            or self.transitions < 1
            or getattr(self, "_snapshot", None) != self._current_snapshot()
        ):
            raise ValueError("comma boundary selection receipt was altered")
        if (
            self.selection.source != self.source_state
            or self.source_exponent % PERIOD != self.source_state.exponent_residue
            or self.target_exponent % PERIOD != self.target_state.exponent_residue
        ):
            raise ValueError("comma selection receipt has another source phase")

    def validate_provider(self, provider: object) -> None:
        from number_compiler.sequences.comma.future_provider import (
            SemanticFutureProvider,
            SemanticFutureProviderLease,
        )

        self.validate_shape()
        if type(provider) is SemanticFutureProvider:
            checked_provider: SemanticFutureProvider | SemanticFutureProviderLease = (
                provider
            )
        elif type(provider) is SemanticFutureProviderLease:
            checked_provider = provider
        else:
            raise PermissionError("comma selection receipt belongs to another provider")
        if not self.selection.matches_provider(checked_provider):
            raise PermissionError("comma selection receipt belongs to another provider")
        checked_provider.require_global_release_admission()
        if self.artifact_sha256 != checked_provider.artifact_sha256:
            raise PermissionError("comma selection receipt belongs to another artifact")

    def validate_source(
        self,
        *,
        source_state: BoundaryState,
        source_exponent: int,
        source_value: int,
        source_index: int,
        source_extent: int,
    ) -> None:
        self.validate_shape()
        if (
            source_state != self.source_state
            or source_exponent != self.source_exponent
            or source_value != self.source_value
            or source_index != self.source_index
            or source_extent != self.source_extent
        ):
            raise ValueError("comma selection receipt belongs to another source seam")

    def validate_output(
        self,
        *,
        value: int,
        absolute_index: int,
        cursor: BoundaryPrefixCursor,
        receipt_id: BoundarySelectionReceiptID,
    ) -> None:
        self.validate_shape()
        if (
            type(cursor) is not BoundaryPrefixCursor
            or type(receipt_id) is not BoundarySelectionReceiptID
            or cursor.selection_receipt != receipt_id
            or cursor.state != self.target_state
            or cursor.exponent != self.target_exponent
            or cursor.transitions != 0
            or value != self.target_value
            or absolute_index != self.source_index + self.transitions
        ):
            raise ValueError("comma selected output differs from its issued receipt")

    @classmethod
    def from_semantic_child(
        cls,
        selected: SemanticMacroChild,
        provider: SemanticFutureProvider | SemanticFutureProviderLease,
        *,
        source_value: int,
        source_index: int,
        source_extent: int,
    ) -> BoundarySelectionReceipt:
        from number_compiler.sequences.comma.future_provider import (
            SemanticFutureProvider,
            SemanticFutureProviderLease,
        )
        from number_compiler.sequences.comma.semantic_branch import (
            SemanticMacroChild,
        )

        if type(selected) is not SemanticMacroChild or type(provider) not in (
            SemanticFutureProvider,
            SemanticFutureProviderLease,
        ):
            raise TypeError("comma selection receipt needs its exact issued child")
        selected.validate()
        provider.require_global_release_admission()
        if not selected.selection.matches_provider(provider):
            raise PermissionError("comma selection belongs to another provider")
        source = selected.source
        target = selected.target
        if (
            type(source_value) is not int
            or type(source_index) is not int
            or type(source_extent) is not int
            or source_extent < 0
            or source.state != selected.selection.source
            or selected.selection.fork_coefficient
            != selected.prefix.template.destination_a
        ):
            raise ValueError("comma selected child has another source binding")
        return cls(
            selected.selection,
            provider.artifact_sha256,
            source.state,
            source.exponent,
            source_value,
            source_index,
            source_extent,
            target.state,
            target.exponent,
            selected.literal_value,
            selected.total_transition_count,
            _seal=_BOUNDARY_SELECTION_RECEIPT_SEAL,
        )


@dataclass(frozen=True, slots=True)
class BoundaryPrefixCursor:
    """Fixed-size occurrence cursor for one exact boundary prefix."""

    state: BoundaryState
    exponent: int
    transitions: int
    selection_receipt: BoundarySelectionReceiptID | None = None


@dataclass(frozen=True, slots=True)
class CommaImagePayload:
    value: int
    absolute_index: int
    certificate_version: str = "uncertified-arithmetic"
    boundary_cursor: BoundaryPrefixCursor | None = None


@dataclass(frozen=True, slots=True)
class CommaOccurrenceRecord:
    """Term-owned source-image occurrence and its exact boundary cursor."""

    image: SourceImageID
    value: int
    absolute_index: int
    certificate_version: str
    boundary_cursor: BoundaryPrefixCursor | None = None


@dataclass(frozen=True, slots=True)
class CommaTermPayloadAuditSnapshot:
    """Read-only occurrence and action payload views owned by one term."""

    arena: CommaActionArenaAuditSnapshot
    occurrence_token: ArenaToken
    occurrence_kind: str
    occurrence_owner: int
    occurrence_seal_owner: int
    occurrences: Sequence[CommaOccurrenceRecord]
    occurrence_seals: Sequence[CommaOccurrenceRecord]
    boundary_receipt_token: ArenaToken
    boundary_receipt_kind: str
    boundary_receipt_owner: int
    boundary_receipt_seal_owner: int
    boundary_receipts: Mapping[BoundarySelectionReceiptID, BoundarySelectionReceipt]
    boundary_receipt_seals: Mapping[
        BoundarySelectionReceiptID, BoundarySelectionReceipt
    ]
    stores_owned: bool


def validate_action_result(
    arena: CommaActionArena,
    owner: CommaTerm | None,
    action: CommaActionRecord,
    source_payload: CommaImagePayload,
    source_extent: int,
    result_payload: CommaImagePayload,
    result_extent: int,
    result_ports: tuple[Hashable, ...],
    *,
    expected_transitions: int | None = None,
    template: MacroTemplate | None = None,
) -> None:
    """Validate selected boundary output before image publication or reuse."""
    if owner is None:
        raise ValueError("comma action result has no source owner")
    if action.kind == "source20-first-child":
        from number_compiler.sequences.comma.future_authority import (
            SOURCE20_FIRST_FORK_INDEX,
            SOURCE20_FIRST_FORK_VALUE,
            SOURCE20_SELECTED_CHILD,
        )

        provider = owner.require_global_future_provider(action.future_digest)
        cursor = result_payload.boundary_cursor
        if (
            source_payload.absolute_index != SOURCE20_FIRST_FORK_INDEX
            or source_payload.value != SOURCE20_FIRST_FORK_VALUE
            or source_payload.boundary_cursor is not None
            or type(cursor) is not BoundaryPrefixCursor
            or cursor.selection_receipt is not None
            or cursor.state != BoundaryState("N", 2, 10)
            or cursor.exponent != 10
            or cursor.transitions != 0
            or result_payload.value != SOURCE20_SELECTED_CHILD
            or result_payload.absolute_index != source_payload.absolute_index + 1
            or result_extent != source_extent + 1
        ):
            raise ValueError("comma source-20 result differs from its fixed edge")
        provider.require_global_release_admission()
        ports = _exact_boundary_ports(result_ports)
        sector = decimal_sector(result_payload.value)
        if ports != (sector.leading, sector.digit, sector.headroom):
            raise ValueError("comma source-20 result changed its literal ports")
        return
    if action.kind != "global-boundary-return":
        return

    state = action.boundary_source
    source_cursor = source_payload.boundary_cursor
    if (
        type(state) is not BoundaryState
        or action.boundary_target is not None
        or type(source_cursor) is not BoundaryPrefixCursor
        or source_cursor.state != state
        or source_cursor.transitions != 0
    ):
        raise ValueError("comma global return has another source cursor")
    provider = owner.require_global_future_provider(action.future_digest)
    source_exponent = decimal_sector(source_payload.value).exponent
    if source_cursor.exponent != source_exponent:
        raise ValueError("comma global return has another source phase")
    selected_template = arena.boundary_template(state) if template is None else template
    if (
        type(selected_template) is not MacroTemplate
        or selected_template.source != state
        or selected_template.outcome != "fork"
    ):
        raise ValueError("comma global return source is not a fork")
    exact_transitions = (
        selected_template.weight.evaluate(
            source_exponent, charge_bits=arena.charge_bits
        )
        + 1
    )
    if expected_transitions is not None and expected_transitions != exact_transitions:
        raise ValueError("comma global return changed its admitted macro extent")
    cursor = result_payload.boundary_cursor
    if (
        type(cursor) is not BoundaryPrefixCursor
        or type(cursor.selection_receipt) is not BoundarySelectionReceiptID
    ):
        raise ValueError("comma global return omitted its selection receipt")
    receipt_id = cursor.selection_receipt
    receipt = owner.resolve_boundary_selection_receipt(receipt_id)
    receipt.validate_provider(provider)
    receipt.validate_source(
        source_state=state,
        source_exponent=source_exponent,
        source_value=source_payload.value,
        source_index=source_payload.absolute_index,
        source_extent=source_extent,
    )
    selection = receipt.selection
    slot = selection.selected_slot
    if (
        selection.source != state
        or selection.fork_coefficient != selected_template.destination_a
        or slot not in (0, 1)
        or receipt.target_state != selected_template.ordered_children[slot]
        or receipt.target_exponent != source_exponent + selected_template.exponent_delta
        or receipt.transitions != exact_transitions
        or result_payload.value != receipt.target_value
        or result_payload.absolute_index
        != source_payload.absolute_index + exact_transitions
        or result_extent != source_extent + exact_transitions
        or cursor.state != receipt.target_state
        or cursor.exponent != receipt.target_exponent
        or cursor.transitions != 0
    ):
        raise ValueError("comma global return differs from its issued child slot")
    receipt.validate_output(
        value=result_payload.value,
        absolute_index=result_payload.absolute_index,
        cursor=cursor,
        receipt_id=receipt_id,
    )
    ports = _exact_boundary_ports(result_ports)
    sector = decimal_sector(result_payload.value)
    if ports != (sector.leading, sector.digit, sector.headroom):
        raise ValueError("comma global return changed its output ports")


def _exact_boundary_ports(ports: tuple[Hashable, ...]) -> tuple[int, int, int]:
    if len(ports) != 3:
        raise ValueError("comma future return needs exactly three boundary ports")
    leading, digit, headroom = ports
    if type(leading) is not int or type(digit) is not int or type(headroom) is not int:
        raise ValueError("comma future return boundary ports must be exact integers")
    return leading, digit, headroom


def clear_boundary_occurrence_stores(
    ledger: ResourceLedger,
    occurrences: LedgerList[_OccurrenceRecord],
    seals: LedgerList[_OccurrenceRecord],
    occurrence_owner: int,
    seal_owner: int,
) -> None:
    """Clear occurrence payloads and reconcile their term-owned ledger charges."""
    for store, owner in ((occurrences, occurrence_owner), (seals, seal_owner)):
        store.clear()
        if len(store):
            raise RuntimeError("comma occurrence store did not clear")
        account = ledger.inventory_owner(owner)
        if account.entries or account.nodes:
            ledger.release(owner, entries=account.entries, nodes=account.nodes)


def clear_boundary_selection_receipt_stores(
    ledger: ResourceLedger,
    receipts: LedgerDict[BoundarySelectionReceiptID, BoundarySelectionReceipt],
    seals: LedgerDict[BoundarySelectionReceiptID, BoundarySelectionReceipt],
    receipt_owner: int,
    seal_owner: int,
) -> None:
    """Remove every receipt handle and release residual ledger charges safely."""
    receipt_view = receipts.audit_view()
    seal_view = seals.audit_view()
    identifiers = tuple(dict.fromkeys((*receipt_view.keys(), *seal_view.keys())))
    for identifier in identifiers:
        if identifier in receipt_view:
            receipt = receipt_view[identifier]
            if not receipts.rollback_unpublished(identifier, receipt):
                raise RuntimeError("comma receipt disappeared during close")
        if identifier in seal_view:
            seal = seal_view[identifier]
            if not seals.rollback_unpublished(identifier, seal):
                raise RuntimeError("comma receipt seal disappeared during close")
    for store, owner in ((receipts, receipt_owner), (seals, seal_owner)):
        if len(store):
            raise RuntimeError("comma receipt store did not clear")
        account = ledger.inventory_owner(owner)
        if account.entries or account.nodes:
            ledger.release(owner, entries=account.entries, nodes=account.nodes)


def rollback_boundary_selection_receipt_entry(
    ledger: ResourceLedger,
    identifier: BoundarySelectionReceiptID,
    receipt: BoundarySelectionReceipt,
    receipts: LedgerDict[BoundarySelectionReceiptID, BoundarySelectionReceipt],
    seals: LedgerDict[BoundarySelectionReceiptID, BoundarySelectionReceipt],
    receipt_owner: int,
    seal_owner: int,
) -> None:
    """Undo one reserved receipt/seal pair without touching other owners."""
    for store, owner in ((receipts, receipt_owner), (seals, seal_owner)):
        current = store.get(identifier)
        if current is receipt:
            if not store.rollback_unpublished(identifier, receipt):
                raise RuntimeError("comma receipt rollback lost its exact entry")
        elif current is None:
            ledger.release(owner, entries=1, nodes=1)
        else:
            raise RuntimeError("comma receipt rollback found another object")


__all__ = [
    "BoundaryPrefixCursor",
    "BoundarySelectionReceiptID",
    "BoundarySelectionReceipt",
    "issue_boundary_selection_receipt_entry",
    "resolve_boundary_selection_receipt_entry",
    "clear_boundary_occurrence_stores",
    "clear_boundary_selection_receipt_stores",
    "rollback_boundary_selection_receipt_entry",
    "CommaImagePayload",
    "CommaOccurrenceRecord",
    "CommaTermPayloadAuditSnapshot",
    "SOURCE",
    "validate_action_result",
]
