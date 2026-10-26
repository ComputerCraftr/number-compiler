"""Bounded runtime access to an admitted semantic FutureCID table.

The codec owns bounded candidate parsing and this module owns admitted runtime
providers, selection seals, and their ledger-scoped lifecycle. It never
constructs the semantic graph or derives a classification from arithmetic.
Candidate JSON is untrusted input: a private immutable registry must bind the
exact canonical artifact digest to the accepted kernel theorem before a
provider is returned. That registry is deliberately empty today.

The required kernel contract is the producer-level release theorem: it joins
the decade writer and prefix-selection model with the semantic global-safety
result. This model theorem is not an executable proof of Python source; an
artifact remains unregistered until its producer/runtime bridge is reviewed.

The table contains classifier observations only.  It does not contain an
occurrence weight, width, phase advance, endpoint, or C1 seam.  A selected
slot can be applied to the caller's exact ordered literal children, preserving
those occurrence values unchanged. Finite synthetic fixtures have a separate
test-only scope and cannot satisfy the global release contract. Public
queries can consume an explicitly supplied, revalidated global lease;
default activation still requires an accepted kernel registry entry and
loading its exact artifact.
"""

from __future__ import annotations

from collections.abc import Callable, Generator, Mapping
from contextlib import ExitStack, contextmanager
from dataclasses import dataclass, field
from functools import partial
from pathlib import Path
from threading import RLock
from types import MappingProxyType
from typing import Final, Literal, Self, TypeVar
from weakref import ReferenceType, ref

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.resources.bounded_json import NodeReserver
from number_compiler.resources.immutable_signature import (
    ScalarSignature,
    matches_scalar_signature,
)
from number_compiler.resources.ledger import (
    LedgerReservation,
    OwnedMemo,
    ResourceLedger,
)
from number_compiler.resources.metric_keys import comma as _comma_keys
from number_compiler.resources.payload_contracts import PayloadAuditStoreBinding
from number_compiler.sequences.comma import future_authority as _future_authority
from number_compiler.sequences.comma.boundary_quotient import (
    BoundaryState,
    boundary_source_index,
    boundary_state_signature,
)
from number_compiler.sequences.comma.future_authority import (
    FutureClass,
    FutureControl,
    KernelInstanceAdmission,
    class_row_signature,
    global_release_admission_matches,
    registered_admission_matches,
    valid_artifact_digest,
)
from number_compiler.sequences.comma.future_provider_codec import (
    FUTURE_CANDIDATE_AUTHORITY,
    FUTURE_CANDIDATE_FORMAT,
    FUTURE_SOURCE_UNIVERSE,
    MAX_CANDIDATE_BYTES,
    MAX_CANDIDATE_JSON_DEPTH,
    MAX_CANDIDATE_JSON_NODES,
    MAX_CID_VARINT_BYTES,
    SOURCE_COUNT,
    ParsedFutureCandidate,
    future_candidate_sha256,
    parse_future_candidate,
    preflight_future_candidate,
    validate_record,
)
from number_compiler.sequences.comma.future_provider_codec import (
    charge_work_amount as _charge_work,
)
from number_compiler.sequences.comma.future_provider_codec import (
    parse_future_candidate_file as _parse_future_candidate_file,
)
from number_compiler.sequences.comma.future_provider_codec import (
    parse_preflighted_future_candidate as _parse_preflighted_future_candidate,
)
from number_compiler.sequences.comma.future_provider_memory import (
    RetainedSemanticFutureProvider,
    SemanticFutureProviderAuditSnapshot,
    SemanticFutureProviderLease,
    SemanticFutureProviderStoreAuditSnapshot,
    admission_metadata_matches,
    audit_semantic_future_provider_store,
    candidate_admission_matches,
    candidate_workspace_cost,
    close_provider_store,
    copy_admission_metadata,
    make_retained_provider_entry,
    provider_audit_snapshot,
    provider_node_cost,
    provider_store_audit_snapshot,
    provider_table_bindings_match,
    resolve_provider_lease_locked,
    retained_provider_entry_matches,
)

FUTURE_PROVIDER_ASSET: Final[str] = "comma_semantic_future_v2.json"
FUTURE_PROVIDER_CONTRACT: Final[str] = "comma-semantic-future-provider-exact-v1"
FUTURE_PROVIDER_AUDIT_FAMILY: Final[str] = "comma"
FUTURE_PROVIDER_STORE_ROLE: Final[str] = "semantic_future_provider"
FUTURE_PROVIDER_WORKSPACE_ROLE: Final[str] = "semantic_future_provider_workspace"
# Deliberately empty until the FutureCID instance has passed the Isabelle
# kernel gate and its exact artifact/theorem binding is reviewed for release.
_ADMITTED_KERNEL_INSTANCES: Mapping[str, KernelInstanceAdmission] = MappingProxyType(
    dict[str, KernelInstanceAdmission]()
)


def registered_admission_metadata_matches(candidate: object, digest: str) -> bool:
    """Match copied metadata against the private kernel registry entry."""
    if type(candidate) is not KernelInstanceAdmission or not valid_artifact_digest(
        digest
    ):
        return False
    return admission_metadata_matches(
        candidate, _ADMITTED_KERNEL_INSTANCES.get(digest), digest
    )


registered_global_release_artifact_sha256 = partial(
    _future_authority.registered_global_release_artifact_sha256,
    _ADMITTED_KERNEL_INSTANCES,
)


_PROVIDER_SEAL = object()
_SELECTION_SEAL = object()
WorkCharger = Callable[[int], None]


_Literal = TypeVar("_Literal")
_BeforeFutureParse = Callable[[Mapping[str, object]], None]
_ReserveDecodedShape = Callable[[Mapping[str, object]], None]


@dataclass(frozen=True, slots=True, init=False)
class UnrankedChildSelection:
    """Unique unranked quotient edge, without occurrence reconstruction."""

    source: BoundaryState
    source_class: int
    fork_coefficient: int
    ordered_child_classes: tuple[int, int]
    selected_slot: Literal[0, 1]
    _provider_authority: object = field(repr=False, compare=False, hash=False)
    _provider_authority_snapshot: object = field(repr=False, compare=False, hash=False)
    _fields_snapshot: tuple[object, ...] = field(repr=False, compare=False, hash=False)
    _seal: object = field(repr=False, compare=False, hash=False)

    def __init__(
        self,
        source: BoundaryState,
        source_class: int,
        fork_coefficient: int,
        ordered_child_classes: tuple[int, int],
        selected_slot: Literal[0, 1],
        *,
        _provider_authority: object | None = None,
        _seal: object | None = None,
    ) -> None:
        if _seal is not _SELECTION_SEAL or _provider_authority is None:
            raise TypeError("use the checked provider selection issuer")
        object.__setattr__(self, "source", source)
        object.__setattr__(self, "source_class", source_class)
        object.__setattr__(self, "fork_coefficient", fork_coefficient)
        object.__setattr__(self, "ordered_child_classes", ordered_child_classes)
        object.__setattr__(self, "selected_slot", selected_slot)
        object.__setattr__(self, "_provider_authority", _provider_authority)
        object.__setattr__(self, "_provider_authority_snapshot", _provider_authority)
        object.__setattr__(self, "_fields_snapshot", self._current_fields_snapshot())
        object.__setattr__(self, "_seal", _seal)
        self._validate_fields()

    def _current_fields_snapshot(self) -> tuple[object, ...]:
        return (
            boundary_state_signature(self.source),
            self.source_class,
            self.fork_coefficient,
            self.ordered_child_classes,
            self.selected_slot,
        )

    def _validate_fields(self) -> None:
        if type(self.source) is not BoundaryState:
            raise ValueError("future selection needs an exact source state")
        boundary_source_index(self.source)
        if type(self.source_class) is not int or self.source_class < 0:
            raise ValueError("future selection needs an exact source CID")
        if (
            type(self.fork_coefficient) is not int
            or not 2 <= self.fork_coefficient <= 9
        ):
            raise ValueError("future selection needs an exact Fork coefficient")
        if (
            type(self.ordered_child_classes) is not tuple
            or len(self.ordered_child_classes) != 2
            or any(
                type(cid) is not int or cid < 0 for cid in self.ordered_child_classes
            )
        ):
            raise ValueError("future selection needs two exact ordered child CIDs")
        if type(self.selected_slot) is not int or self.selected_slot not in (0, 1):
            raise ValueError("future selection needs an exact ordered child slot")

    def is_issued(self) -> bool:
        """Check the immutable issuer seal before using this selection."""
        if (
            self._seal is not _SELECTION_SEAL
            or self._provider_authority is not self._provider_authority_snapshot
        ):
            return False
        try:
            self._validate_fields()
            return self._current_fields_snapshot() == self._fields_snapshot
        except (AttributeError, TypeError, ValueError):
            return False

    def matches_provider(self, provider: object) -> bool:
        """Require this selection to be issued by the exact provider instance."""
        if not self.is_issued():
            return False
        if type(provider) is SemanticFutureProvider:
            resolved = provider
        elif type(provider) is SemanticFutureProviderLease:
            try:
                resolved = provider.resolve_provider(record_metrics=False)
            except (PermissionError, RuntimeError, TypeError):
                return False
        else:
            return False
        try:
            return resolved.matches_selection_authority(self._provider_authority)
        except (PermissionError, RuntimeError, TypeError):
            return False

    @property
    def selected_class(self) -> int:
        if not self.is_issued():
            raise ValueError("future selection fields changed after issuance")
        return self.ordered_child_classes[self.selected_slot]

    def select_literal(self, ordered_literals: tuple[_Literal, _Literal]) -> _Literal:
        """Select the exact caller-provided child at the checked N/Z slot."""
        if not self.is_issued():
            raise ValueError("future selection fields changed after issuance")
        if type(ordered_literals) is not tuple or len(ordered_literals) != 2:
            raise ValueError("future selection needs both ordered literal children")
        return ordered_literals[self.selected_slot]


@dataclass(frozen=True, slots=True, init=False)
class SemanticFutureProvider:
    """Bounded FutureCID data with execution authority only while store-retained."""

    _source_classes: tuple[int, ...]
    _classes: tuple[FutureClass, ...]
    _digest: str
    _admission: KernelInstanceAdmission
    _source_classes_binding: tuple[int, ...] = field(
        repr=False, compare=False, hash=False
    )
    _classes_binding: tuple[FutureClass, ...] = field(
        repr=False, compare=False, hash=False
    )
    _class_signatures: tuple[ScalarSignature, ...] = field(
        repr=False, compare=False, hash=False
    )
    _class_signatures_binding: tuple[ScalarSignature, ...] = field(
        repr=False, compare=False, hash=False
    )
    _selection_authority: object = field(repr=False, compare=False, hash=False)
    _selection_authority_binding: object = field(repr=False, compare=False, hash=False)
    _runtime_store_ref: ReferenceType[SemanticFutureProviderStore] | None = field(
        repr=False, compare=False, hash=False
    )

    def matches_selection_authority(self, authority: object) -> bool:
        """Check an issuer token against this currently admitted provider."""
        self.require_runtime_admission()
        return authority is self._selection_authority

    def is_bound_to_store(self, store: object) -> bool:
        store_ref = self._runtime_store_ref
        return type(store_ref) is ReferenceType and store_ref() is store

    def matches_retained_entry(
        self,
        retained: object,
        store_binding_matches: bool,
    ) -> bool:
        """Validate the store's issuer record against this provider's exact rows."""
        digest = self._digest
        return (
            type(retained) is RetainedSemanticFutureProvider
            and retained.provider is self
            and retained.artifact_sha256 == digest
            and retained.source_classes is self._source_classes
            and retained.classes is self._classes
            and retained.row_signatures is self._class_signatures
            and retained.admission is self._admission
            and retained.selection_authority is self._selection_authority
            and store_binding_matches
            and registered_admission_metadata_matches(self._admission, digest)
        )

    def __init__(
        self,
        source_classes: tuple[int, ...],
        classes: tuple[FutureClass, ...],
        digest: str,
        *,
        admission: KernelInstanceAdmission,
        _seal: object,
    ) -> None:
        if _seal is not _PROVIDER_SEAL:
            raise TypeError("use the admitted loader")
        object.__setattr__(self, "_source_classes", source_classes)
        object.__setattr__(self, "_classes", classes)
        object.__setattr__(self, "_digest", digest)
        object.__setattr__(self, "_admission", admission)
        signatures = tuple(class_row_signature(row) for row in classes)
        object.__setattr__(self, "_source_classes_binding", source_classes)
        object.__setattr__(self, "_classes_binding", classes)
        object.__setattr__(self, "_class_signatures", signatures)
        object.__setattr__(self, "_class_signatures_binding", signatures)
        selection_authority = object()
        object.__setattr__(self, "_selection_authority", selection_authority)
        object.__setattr__(self, "_selection_authority_binding", selection_authority)
        object.__setattr__(self, "_runtime_store_ref", None)

    @classmethod
    def from_record(
        cls,
        record: Mapping[str, object],
        *,
        charge_work: WorkCharger,
        _before_parse: _BeforeFutureParse | None = None,
        _reserve_nodes: NodeReserver | None = None,
        _reserve_decoded_shape: _ReserveDecodedShape | None = None,
    ) -> SemanticFutureProvider:
        """Read a registered candidate; the ledger store issues runtime authority."""
        snapshot = preflight_future_candidate(
            record,
            charge_work=charge_work,
            reserve_nodes=_reserve_nodes,
        )
        if _before_parse is not None:
            _before_parse(record)
        if _reserve_decoded_shape is not None:
            _reserve_decoded_shape(snapshot)
        parsed = _parse_preflighted_future_candidate(
            snapshot,
            charge_work=charge_work,
        )
        return cls._from_parsed(parsed)

    @classmethod
    def _from_parsed(cls, parsed: ParsedFutureCandidate) -> SemanticFutureProvider:
        registered = _ADMITTED_KERNEL_INSTANCES.get(parsed.artifact_sha256)
        if registered is None or not _admission_matches(registered, parsed):
            raise PermissionError(
                "no kernel-admitted semantic future artifact is registered"
            )
        admission = copy_admission_metadata(registered)
        return cls(
            parsed.source_classes,
            parsed.classes,
            parsed.artifact_sha256,
            admission=admission,
            _seal=_PROVIDER_SEAL,
        )

    @classmethod
    def load_file(
        cls,
        path: Path,
        *,
        charge_work: WorkCharger,
        _before_parse: _BeforeFutureParse | None = None,
        _reserve_nodes: NodeReserver | None = None,
        _reserve_decoded_shape: _ReserveDecodedShape | None = None,
    ) -> SemanticFutureProvider:
        """Load a bounded canonical artifact and require registry admission."""
        parsed = _parse_future_candidate_file(
            path,
            charge_work=charge_work,
            before_parse=_before_parse,
            reserve_nodes=_reserve_nodes,
            reserve_decoded_shape=_reserve_decoded_shape,
        )
        return cls._from_parsed(parsed)

    @property
    def artifact_sha256(self) -> str:
        return self._digest

    @property
    def runtime_admitted(self) -> bool:
        if not self._candidate_admission_matches():
            return False
        store_ref = self._runtime_store_ref
        if type(store_ref) is not ReferenceType:
            return False
        store = store_ref()
        return type(
            store
        ) is SemanticFutureProviderStore and store.retained_provider_matches(self)

    @property
    def global_release_admitted(self) -> bool:
        """Whether this exact artifact has the full global kernel contract."""
        return self.runtime_admitted and global_release_admission_matches(
            self._admission, self._digest
        )

    @property
    def class_count(self) -> int:
        self._require_table_bindings()
        return len(self._classes)

    @property
    def source_class_count(self) -> int:
        """Return the validated number of retained source-class rows."""
        self._require_table_bindings()
        return len(self._source_classes)

    def _tables_bound(self, *, allow_closing: bool = False) -> bool:
        if not self._tables_bound_without_store():
            return False
        store_ref = self._runtime_store_ref
        if store_ref is None:
            return not allow_closing
        if type(store_ref) is not ReferenceType:
            return False
        store = store_ref()
        return type(
            store
        ) is SemanticFutureProviderStore and store.retained_provider_matches(
            self, allow_closing=allow_closing
        )

    def _candidate_admission_matches(self) -> bool:
        return candidate_admission_matches(
            self._digest,
            self._admission,
            self._tables_bound_without_store(),
            registered_admission_metadata_matches,
        )

    def _tables_bound_without_store(self) -> bool:
        return provider_table_bindings_match(
            self._source_classes,
            self._source_classes_binding,
            self._classes,
            self._classes_binding,
            self._class_signatures,
            self._class_signatures_binding,
            self._selection_authority,
            self._selection_authority_binding,
        )

    def retained_record_for_store(self) -> RetainedSemanticFutureProvider:
        if self._runtime_store_ref is not None:
            raise PermissionError("semantic future provider is already store-issued")
        if not self._candidate_admission_matches():
            raise PermissionError("semantic future candidate tables were altered")
        return make_retained_provider_entry(
            self,
            self._digest,
            self._source_classes,
            self._classes,
            self._class_signatures,
            self._admission,
            self._selection_authority,
        )

    def audit_snapshot(self) -> SemanticFutureProviderAuditSnapshot:
        """Expose immutable rows and their issuer binding for forensic validation."""
        return provider_audit_snapshot(
            self._digest,
            self._source_classes,
            self._classes,
            self._class_signatures,
            self._admission,
            self._selection_authority,
            self._tables_bound(allow_closing=True),
            self._tables_bound(),
            self.runtime_admitted,
            self._selection_authority is self._selection_authority_binding,
        )

    def _require_table_bindings(self) -> None:
        if not self._tables_bound():
            raise PermissionError("semantic future provider table binding changed")

    def _checked_class_row(self, cid: int) -> FutureClass:
        self._require_table_bindings()
        if type(cid) is not int or not 0 <= cid < len(self._classes):
            raise ValueError("future class identifier is out of range")
        row = self._classes[cid]
        try:
            fields = class_row_signature(row)
        except TypeError as exc:
            raise PermissionError("semantic future class row was altered") from exc
        if not matches_scalar_signature(fields, self._class_signatures[cid]):
            raise PermissionError("semantic future class row was altered")
        return row

    def require_runtime_admission(self) -> None:
        """Reject fixtures and candidates absent from the kernel admission registry."""
        if not self.runtime_admitted:
            raise PermissionError("semantic future provider lacks kernel admission")

    def require_global_release_admission(self) -> None:
        """Require the exact global theorem contract, not finite fixture evidence."""
        if not self.global_release_admitted:
            raise PermissionError(
                "semantic future provider lacks global release authority"
            )

    def source_class(self, source: BoundaryState, *, charge_work: WorkCharger) -> int:
        if type(source) is not BoundaryState:
            raise TypeError("future lookup requires a validated BoundaryState")
        self._require_table_bindings()
        _charge_work(charge_work, 1)
        return self._source_classes[boundary_source_index(source)]

    def class_row(self, cid: int, *, charge_work: WorkCharger) -> FutureClass:
        _charge_work(charge_work, 1)
        return self._checked_class_row(cid)

    def select_unique_unranked_child(
        self, source: BoundaryState, *, charge_work: WorkCharger
    ) -> UnrankedChildSelection:
        """Return the unique unranked ordered slot for this admitted source.

        The caller supplies its exact literal children to
        ``selection.select_literal``.  This method never constructs children,
        weights, phases, or extents.
        """
        self.require_runtime_admission()
        _charge_work(charge_work, 1)
        if type(source) is not BoundaryState:
            raise TypeError("future lookup requires a validated BoundaryState")
        self._require_table_bindings()
        source_cid = self._source_classes[boundary_source_index(source)]
        row = self._checked_class_row(source_cid)
        if row.control.kind != "fork" or row.control.fork_coefficient is None:
            raise ValueError("future source is not a Fork class")
        left, right = row.ordered_children
        if left is None or right is None:
            raise ValueError("admitted Fork row lost an ordered child")
        left_unranked = self._checked_class_row(left).rank is None
        right_unranked = self._checked_class_row(right).rank is None
        if left_unranked == right_unranked:
            raise ValueError("future Fork has no unique unranked child")
        slot: Literal[0, 1] = 0 if left_unranked else 1
        if row.rank is not None:
            raise ValueError("finite-ranked source cannot select an infinite child")
        return UnrankedChildSelection(
            source,
            source_cid,
            row.control.fork_coefficient,
            (left, right),
            slot,
            _provider_authority=self._selection_authority,
            _seal=_SELECTION_SEAL,
        )


_FutureProviderLoader = Callable[
    [WorkCharger, NodeReserver, _ReserveDecodedShape], SemanticFutureProvider
]


class SemanticFutureProviderStore:
    """Instance-scoped, ledger-owned admission cache for immutable providers.

    Artifact validation and digest verification occur when a record or file is
    loaded. ``get`` is the separate warm path: it names an already verified
    artifact and never ignores newly supplied bytes or records. Query methods
    on a lease use the retained provider directly. The store has no global state.
    """

    def __init__(self, ledger: ResourceLedger) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("future provider store needs a ResourceLedger")
        self.ledger = ledger
        next_owner = ledger.owner_count
        owner_name = f"comma-semantic-future-provider-{next_owner}"
        workspace_name = f"comma-semantic-future-provider-workspace-{next_owner + 1}"
        ledger.require_fresh_owner_names((owner_name, workspace_name))
        self.owner = ledger.register(owner_name, FUTURE_PROVIDER_STORE_ROLE)
        self._workspace_owner = ledger.register(
            workspace_name,
            FUTURE_PROVIDER_WORKSPACE_ROLE,
        )
        self._providers: OwnedMemo[str, RetainedSemanticFutureProvider] = OwnedMemo(
            ledger, self.owner, node_cost=provider_node_cost
        )
        self._token = ArenaToken("comma-semantic-future-provider")
        self._closed = False
        self._closing = False
        self._lock = RLock()
        ledger.register_execution_root(self)
        self._register_payload_audit_contract()

    @property
    def _audit_provider_payloads(self) -> Mapping[str, object]:
        return self._providers.audit_snapshot().container

    def audit_snapshot(self) -> SemanticFutureProviderStoreAuditSnapshot:
        """Return exact store shape and ledger memo metadata without traversal."""
        lock = self._lock
        lock_valid = self.ledger.payload_audit_contract_matches_root(
            self, FUTURE_PROVIDER_AUDIT_FAMILY
        )
        if lock_valid:
            with lock:
                memo = self._providers.audit_snapshot()
                return provider_store_audit_snapshot(
                    self.ledger,
                    self.owner,
                    self._workspace_owner,
                    memo,
                    self._closed,
                    self._closing,
                    frozenset(vars(self)),
                    frozenset(vars(self._providers)),
                    self._lock is lock
                    and self.ledger.payload_audit_contract_matches_root(
                        self, FUTURE_PROVIDER_AUDIT_FAMILY
                    ),
                    self._providers.node_cost is provider_node_cost,
                )
        memo = self._providers.audit_snapshot()
        return provider_store_audit_snapshot(
            self.ledger,
            self.owner,
            self._workspace_owner,
            memo,
            self._closed,
            self._closing,
            frozenset(vars(self)),
            frozenset(vars(self._providers)),
            False,
            self._providers.node_cost is provider_node_cost,
        )

    def _register_payload_audit_contract(self) -> None:
        self.ledger.register_payload_audit_contract(
            self,
            FUTURE_PROVIDER_AUDIT_FAMILY,
            (
                PayloadAuditStoreBinding(
                    self.owner,
                    "_audit_provider_payloads",
                    FUTURE_PROVIDER_STORE_ROLE,
                    identity_attributes=("_lock", "_providers"),
                    scalar_attributes=("_workspace_owner",),
                ),
            ),
            audit_semantic_future_provider_store,
        )

    def check_open(self) -> None:
        if type(self._closed) is not bool or type(self._closing) is not bool:
            raise RuntimeError("malformed future provider store lifecycle")
        if self._closed or self._closing:
            raise RuntimeError("future provider store is closing or closed")
        self._check_pinned_root()

    def retained_provider_matches(
        self, provider: object, *, allow_closing: bool = False
    ) -> bool:
        if type(provider) is not SemanticFutureProvider:
            return False
        if type(allow_closing) is not bool:
            return False
        lock = self._lock
        try:
            self._check_pinned_root()
            with lock:
                self._check_pinned_root()
                if (
                    self._lock is not lock
                    or type(self._closed) is not bool
                    or self._closed
                    or type(self._closing) is not bool
                    or (self._closing and not allow_closing)
                ):
                    return False
                digest = provider.artifact_sha256
                if type(digest) is not str or not valid_artifact_digest(digest):
                    return False
                store_binding_matches = provider.is_bound_to_store(self)
                return retained_provider_entry_matches(
                    self.ledger,
                    self.owner,
                    self._providers,
                    FUTURE_PROVIDER_STORE_ROLE,
                    provider,
                    digest,
                    store_binding_matches,
                )
        except (KeyError, RuntimeError, TypeError, ValueError):
            return False

    def _check_pinned_root(self) -> None:
        if not self.ledger.payload_audit_contract_matches_attribute(
            self, FUTURE_PROVIDER_AUDIT_FAMILY, "_lock"
        ):
            raise RuntimeError("future provider store lock binding changed")
        if not self.ledger.payload_audit_contract_matches_attribute(
            self, FUTURE_PROVIDER_AUDIT_FAMILY, "_workspace_owner"
        ):
            raise RuntimeError("future provider store workspace owner binding changed")
        if not self.ledger.payload_audit_contract_matches_root(
            self, FUTURE_PROVIDER_AUDIT_FAMILY
        ):
            raise RuntimeError("future provider store authority binding changed")

    @contextmanager
    def _open_store_scope(self) -> Generator[None, None, None]:
        """Capture, validate and acquire the ledger-pinned store lock once."""
        lock = self._lock
        self.check_open()
        with lock:
            self.check_open()
            yield

    def _retain(
        self,
        provider: SemanticFutureProvider,
        reservation: LedgerReservation,
    ) -> SemanticFutureProviderLease:
        self.check_open()
        retained_entry = provider.retained_record_for_store()
        digest = provider.artifact_sha256
        retained = self._providers.get(digest)
        if retained is None:
            # The retained key becomes one live cache entry. Reserve that
            # exact entry only after the absent-digest branch is known.
            reservation.reserve(entries=1)
            object.__setattr__(provider, "_runtime_store_ref", ref(self))
            try:
                self._providers.adopt_reserved(digest, retained_entry, reservation)
            except BaseException:
                object.__setattr__(provider, "_runtime_store_ref", None)
                raise
            try:
                self.ledger.bump(_comma_keys.COMMA_FUTURE_PROVIDER_PUBLICATIONS)
            except BaseException:
                del self._providers[digest]
                object.__setattr__(provider, "_runtime_store_ref", None)
                raise
        else:
            if (
                type(retained) is not RetainedSemanticFutureProvider
                or retained.artifact_sha256 != digest
            ):
                raise PermissionError("future provider store retained an invalid entry")
            retained.provider.require_runtime_admission()
            self.ledger.bump(_comma_keys.COMMA_FUTURE_PROVIDER_SEMANTIC_REUSES)
        return SemanticFutureProviderLease(self, digest, self._token)

    def _load_provider(
        self,
        loader: _FutureProviderLoader,
        charge_work: WorkCharger,
    ) -> SemanticFutureProviderLease:
        with self._open_store_scope():
            self.ledger.bump(_comma_keys.COMMA_FUTURE_PROVIDER_LOAD_REQUESTS)
            self.ledger.bump(_comma_keys.COMMA_FUTURE_PROVIDER_VALIDATION_REQUESTS)
            try:
                with ExitStack() as reservations:
                    workspace = LedgerReservation(self.ledger, self._workspace_owner)
                    reservations.callback(workspace.close)

                    def reserve_snapshot_nodes(amount: int) -> None:
                        workspace.reserve(nodes=amount)

                    def reserve_decoded_shape(record: Mapping[str, object]) -> None:
                        nodes = candidate_workspace_cost(record, SOURCE_COUNT)
                        if nodes:
                            workspace.reserve(nodes=nodes)

                    def charge_once(amount: int) -> None:
                        _charge_work(charge_work, amount)
                        self.ledger.bump(
                            _comma_keys.COMMA_FUTURE_PROVIDER_LOAD_WORK, amount
                        )

                    provider = loader(
                        charge_once,
                        reserve_snapshot_nodes,
                        reserve_decoded_shape,
                    )
                    return self._retain(provider, workspace)
            except Exception:
                self.ledger.bump(_comma_keys.COMMA_FUTURE_PROVIDER_LOAD_FAILURES)
                raise
            except BaseException:
                # Cancellation/system-exit paths are not validation failures,
                # but still have explicit accounting. ExitStack releases any
                # workspace reservation before this handler runs.
                self.ledger.bump(_comma_keys.COMMA_FUTURE_PROVIDER_LOAD_CANCELLATIONS)
                raise

    def get(self, artifact_sha256: str) -> SemanticFutureProviderLease:
        """Retrieve an already verified registry admission without reading input."""
        with self._open_store_scope():
            self.ledger.bump(_comma_keys.COMMA_FUTURE_PROVIDER_LOOKUPS)
            if not valid_artifact_digest(artifact_sha256):
                self.ledger.bump(_comma_keys.COMMA_FUTURE_PROVIDER_LOOKUP_REFUSALS)
                raise ValueError("future artifact lookup needs a lowercase SHA-256")
            retained = self._providers.get(artifact_sha256)
            if retained is None:
                self.ledger.bump(_comma_keys.COMMA_FUTURE_PROVIDER_LOOKUP_MISSES)
                raise KeyError("future artifact has not been loaded into this ledger")
            if (
                type(retained) is not RetainedSemanticFutureProvider
                or retained.artifact_sha256 != artifact_sha256
            ):
                raise RuntimeError("future provider store retained an invalid entry")
            provider = retained.provider
            provider.require_runtime_admission()
            self.ledger.bump(_comma_keys.COMMA_FUTURE_PROVIDER_LOOKUP_HITS)
            return SemanticFutureProviderLease(self, artifact_sha256, self._token)

    def load_record(
        self,
        record: Mapping[str, object],
        *,
        charge_work: WorkCharger,
    ) -> SemanticFutureProviderLease:
        """Validate, admit, and retain a supplied in-memory candidate."""
        return self._load_provider(
            lambda charged, reserve_nodes, reserve_shape: (
                SemanticFutureProvider.from_record(
                    record,
                    charge_work=charged,
                    _reserve_nodes=reserve_nodes,
                    _reserve_decoded_shape=reserve_shape,
                )
            ),
            charge_work,
        )

    def load_file(
        self,
        path: Path,
        *,
        charge_work: WorkCharger,
    ) -> SemanticFutureProviderLease:
        """Verify supplied bytes before admitting and retaining their provider."""
        return self._load_provider(
            lambda charged, reserve_nodes, reserve_shape: (
                SemanticFutureProvider.load_file(
                    path,
                    charge_work=charged,
                    _reserve_nodes=reserve_nodes,
                    _reserve_decoded_shape=reserve_shape,
                )
            ),
            charge_work,
        )

    def resolve_checked(
        self,
        digest: str,
        token: ArenaToken,
        *,
        record_metrics: bool = True,
    ) -> SemanticFutureProvider:
        if type(self) is not SemanticFutureProviderStore:
            raise TypeError("future provider lease needs its exact provider store")
        if type(record_metrics) is not bool:
            raise TypeError("future provider resolution mode must be Boolean")
        ledger = getattr(self, "ledger", None)
        closed = getattr(self, "_closed", None)
        closing = getattr(self, "_closing", None)
        if (
            type(ledger) is not ResourceLedger
            or type(closed) is not bool
            or type(closing) is not bool
        ):
            raise RuntimeError("malformed future provider store")
        if closed or closing:
            if record_metrics:
                ledger.bump(_comma_keys.COMMA_FUTURE_PROVIDER_STALE_LEASE_REFUSALS)
            raise RuntimeError("future provider lease is stale")
        lock = getattr(self, "_lock", None)
        if lock is None:
            raise RuntimeError("malformed future provider store")
        self._check_pinned_root()
        with lock:
            self._check_pinned_root()
            return resolve_provider_lease_locked(
                ledger,
                self,
                FUTURE_PROVIDER_AUDIT_FAMILY,
                FUTURE_PROVIDER_STORE_ROLE,
                digest,
                token,
                record_metrics,
                getattr(self, "_closed", None),
                getattr(self, "_closing", None),
                getattr(self, "_token", None),
                getattr(self, "_providers", None),
                getattr(self, "owner", None),
            )

    def reset(self) -> None:
        """Release retained candidates and revoke leases without closing owner."""
        with self._open_store_scope():
            self._providers.clear()
            self._token = ArenaToken("comma-semantic-future-provider")
            self.ledger.bump(_comma_keys.COMMA_FUTURE_PROVIDER_RESETS)

    def close(self) -> None:
        """Drop retained tables and invalidate every lease; safe to call twice."""
        if self._closed:
            return
        lock = self._lock
        self._check_pinned_root()
        with lock:
            if self._closed:
                return
            self._check_pinned_root()
            self._closing = True
            close_provider_store(
                self.ledger,
                self,
                self.owner,
                self._providers,
                FUTURE_PROVIDER_AUDIT_FAMILY,
                self._register_payload_audit_contract,
                self._finish_close,
            )

    def _finish_close(self) -> None:
        self._token = ArenaToken("comma-semantic-future-provider")
        self._closed = True
        self._closing = False
        self.ledger.bump(_comma_keys.COMMA_FUTURE_PROVIDER_CLOSES)

    def __enter__(self) -> Self:
        with self._open_store_scope():
            return self

    def __exit__(self, exc_type: object, exc: object, traceback: object) -> None:
        self.close()


def _admission_matches(
    admission: KernelInstanceAdmission, parsed: ParsedFutureCandidate
) -> bool:
    return registered_admission_matches(admission, parsed.artifact_sha256)


__all__ = [
    "FUTURE_CANDIDATE_AUTHORITY",
    "FUTURE_CANDIDATE_FORMAT",
    "FUTURE_PROVIDER_CONTRACT",
    "FUTURE_SOURCE_UNIVERSE",
    "FutureClass",
    "FutureControl",
    "MAX_CANDIDATE_BYTES",
    "MAX_CANDIDATE_JSON_DEPTH",
    "MAX_CANDIDATE_JSON_NODES",
    "MAX_CID_VARINT_BYTES",
    "ParsedFutureCandidate",
    "registered_admission_metadata_matches",
    "SemanticFutureProvider",
    "SemanticFutureProviderLease",
    "SemanticFutureProviderStore",
    "UnrankedChildSelection",
    "future_candidate_sha256",
    "preflight_future_candidate",
    "parse_future_candidate",
    "validate_record",
]
