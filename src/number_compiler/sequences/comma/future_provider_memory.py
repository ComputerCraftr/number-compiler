"""Ledger ownership, retained-entry audits, and leases for FutureCID providers."""

from __future__ import annotations

from collections.abc import Callable, Mapping
from dataclasses import dataclass
from types import MappingProxyType
from typing import TYPE_CHECKING, NamedTuple, TypeGuard, cast

from number_compiler.arithmetic.contracts.input_validation import (
    is_exact_object_tuple,
    is_object_list,
)
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.resources.immutable_signature import (
    ScalarSignature,
    matches_scalar_signature,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import comma as _comma_keys
from number_compiler.resources.owned_memo import (
    DynamicMemoValue,
    OwnedMemo,
    OwnedMemoAuditSnapshot,
)
from number_compiler.resources.payload_containers import audit_mapping_items
from number_compiler.resources.payload_contracts import (
    PayloadAuditContribution,
    PayloadAuditEntry,
)
from number_compiler.resources.stores import LedgerDict, TrackedDict
from number_compiler.sequences.comma.boundary_quotient import BoundaryState
from number_compiler.sequences.comma.future_authority import (
    FutureClass,
    FutureControl,
    KernelInstanceAdmission,
    class_row_signature,
    registered_admission_matches,
    valid_artifact_digest,
)
from number_compiler.sequences.comma.future_provider_codec import SOURCE_COUNT

if TYPE_CHECKING:
    from number_compiler.sequences.comma.future_provider import (
        SemanticFutureProvider,
        SemanticFutureProviderStore,
        UnrankedChildSelection,
    )


class RetainedSemanticFutureProvider(NamedTuple):
    """Store-owned anchor for the exact tables issued by the provider store."""

    provider: SemanticFutureProvider
    artifact_sha256: str
    source_classes: tuple[int, ...]
    classes: tuple[FutureClass, ...]
    row_signatures: tuple[ScalarSignature, ...]
    admission: KernelInstanceAdmission
    selection_authority: object


@dataclass(frozen=True, slots=True)
class SemanticFutureProviderAuditSnapshot:
    """Read-only provider rows and source authority used by the store contract."""

    artifact_sha256: str
    source_classes: tuple[int, ...]
    classes: tuple[FutureClass, ...]
    row_signatures: tuple[ScalarSignature, ...]
    admission: KernelInstanceAdmission
    selection_authority: object
    retained_entry_bound: bool
    tables_bound: bool
    runtime_admitted: bool
    selection_authority_bound: bool


@dataclass(frozen=True, slots=True)
class SemanticFutureProviderStoreAuditSnapshot:
    """Read-only store shape and exact ledger memo snapshot."""

    ledger: ResourceLedger
    owner: int
    workspace_owner: int
    memo: OwnedMemoAuditSnapshot[str, RetainedSemanticFutureProvider]
    closed: bool
    closing: bool
    root_fields: frozenset[str]
    memo_fields: frozenset[str]
    lock_valid: bool
    memo_node_cost_valid: bool


def provider_store_audit_snapshot(
    ledger: ResourceLedger,
    owner: int,
    workspace_owner: int,
    memo: OwnedMemoAuditSnapshot[str, RetainedSemanticFutureProvider],
    closed: bool,
    closing: bool,
    root_fields: frozenset[str],
    memo_fields: frozenset[str],
    lock_valid: bool,
    memo_node_cost_valid: bool,
) -> SemanticFutureProviderStoreAuditSnapshot:
    return SemanticFutureProviderStoreAuditSnapshot(
        ledger,
        owner,
        workspace_owner,
        memo,
        closed,
        closing,
        root_fields,
        memo_fields,
        lock_valid,
        memo_node_cost_valid,
    )


def provider_table_bindings_match(
    source_classes: object,
    source_binding: object,
    classes: object,
    classes_binding: object,
    signatures: object,
    signatures_binding: object,
    selection_authority: object,
    selection_binding: object,
) -> bool:
    if (
        not _is_int_tuple(source_classes)
        or source_classes is not source_binding
        or not _is_future_class_tuple(classes)
        or classes is not classes_binding
        or not _is_signature_tuple(signatures)
        or signatures is not signatures_binding
        or selection_authority is not selection_binding
    ):
        return False
    return len(classes) == len(signatures)


def candidate_admission_matches(
    digest: object,
    admission: object,
    table_bindings_match: bool,
    matches_registered_admission: Callable[[object, str], bool],
) -> bool:
    if (
        not table_bindings_match
        or type(digest) is not str
        or not valid_artifact_digest(digest)
        or type(admission) is not KernelInstanceAdmission
    ):
        return False
    return matches_registered_admission(admission, digest)


def copy_admission_metadata(
    admission: KernelInstanceAdmission,
) -> KernelInstanceAdmission:
    """Copy registry metadata so provider snapshots never expose its record."""
    if type(
        admission
    ) is not KernelInstanceAdmission or not registered_admission_matches(
        admission, admission.artifact_sha256
    ):
        raise PermissionError("semantic future registry admission is malformed")
    return KernelInstanceAdmission(
        artifact_sha256=admission.artifact_sha256,
        instance_id=admission.instance_id,
        theorem_id=admission.theorem_id,
        contract_id=admission.contract_id,
        claims=frozenset(tuple(admission.claims)),
        scope=admission.scope,
    )


def admission_metadata_matches(
    candidate: object, registered: object, digest: str
) -> bool:
    """Compare copied admission data with the private registry entry."""
    if (
        type(candidate) is not KernelInstanceAdmission
        or type(registered) is not KernelInstanceAdmission
        or not valid_artifact_digest(digest)
        or not registered_admission_matches(candidate, digest)
        or not registered_admission_matches(registered, digest)
    ):
        return False
    return (
        candidate.artifact_sha256 == registered.artifact_sha256
        and candidate.instance_id == registered.instance_id
        and candidate.theorem_id == registered.theorem_id
        and candidate.contract_id == registered.contract_id
        and candidate.claims == registered.claims
        and candidate.scope == registered.scope
    )


def retained_entry_matches_provider(
    retained: object,
    provider: SemanticFutureProvider,
    store_binding_matches: bool,
) -> bool:
    return provider.matches_retained_entry(retained, store_binding_matches)


def _is_retained_provider_memo(
    value: object,
) -> TypeGuard[OwnedMemo[str, RetainedSemanticFutureProvider]]:
    return type(value) is OwnedMemo


def _is_int_tuple(value: object) -> TypeGuard[tuple[int, ...]]:
    return is_exact_object_tuple(value) and all(type(item) is int for item in value)


def _is_future_class_tuple(
    value: object,
) -> TypeGuard[tuple[FutureClass, ...]]:
    return is_exact_object_tuple(value) and all(
        type(item) is FutureClass for item in value
    )


def _is_signature_tuple(
    value: object,
) -> TypeGuard[tuple[ScalarSignature, ...]]:
    return is_exact_object_tuple(value) and all(type(item) is tuple for item in value)


def retained_provider_entry_matches(
    ledger: ResourceLedger,
    owner: object,
    memo_value: object,
    store_role: str,
    provider: SemanticFutureProvider,
    digest: object,
    store_binding_matches: bool,
) -> bool:
    """Match a provider against its exact still-owned memo entry in O(1)."""
    from number_compiler.sequences.comma.future_provider import SemanticFutureProvider

    if (
        type(ledger) is not ResourceLedger
        or type(owner) is not int
        or not _is_retained_provider_memo(memo_value)
        or memo_value.ledger is not ledger
        or memo_value.owner != owner
        or memo_value.node_cost is not provider_node_cost
        or type(provider) is not SemanticFutureProvider
        or type(digest) is not str
        or not valid_artifact_digest(digest)
        or type(store_role) is not str
        or type(store_binding_matches) is not bool
        or not store_binding_matches
    ):
        return False
    try:
        memo_snapshot = memo_value.audit_snapshot()
        owner_status = ledger.account_status(owner)
        if (
            memo_snapshot.disposed
            or owner_status.disposed
            or owner_status.role != store_role
            or owner_status.container_identity != id(memo_snapshot.container)
        ):
            return False
        retained: RetainedSemanticFutureProvider | None = memo_value.get(digest)
        return retained_entry_matches_provider(
            retained,
            provider,
            store_binding_matches,
        )
    except (KeyError, RuntimeError, TypeError, ValueError):
        return False


def make_retained_provider_entry(
    provider: SemanticFutureProvider,
    digest: str,
    source_classes: tuple[int, ...],
    classes: tuple[FutureClass, ...],
    row_signatures: tuple[ScalarSignature, ...],
    admission: KernelInstanceAdmission,
    selection_authority: object,
) -> RetainedSemanticFutureProvider:
    return RetainedSemanticFutureProvider(
        provider,
        digest,
        source_classes,
        classes,
        row_signatures,
        admission,
        selection_authority,
    )


def provider_audit_snapshot(
    digest: str,
    source_classes: tuple[int, ...],
    classes: tuple[FutureClass, ...],
    row_signatures: tuple[ScalarSignature, ...],
    admission: KernelInstanceAdmission,
    selection_authority: object,
    retained_entry_bound: bool,
    tables_bound: bool,
    runtime_admitted: bool,
    selection_authority_bound: bool,
) -> SemanticFutureProviderAuditSnapshot:
    return SemanticFutureProviderAuditSnapshot(
        digest,
        source_classes,
        classes,
        row_signatures,
        admission,
        selection_authority,
        retained_entry_bound,
        tables_bound,
        runtime_admitted,
        selection_authority_bound,
    )


def close_provider_store(
    ledger: ResourceLedger,
    root: object,
    owner: int,
    memo: OwnedMemo[str, RetainedSemanticFutureProvider],
    audit_family: str,
    register_contract: Callable[[], None],
    finish_close: Callable[[], None],
) -> None:
    snapshot = memo.audit_snapshot()
    try:
        if not snapshot.disposed:
            register_contract()
        ledger.remove_payload_audit_contract(root, audit_family)
        memo.dispose()
    except BaseException as disposal_error:
        snapshot = memo.audit_snapshot()
        owner_status = ledger.account_status(owner)
        if not snapshot.disposed and not owner_status.disposed:
            try:
                register_contract()
            except BaseException as restoration_error:
                raise RuntimeError(
                    "future provider close could not restore its audit contract"
                ) from restoration_error
        elif snapshot.disposed and owner_status.disposed and not snapshot.container:
            finish_close()
        else:
            raise RuntimeError(
                "future provider close left an inconsistent memo owner"
            ) from disposal_error
        raise
    finish_close()


def resolve_provider_lease_locked(
    ledger: ResourceLedger,
    root: object,
    audit_family: str,
    store_role: str,
    digest: str,
    token: ArenaToken,
    record_metrics: bool,
    closed: object,
    closing: object,
    current_token: object,
    memo_value: object,
    owner: object,
) -> SemanticFutureProvider:
    if type(closed) is not bool or type(closing) is not bool:
        raise RuntimeError("malformed future provider store")
    if closed or closing:
        if record_metrics:
            ledger.bump(_comma_keys.COMMA_FUTURE_PROVIDER_STALE_LEASE_REFUSALS)
        raise RuntimeError("future provider lease is stale")
    if (
        not ledger.payload_audit_contract_matches_root(root, audit_family)
        or type(current_token) is not ArenaToken
    ):
        raise RuntimeError("malformed future provider store")
    if (
        type(digest) is not str
        or not valid_artifact_digest(digest)
        or type(token) is not ArenaToken
        or token is not current_token
    ):
        if record_metrics:
            ledger.bump(_comma_keys.COMMA_FUTURE_PROVIDER_STALE_LEASE_REFUSALS)
        raise RuntimeError("future provider lease is stale")
    if (
        type(memo_value) is not OwnedMemo
        or memo_value.ledger is not ledger
        or type(owner) is not int
        or memo_value.owner != owner
        or ledger.account_status(owner).role != store_role
    ):
        raise RuntimeError("future provider store has a foreign retained table")
    memo = cast(OwnedMemo[str, object], memo_value)
    retained = memo.get(digest)
    if retained is None:
        if record_metrics:
            ledger.bump(_comma_keys.COMMA_FUTURE_PROVIDER_LEASE_MISSES)
        raise RuntimeError("future provider is no longer retained")
    from number_compiler.sequences.comma.future_provider import (
        SemanticFutureProvider,
    )

    if (
        type(retained) is not RetainedSemanticFutureProvider
        or type(retained.provider) is not SemanticFutureProvider
        or retained.artifact_sha256 != digest
    ):
        raise RuntimeError("future provider store retained a foreign provider")
    provider = retained.provider
    provider.require_runtime_admission()
    if record_metrics:
        ledger.bump(_comma_keys.COMMA_FUTURE_PROVIDER_LEASE_RESOLUTIONS)
    return provider


def provider_node_cost(digest: str, retained: RetainedSemanticFutureProvider) -> int:
    if digest != retained.artifact_sha256:
        raise ValueError("future provider ledger key differs from its artifact digest")
    # Include the retained source/class rows, signatures, issuer and external
    # table anchor. The DynamicMemoValue wrapper is charged by OwnedMemo.
    return len(retained.source_classes) + 10 * len(retained.classes) + 9


def candidate_workspace_cost(record: Mapping[str, object], source_count: int) -> int:
    """Reserve decoded semantic tuples while candidate validation is active.

    The serialized byte limit bounds input size; this estimate does not claim
    to measure the parser's raw JSON object graph or process RSS peak.
    """
    if type(record) not in (dict, MappingProxyType):
        return 0
    controls = record.get("controls")
    if not is_object_list(controls) or not 0 < len(controls) <= source_count:
        return 0
    # Source IDs and their tuple coexist; class rows overlap their builder list.
    signature_nodes = 6 * len(controls) + 5
    return 2 * source_count + 5 * len(controls) + 2 + signature_nodes


def _provider_rows_are_admitted(
    snapshot: SemanticFutureProviderAuditSnapshot,
    digest: str,
    retained: RetainedSemanticFutureProvider,
    matches_registered_admission: Callable[[object, str], bool],
    *,
    allow_quarantined: bool,
) -> bool:
    if (
        type(snapshot) is not SemanticFutureProviderAuditSnapshot
        or hasattr(snapshot, "__dict__")
        or not valid_artifact_digest(digest)
        or snapshot.artifact_sha256 != digest
        or type(snapshot.source_classes) is not tuple
        or len(snapshot.source_classes) != SOURCE_COUNT
        or type(snapshot.classes) is not tuple
        or not 0 < len(snapshot.classes) <= SOURCE_COUNT
        or type(snapshot.row_signatures) is not tuple
        or len(snapshot.row_signatures) != len(snapshot.classes)
        or type(snapshot.admission) is not KernelInstanceAdmission
        or type(snapshot.retained_entry_bound) is not bool
        or not snapshot.retained_entry_bound
        or type(snapshot.tables_bound) is not bool
        or type(snapshot.runtime_admitted) is not bool
        or (allow_quarantined and (snapshot.tables_bound or snapshot.runtime_admitted))
        or (
            not allow_quarantined
            and (not snapshot.tables_bound or not snapshot.runtime_admitted)
        )
        or type(snapshot.selection_authority_bound) is not bool
        or not snapshot.selection_authority_bound
        or type(retained) is not RetainedSemanticFutureProvider
        or hasattr(retained, "__dict__")
        or retained.artifact_sha256 != digest
        or retained.provider.artifact_sha256 != digest
        or retained.source_classes is not snapshot.source_classes
        or retained.classes is not snapshot.classes
        or retained.row_signatures is not snapshot.row_signatures
        or retained.admission is not snapshot.admission
        or retained.selection_authority is not snapshot.selection_authority
        or not matches_registered_admission(snapshot.admission, digest)
        or any(type(row) is not FutureClass for row in snapshot.classes)
        or any(hasattr(row, "__dict__") for row in snapshot.classes)
        or any(
            type(row.control) is not FutureControl or hasattr(row.control, "__dict__")
            for row in snapshot.classes
        )
        or any(type(signature) is not tuple for signature in snapshot.row_signatures)
    ):
        return False

    class_count = len(snapshot.classes)
    used_classes = [False] * class_count
    for cid in snapshot.source_classes:
        if type(cid) is not int or not 0 <= cid < class_count:
            return False
        used_classes[cid] = True
    if not all(used_classes):
        return False

    for row, expected_signature in zip(
        snapshot.classes, snapshot.row_signatures, strict=True
    ):
        try:
            current_signature = class_row_signature(row)
        except (AttributeError, TypeError, ValueError):
            return False
        if not matches_scalar_signature(current_signature, expected_signature):
            return False
        control = row.control
        children = row.ordered_children
        if (
            type(control.kind) is not str
            or type(children) is not tuple
            or len(children) != 2
            or (row.rank is not None and (type(row.rank) is not int or row.rank < 0))
        ):
            return False
        if control.kind == "fork":
            if (
                type(control.fork_coefficient) is not int
                or not 2 <= control.fork_coefficient <= 9
                or any(
                    type(child) is not int or not 0 <= child < class_count
                    for child in children
                )
            ):
                return False
        elif control.kind == "landmine":
            if control.fork_coefficient is not None or children != (None, None):
                return False
        else:
            return False
    return True


def _stored_entry_is_admitted(
    digest: object,
    stored: object,
    *,
    allow_quarantined: bool,
    matches_registered_admission: Callable[[object, str], bool],
) -> bool:
    from number_compiler.sequences.comma.future_provider import SemanticFutureProvider

    if (
        type(digest) is not str
        or not valid_artifact_digest(digest)
        or not _is_dynamic_provider_entry(stored)
        or type(stored.nodes) is not int
        or stored.nodes <= 0
        or type(stored.value) is not RetainedSemanticFutureProvider
        or hasattr(stored.value, "__dict__")
        or type(stored.value.provider) is not SemanticFutureProvider
    ):
        return False
    retained = stored.value
    try:
        provider = retained.provider
        return (
            _provider_rows_are_admitted(
                provider.audit_snapshot(),
                digest,
                retained,
                matches_registered_admission,
                allow_quarantined=allow_quarantined,
            )
            and stored.nodes == provider_node_cost(digest, retained) + 1
        )
    except (
        ArithmeticError,
        AttributeError,
        IndexError,
        KeyError,
        PermissionError,
        RuntimeError,
        TypeError,
        ValueError,
    ):
        return False


def _is_dynamic_provider_entry(
    value: object,
) -> TypeGuard[DynamicMemoValue[RetainedSemanticFutureProvider]]:
    return type(value) is DynamicMemoValue


def _is_provider_ledger_dict(value: object) -> TypeGuard[LedgerDict[str, object]]:
    return type(value) is LedgerDict


def _is_provider_tracked_dict(value: object) -> TypeGuard[TrackedDict[str, object]]:
    return type(value) is TrackedDict


def audit_semantic_future_provider_store(
    ledger_value: object, root_value: object
) -> PayloadAuditContribution:
    """Validate the comma provider memo before approving its direct entries."""
    from number_compiler.sequences.comma.future_provider import (
        FUTURE_PROVIDER_STORE_ROLE,
        FUTURE_PROVIDER_WORKSPACE_ROLE,
        SemanticFutureProviderStore,
        registered_admission_metadata_matches,
    )

    if (
        type(ledger_value) is not ResourceLedger
        or type(root_value) is not SemanticFutureProviderStore
    ):
        raise TypeError("future provider payload audit needs its exact owner")
    ledger = ledger_value
    store = root_value
    state = store.audit_snapshot()
    expected_root_fields = frozenset(
        {
            "ledger",
            "owner",
            "_workspace_owner",
            "_providers",
            "_token",
            "_closed",
            "_closing",
            "_lock",
        }
    )
    expected_memo_fields = frozenset(
        {
            "ledger",
            "owner",
            "nodes_per_entry",
            "node_cost",
            "_dynamic_nodes",
            "_pending_clear_entries",
            "_pending_clear_nodes",
            "_disposed",
            "_data",
        }
    )
    if (
        type(state) is not SemanticFutureProviderStoreAuditSnapshot
        or hasattr(state, "__dict__")
        or state.ledger is not ledger
        or type(state.owner) is not int
        or type(state.workspace_owner) is not int
        or state.owner == state.workspace_owner
        or type(state.closed) is not bool
        or state.closed
        or type(state.closing) is not bool
        or type(state.root_fields) is not frozenset
        or type(state.memo_fields) is not frozenset
        or type(state.lock_valid) is not bool
        or type(state.memo_node_cost_valid) is not bool
        or state.root_fields != expected_root_fields
        or state.memo_fields != expected_memo_fields
        or not state.lock_valid
        or not state.memo_node_cost_valid
    ):
        raise ValueError("future provider store shape or lifecycle changed")

    memo = state.memo
    container = memo.container
    if (
        type(memo) is not OwnedMemoAuditSnapshot
        or memo.ledger is not ledger
        or type(memo.owner) is not int
        or memo.owner != state.owner
        or type(memo.nodes_per_entry) is not int
        or memo.nodes_per_entry != 0
        or type(memo.dynamic_cost) is not bool
        or not memo.dynamic_cost
        or type(memo.dynamic_nodes) is not int
        or memo.dynamic_nodes < 0
        or type(memo.pending_clear_entries) is not int
        or memo.pending_clear_entries != 0
        or type(memo.pending_clear_nodes) is not int
        or memo.pending_clear_nodes != 0
        or type(memo.disposed) is not bool
        or memo.disposed
        or not _is_provider_ledger_dict(container)
        or type(container.sealed) is not bool
        or not container.sealed
        or container.ledger is not ledger
        or type(container.owner) is not int
        or container.owner != state.owner
        or type(container.nodes_per_entry) is not int
        or container.nodes_per_entry != 0
        or type(container.write_once) is not bool
        or container.write_once
    ):
        raise ValueError("future provider memo lost its exact ledger binding")

    backing = container.backing_store
    if (
        not _is_provider_tracked_dict(backing)
        or not backing.belongs_to(ledger)
        or set(vars(backing)) != {"_ledger"}
    ):
        raise ValueError("future provider backing map shape changed")

    owner_status = ledger.account_status(state.owner)
    workspace_status = ledger.account_status(state.workspace_owner)
    if (
        owner_status.disposed
        or owner_status.role != FUTURE_PROVIDER_STORE_ROLE
        or type(owner_status.entries) is not int
        or type(owner_status.nodes) is not int
        or owner_status.container_identity != id(container)
        or workspace_status.disposed
        or workspace_status.role != FUTURE_PROVIDER_WORKSPACE_ROLE
        or type(workspace_status.entries) is not int
        or workspace_status.entries != 0
        or type(workspace_status.nodes) is not int
        or workspace_status.nodes < 0
        or workspace_status.container_identity is not None
    ):
        raise ValueError("future provider resource owners changed")

    approved: list[PayloadAuditEntry] = []
    invalid: list[PayloadAuditEntry] = []
    retained_nodes = 0
    rows = audit_mapping_items(container)
    for digest, stored in rows:
        if not _is_dynamic_provider_entry(stored):
            invalid.append(PayloadAuditEntry(state.owner, stored))
            continue
        if not _stored_entry_is_admitted(
            digest,
            stored,
            allow_quarantined=state.closing,
            matches_registered_admission=registered_admission_metadata_matches,
        ):
            invalid.append(PayloadAuditEntry(state.owner, stored))
            invalid.append(PayloadAuditEntry(state.owner, stored.value))
            continue
        retained_nodes += stored.nodes
        approved.append(PayloadAuditEntry(state.owner, stored))
        approved.append(PayloadAuditEntry(state.owner, stored.value))

    if memo.dynamic_nodes != retained_nodes or not ledger.matches_store_account(
        state.owner,
        container,
        FUTURE_PROVIDER_STORE_ROLE,
        entries=len(rows),
        nodes=retained_nodes,
    ):
        raise ValueError("future provider memo charges differ from its rows")
    return PayloadAuditContribution(tuple(approved), tuple(invalid))


@dataclass(frozen=True, slots=True)
class SemanticFutureProviderLease:
    """Generation-checked access to one provider retained by a ledger store."""

    _store: SemanticFutureProviderStore
    _digest: str
    _token: ArenaToken

    def __post_init__(self) -> None:
        from number_compiler.sequences.comma.future_provider import (
            SemanticFutureProviderStore,
        )

        if type(self._store) is not SemanticFutureProviderStore:
            raise TypeError("future provider lease needs its exact provider store")
        if not valid_artifact_digest(self._digest):
            raise ValueError("future provider lease needs a lowercase SHA-256")
        if type(self._token) is not ArenaToken:
            raise TypeError("future provider lease needs an exact store token")

    def resolve_provider(
        self, *, record_metrics: bool = True
    ) -> SemanticFutureProvider:
        from number_compiler.sequences.comma.future_provider import (
            SemanticFutureProviderStore,
        )

        store = getattr(self, "_store", None)
        digest = getattr(self, "_digest", None)
        token = getattr(self, "_token", None)
        if (
            type(store) is not SemanticFutureProviderStore
            or type(digest) is not str
            or not valid_artifact_digest(digest)
            or type(token) is not ArenaToken
        ):
            raise TypeError("malformed future provider lease binding")
        return SemanticFutureProviderStore.resolve_checked(
            store,
            digest,
            token,
            record_metrics=record_metrics,
        )

    @property
    def resource_ledger(self) -> ResourceLedger:
        """Inspect the exact store owner without resolving or charging a lookup."""
        from number_compiler.sequences.comma.future_provider import (
            SemanticFutureProviderStore,
        )

        store = getattr(self, "_store", None)
        if type(store) is not SemanticFutureProviderStore:
            raise TypeError("malformed future provider lease binding")
        return store.ledger

    @property
    def artifact_sha256(self) -> str:
        return self.resolve_provider().artifact_sha256

    def status_provider(self) -> SemanticFutureProvider | None:
        """Validate an already retained provider without changing work counters."""
        try:
            return self.resolve_provider(record_metrics=False)
        except (PermissionError, RuntimeError, TypeError):
            return None

    @property
    def runtime_admitted(self) -> bool:
        provider = self.status_provider()
        return provider is not None and provider.runtime_admitted

    @property
    def global_release_admitted(self) -> bool:
        provider = self.status_provider()
        return provider is not None and provider.global_release_admitted

    def matches_global_release_binding(
        self, ledger: ResourceLedger, artifact_sha256: str
    ) -> bool:
        provider = self.status_provider()
        return (
            type(ledger) is ResourceLedger
            and valid_artifact_digest(artifact_sha256)
            and provider is not None
            and provider.global_release_admitted
            and self._store.ledger is ledger
            and provider.artifact_sha256 == artifact_sha256
        )

    @property
    def class_count(self) -> int:
        return self.resolve_provider().class_count

    def require_runtime_admission(self) -> None:
        self.resolve_provider().require_runtime_admission()

    def require_global_release_admission(self) -> None:
        self.resolve_provider().require_global_release_admission()

    def source_class(
        self, source: BoundaryState, *, charge_work: Callable[[int], None]
    ) -> int:
        return self.resolve_provider().source_class(source, charge_work=charge_work)

    def class_row(self, cid: int, *, charge_work: Callable[[int], None]) -> FutureClass:
        return self.resolve_provider().class_row(cid, charge_work=charge_work)

    def select_unique_unranked_child(
        self, source: BoundaryState, *, charge_work: Callable[[int], None]
    ) -> UnrankedChildSelection:
        return self.resolve_provider().select_unique_unranked_child(
            source, charge_work=charge_work
        )


__all__ = [
    "SemanticFutureProviderAuditSnapshot",
    "SemanticFutureProviderStoreAuditSnapshot",
    "RetainedSemanticFutureProvider",
    "SemanticFutureProviderLease",
    "audit_semantic_future_provider_store",
    "candidate_workspace_cost",
    "candidate_admission_matches",
    "copy_admission_metadata",
    "admission_metadata_matches",
    "close_provider_store",
    "provider_node_cost",
    "retained_provider_entry_matches",
    "provider_audit_snapshot",
    "provider_table_bindings_match",
    "provider_store_audit_snapshot",
    "make_retained_provider_entry",
    "retained_entry_matches_provider",
    "resolve_provider_lease_locked",
]
