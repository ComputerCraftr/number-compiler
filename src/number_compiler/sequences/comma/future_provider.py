"""Bounded runtime access to an admitted semantic FutureCID table.

This module decodes a compact source-to-class map and one ordered transition
row per class.  It never constructs the semantic graph or derives a
classification from arithmetic.  Candidate JSON is untrusted input: a
private immutable registry must bind the exact canonical artifact digest to
the accepted kernel theorem before a provider is returned.  That registry is
deliberately empty today.

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

import base64
import binascii
import json
from collections.abc import Callable, Mapping
from contextlib import ExitStack
from dataclasses import dataclass, field
from functools import partial
from hashlib import sha256
from pathlib import Path
from threading import RLock
from types import MappingProxyType
from typing import Final, Literal, Self, TypeVar

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.resources.bounded_json import (
    NodeReserver,
    snapshot_canonical_json,
)
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
from number_compiler.sequences.comma import future_authority as _future_authority
from number_compiler.sequences.comma.boundary_chart import PERIOD
from number_compiler.sequences.comma.boundary_quotient import (
    BoundaryState,
    boundary_source_index,
)
from number_compiler.sequences.comma.future_authority import (
    FutureClass,
    FutureControl,
    KernelInstanceAdmission,
    _valid_artifact_digest,
    class_row_signature,
    global_release_admission_matches,
    registered_admission_matches,
)
from number_compiler.sequences.comma.future_provider_memory import (
    candidate_workspace_cost,
    provider_node_cost,
)

SOURCE_COUNT = 2 * 8 * PERIOD
FUTURE_CANDIDATE_FORMAT: Final[str] = "comma-semantic-future-candidate-v2"
FUTURE_CANDIDATE_AUTHORITY = "untrusted-source-derived-candidate"
FUTURE_PROVIDER_ASSET = "comma_semantic_future_v2.json"
FUTURE_SOURCE_UNIVERSE = "kind=N,Z; a=2..9; residue=0..923; nested-order"
FUTURE_PROVIDER_CONTRACT: Final[str] = "comma-semantic-future-provider-exact-v1"
MAX_CANDIDATE_BYTES = 2 * 1024 * 1024
MAX_CANDIDATE_JSON_DEPTH = 16
MAX_CANDIDATE_JSON_NODES = 1_048_576
MAX_CID_VARINT_BYTES = 2
_RECORD_FIELDS = frozenset(
    {
        "format",
        "authority",
        "state_universe",
        "class_of_state_varint_base64",
        "controls",
        "ordered_children",
        "class_rank_candidate",
    }
)
# Deliberately empty until the FutureCID instance has passed the Isabelle
# kernel gate and its exact artifact/theorem binding is reviewed for release.
_ADMITTED_KERNEL_INSTANCES: Mapping[str, KernelInstanceAdmission] = MappingProxyType({})


registered_global_release_artifact_sha256 = partial(
    _future_authority.registered_global_release_artifact_sha256,
    _ADMITTED_KERNEL_INSTANCES,
)


_PROVIDER_SEAL = object()
WorkCharger = Callable[[int], None]
_STORE_LOCK_TYPE = type(RLock())


@dataclass(frozen=True, slots=True)
class ParsedFutureCandidate:
    """Structurally checked candidate data with no runtime authority."""

    source_classes: tuple[int, ...]
    classes: tuple[FutureClass, ...]
    artifact_sha256: str


_Literal = TypeVar("_Literal")
_BeforeFutureParse = Callable[[Mapping[str, object]], None]
_ReserveDecodedShape = Callable[[Mapping[str, object]], None]


@dataclass(frozen=True, slots=True)
class UnrankedChildSelection:
    """Unique unranked quotient edge, without occurrence reconstruction."""

    source: BoundaryState
    source_class: int
    fork_coefficient: int
    ordered_child_classes: tuple[int, int]
    selected_slot: Literal[0, 1]

    def __post_init__(self) -> None:
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

    @property
    def selected_class(self) -> int:
        return self.ordered_child_classes[self.selected_slot]

    def select_literal(self, ordered_literals: tuple[_Literal, _Literal]) -> _Literal:
        """Select the exact caller-provided child at the checked N/Z slot."""
        if type(ordered_literals) is not tuple or len(ordered_literals) != 2:
            raise ValueError("future selection needs both ordered literal children")
        return ordered_literals[self.selected_slot]


@dataclass(frozen=True, slots=True, init=False)
class SemanticFutureProvider:
    """Immutable O(1) lookups over an admitted compact FutureCID artifact."""

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
        """Load only an artifact already registered to an accepted kernel theorem."""
        snapshot = _preflight_future_candidate(
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
        admission = _ADMITTED_KERNEL_INSTANCES.get(parsed.artifact_sha256)
        if admission is None or not _admission_matches(admission, parsed):
            raise PermissionError(
                "no kernel-admitted semantic future artifact is registered"
            )
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
        if not isinstance(path, Path):
            raise TypeError("future candidate path must be a pathlib Path")
        size = path.stat().st_size
        if size > MAX_CANDIDATE_BYTES:
            raise ValueError("future candidate exceeds the bounded input size")
        estimated_work = max(1, (size + 65_535) // 65_536)
        _charge_work(charge_work, estimated_work)
        with path.open("rb") as stream:
            payload = stream.read(MAX_CANDIDATE_BYTES + 1)
        actual_work = max(1, (len(payload) + 65_535) // 65_536)
        if actual_work > estimated_work:
            _charge_work(charge_work, actual_work - estimated_work)
        if len(payload) > MAX_CANDIDATE_BYTES:
            raise ValueError("future candidate exceeds the bounded input size")
        try:
            text = payload.decode("utf-8")
            raw = json.loads(text, object_pairs_hook=_reject_duplicate_keys)
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise ValueError("future candidate is not valid UTF-8 JSON") from exc
        except RecursionError as exc:
            raise ValueError(
                "future candidate JSON exceeds the parser nesting bound"
            ) from exc
        if type(raw) is not dict:
            raise ValueError("future candidate JSON root must be an object")
        snapshot = _preflight_future_candidate(
            raw,
            charge_work=charge_work,
            reserve_nodes=_reserve_nodes,
        )
        if payload != _canonical_json_bytes(snapshot):
            raise ValueError("future candidate JSON is not in canonical form")
        if _before_parse is not None:
            _before_parse(raw)
        if _reserve_decoded_shape is not None:
            _reserve_decoded_shape(snapshot)
        parsed = _parse_preflighted_future_candidate(
            snapshot,
            charge_work=charge_work,
            artifact_sha256=sha256(payload).hexdigest(),
        )
        return cls._from_parsed(parsed)

    @property
    def artifact_sha256(self) -> str:
        return self._digest

    @property
    def runtime_admitted(self) -> bool:
        if (
            not _valid_artifact_digest(self._digest)
            or type(self._admission) is not KernelInstanceAdmission
        ):
            return False
        admission = _ADMITTED_KERNEL_INSTANCES.get(self._digest)
        return (
            self._tables_bound()
            and type(admission) is KernelInstanceAdmission
            and admission is self._admission
            and registered_admission_matches(admission, self._digest)
        )

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

    def _tables_bound(self) -> bool:
        return (
            type(self._source_classes) is tuple
            and self._source_classes is self._source_classes_binding
            and type(self._classes) is tuple
            and self._classes is self._classes_binding
            and type(self._class_signatures) is tuple
            and self._class_signatures is self._class_signatures_binding
            and len(self._classes) == len(self._class_signatures)
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
        self.owner = ledger.register(owner_name, "semantic_future_provider")
        self._workspace_owner = ledger.register(
            workspace_name,
            "semantic_future_provider_workspace",
        )
        self._providers: OwnedMemo[str, SemanticFutureProvider] = OwnedMemo(
            ledger, self.owner, node_cost=provider_node_cost
        )
        self._token = ArenaToken("comma-semantic-future-provider")
        self._closed = False
        self._lock = RLock()
        ledger.register_execution_root(self)

    def _check_open(self) -> None:
        if self._closed:
            raise RuntimeError("future provider store has been closed")

    def _retain(
        self,
        provider: SemanticFutureProvider,
        reservation: LedgerReservation,
    ) -> SemanticFutureProviderLease:
        self._check_open()
        provider.require_runtime_admission()
        digest = provider.artifact_sha256
        retained = self._providers.get(digest)
        if retained is None:
            # The retained key becomes one live cache entry. Reserve that
            # exact entry only after the absent-digest branch is known.
            reservation.reserve(entries=1)
            self._providers.adopt_reserved(digest, provider, reservation)
            try:
                self.ledger.bump(_comma_keys.COMMA_FUTURE_PROVIDER_PUBLICATIONS)
            except BaseException:
                del self._providers[digest]
                raise
        else:
            retained.require_runtime_admission()
            self.ledger.bump(_comma_keys.COMMA_FUTURE_PROVIDER_SEMANTIC_REUSES)
        return SemanticFutureProviderLease(self, digest, self._token)

    def _load_provider(
        self,
        loader: _FutureProviderLoader,
        charge_work: WorkCharger,
    ) -> SemanticFutureProviderLease:
        with self._lock:
            self._check_open()
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
        with self._lock:
            self._check_open()
            self.ledger.bump(_comma_keys.COMMA_FUTURE_PROVIDER_LOOKUPS)
            if not _valid_artifact_digest(artifact_sha256):
                self.ledger.bump(_comma_keys.COMMA_FUTURE_PROVIDER_LOOKUP_REFUSALS)
                raise ValueError("future artifact lookup needs a lowercase SHA-256")
            provider = self._providers.get(artifact_sha256)
            if provider is None:
                self.ledger.bump(_comma_keys.COMMA_FUTURE_PROVIDER_LOOKUP_MISSES)
                raise KeyError("future artifact has not been loaded into this ledger")
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
        lock = getattr(self, "_lock", None)
        if lock is None or type(lock) is not _STORE_LOCK_TYPE:
            raise RuntimeError("malformed future provider store")
        with lock:
            ledger = getattr(self, "ledger", None)
            closed = getattr(self, "_closed", None)
            current_token = getattr(self, "_token", None)
            if (
                type(ledger) is not ResourceLedger
                or type(closed) is not bool
                or type(current_token) is not ArenaToken
            ):
                raise RuntimeError("malformed future provider store")
            if (
                closed
                or type(digest) is not str
                or not _valid_artifact_digest(digest)
                or type(token) is not ArenaToken
                or token is not current_token
            ):
                if record_metrics:
                    ledger.bump(_comma_keys.COMMA_FUTURE_PROVIDER_STALE_LEASE_REFUSALS)
                raise RuntimeError("future provider lease is stale")
            memo = getattr(self, "_providers", None)
            owner = getattr(self, "owner", None)
            if (
                type(memo) is not OwnedMemo
                or memo.ledger is not ledger
                or memo.owner != owner
            ):
                raise RuntimeError("future provider store has a foreign retained table")
            provider = memo.get(digest)
            if provider is None:
                if record_metrics:
                    ledger.bump(_comma_keys.COMMA_FUTURE_PROVIDER_LEASE_MISSES)
                raise RuntimeError("future provider is no longer retained")
            if type(provider) is not SemanticFutureProvider:
                raise RuntimeError("future provider store retained a foreign provider")
            provider.require_runtime_admission()
            if record_metrics:
                ledger.bump(_comma_keys.COMMA_FUTURE_PROVIDER_LEASE_RESOLUTIONS)
            return provider

    def reset(self) -> None:
        """Release retained candidates and revoke leases without closing owner."""
        with self._lock:
            self._check_open()
            self._providers.clear()
            self._token = ArenaToken("comma-semantic-future-provider")
            self.ledger.bump(_comma_keys.COMMA_FUTURE_PROVIDER_RESETS)

    def close(self) -> None:
        """Drop retained tables and invalidate every lease; safe to call twice."""
        with self._lock:
            if self._closed:
                return
            self._providers.dispose()
            self._token = ArenaToken("comma-semantic-future-provider")
            self._closed = True
            self.ledger.bump(_comma_keys.COMMA_FUTURE_PROVIDER_CLOSES)

    def __enter__(self) -> Self:
        with self._lock:
            self._check_open()
            return self

    def __exit__(self, exc_type: object, exc: object, traceback: object) -> None:
        self.close()


@dataclass(frozen=True, slots=True)
class SemanticFutureProviderLease:
    """Generation-checked access to one provider retained by a ledger store."""

    _store: SemanticFutureProviderStore
    _digest: str
    _token: ArenaToken

    def __post_init__(self) -> None:
        if type(self._store) is not SemanticFutureProviderStore:
            raise TypeError("future provider lease needs its exact provider store")
        if not _valid_artifact_digest(self._digest):
            raise ValueError("future provider lease needs a lowercase SHA-256")
        if type(self._token) is not ArenaToken:
            raise TypeError("future provider lease needs an exact store token")

    def resolve_provider(
        self, *, record_metrics: bool = True
    ) -> SemanticFutureProvider:
        store = getattr(self, "_store", None)
        digest = getattr(self, "_digest", None)
        token = getattr(self, "_token", None)
        if (
            type(store) is not SemanticFutureProviderStore
            or type(digest) is not str
            or not _valid_artifact_digest(digest)
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
            and _valid_artifact_digest(artifact_sha256)
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

    def source_class(self, source: BoundaryState, *, charge_work: WorkCharger) -> int:
        return self.resolve_provider().source_class(source, charge_work=charge_work)

    def class_row(self, cid: int, *, charge_work: WorkCharger) -> FutureClass:
        return self.resolve_provider().class_row(cid, charge_work=charge_work)

    def select_unique_unranked_child(
        self, source: BoundaryState, *, charge_work: WorkCharger
    ) -> UnrankedChildSelection:
        return self.resolve_provider().select_unique_unranked_child(
            source, charge_work=charge_work
        )


def parse_future_candidate(
    record: Mapping[str, object], *, charge_work: WorkCharger
) -> ParsedFutureCandidate:
    """Check bounded JSON structure without granting provider authority."""
    snapshot = _preflight_future_candidate(record, charge_work=charge_work)
    return _parse_preflighted_future_candidate(snapshot, charge_work=charge_work)


def _parse_preflighted_future_candidate(
    record: Mapping[str, object],
    *,
    charge_work: WorkCharger,
    artifact_sha256: str | None = None,
) -> ParsedFutureCandidate:
    """Decode a record after its JSON shape and serialized size were bounded."""
    source_classes, classes = _validate_record(record, charge_work=charge_work)
    digest = (
        _future_candidate_sha256(record) if artifact_sha256 is None else artifact_sha256
    )
    return ParsedFutureCandidate(
        source_classes,
        classes,
        digest,
    )


def _preflight_future_candidate(
    record: Mapping[str, object],
    *,
    charge_work: WorkCharger,
    reserve_nodes: NodeReserver | None = None,
) -> dict[str, object]:
    """Snapshot the input under the FutureCID JSON and resource limits."""
    return snapshot_canonical_json(
        record,
        max_bytes=MAX_CANDIDATE_BYTES,
        max_depth=MAX_CANDIDATE_JSON_DEPTH,
        max_nodes=MAX_CANDIDATE_JSON_NODES,
        charge_work=charge_work,
        reserve_nodes=reserve_nodes,
    )


def _future_candidate_sha256(record: Mapping[str, object]) -> str:
    """Hash a record after its caller has charged bounded structural parsing."""
    if type(record) not in (dict, MappingProxyType) or any(
        type(key) is not str for key in record
    ):
        raise TypeError("future candidate must be a string-keyed mapping")
    canonical_record = dict(record) if type(record) is MappingProxyType else record
    return sha256(_canonical_json_bytes(canonical_record)).hexdigest()


def _canonical_json_bytes(record: Mapping[str, object]) -> bytes:
    try:
        text = json.dumps(
            record,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
            allow_nan=False,
        )
    except (TypeError, ValueError) as exc:
        raise ValueError("future candidate contains non-JSON data") from exc
    return (text + "\n").encode("ascii")


def _charge_work(charge_work: WorkCharger, amount: int) -> None:
    if not callable(charge_work):
        raise TypeError("future provider operation requires a work charger")
    if type(amount) is not int or amount <= 0:
        raise ValueError("future provider work charge must be positive")
    charge_work(amount)


def _reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate future candidate JSON key")
        result[key] = value
    return result


def _admission_matches(
    admission: KernelInstanceAdmission, parsed: ParsedFutureCandidate
) -> bool:
    return registered_admission_matches(admission, parsed.artifact_sha256)


def _validate_record(
    record: Mapping[str, object],
    *,
    charge_work: WorkCharger,
) -> tuple[tuple[int, ...], tuple[FutureClass, ...]]:
    if not isinstance(record, Mapping) or any(type(key) is not str for key in record):
        raise TypeError("future candidate must be a string-keyed object")
    if set(record) != _RECORD_FIELDS:
        raise ValueError("future candidate fields differ from the supported schema")
    if record.get("format") != FUTURE_CANDIDATE_FORMAT:
        raise ValueError("unsupported semantic future candidate version")
    if record.get("authority") != FUTURE_CANDIDATE_AUTHORITY:
        raise ValueError("future candidate producer authority marker is unsupported")
    if record.get("state_universe") != FUTURE_SOURCE_UNIVERSE:
        raise ValueError("future candidate source universe differs from the contract")

    encoded_map = record.get("class_of_state_varint_base64")
    if type(encoded_map) is not str or len(encoded_map) > 4 * (
        (SOURCE_COUNT * 2 + 2) // 3
    ):
        raise ValueError("future source map has an invalid bounded encoding")
    try:
        encoded_bytes = encoded_map.encode("ascii")
        decoded = base64.b64decode(encoded_bytes, validate=True)
    except (UnicodeEncodeError, binascii.Error) as exc:
        raise ValueError("future source map is not valid base64") from exc
    if base64.b64encode(decoded).decode("ascii") != encoded_map:
        raise ValueError("future source map base64 is not canonical")

    raw_controls = record.get("controls")
    raw_children = record.get("ordered_children")
    raw_ranks = record.get("class_rank_candidate")
    if not isinstance(raw_controls, list) or not isinstance(raw_children, list):
        raise TypeError("future controls and ordered children must be arrays")
    if not isinstance(raw_ranks, list):
        raise TypeError("future candidate ranks must be an array")
    class_count = len(raw_controls)
    if not 0 < class_count <= SOURCE_COUNT:
        raise ValueError("future class table has an invalid bounded size")
    if len(raw_children) != class_count or len(raw_ranks) != class_count:
        raise ValueError("future class controls, children, and ranks differ in size")
    _charge_work(charge_work, SOURCE_COUNT + 3 * class_count)
    class_ids = _decode_class_map(decoded, class_count)
    classes = _decode_class_rows(raw_controls, raw_children, raw_ranks, class_count)
    if set(class_ids) != set(range(class_count)):
        raise ValueError("future source map has missing or unused class identifiers")

    return class_ids, classes


def _decode_class_map(payload: bytes, class_count: int) -> tuple[int, ...]:
    if type(payload) is not bytes or len(payload) > SOURCE_COUNT * MAX_CID_VARINT_BYTES:
        raise ValueError("future source map exceeds its bounded varint payload")
    values: list[int] = []
    current = 0
    shift = 0
    width = 0
    for byte in payload:
        width += 1
        if width > MAX_CID_VARINT_BYTES:
            raise ValueError("future source map contains an oversized CID varint")
        current |= (byte & 0x7F) << shift
        if byte & 0x80:
            shift += 7
            continue
        if current >= class_count:
            raise ValueError("future source map contains an out-of-range CID")
        if width > 1 and current < (1 << (7 * (width - 1))):
            raise ValueError("future source map contains a noncanonical CID varint")
        values.append(current)
        if len(values) > SOURCE_COUNT:
            raise ValueError("future source map has too many source entries")
        current = 0
        shift = 0
        width = 0
    if width:
        raise ValueError("future source map ends with a truncated CID varint")
    if len(values) != SOURCE_COUNT:
        raise ValueError("future source map is truncated or has extra source entries")
    return tuple(values)


def _decode_class_rows(
    raw_controls: list[object],
    raw_children: list[object],
    raw_ranks: list[object],
    class_count: int,
) -> tuple[FutureClass, ...]:
    result: list[FutureClass] = []
    for raw_control, raw_row, raw_rank in zip(
        raw_controls, raw_children, raw_ranks, strict=True
    ):
        if not isinstance(raw_control, list) or len(raw_control) != 2:
            raise ValueError("future class control is malformed")
        kind, coefficient = raw_control
        if kind == "fork":
            if type(coefficient) is not int or not 2 <= coefficient <= 9:
                raise ValueError("future Fork control needs its exact coefficient")
            control = FutureControl("fork", coefficient)
        elif kind == "landmine":
            if coefficient is not None:
                raise ValueError("future Landmine control cannot carry a coefficient")
            control = FutureControl("landmine", coefficient)
        else:
            raise ValueError("future class control is neither Fork nor Landmine")
        if not isinstance(raw_row, list) or len(raw_row) != 2:
            raise ValueError("future class row must preserve two ordered slots")
        children: list[int | None] = []
        for target in raw_row:
            if target is None:
                children.append(None)
            elif type(target) is int and 0 <= target < class_count:
                children.append(target)
            else:
                raise ValueError("future ordered child leaves the class table")
        if control.kind == "landmine" and children != [None, None]:
            raise ValueError("future Landmine row carries child edges")
        if control.kind == "fork" and any(child is None for child in children):
            raise ValueError("future Fork row lost an ordered child")
        if raw_rank is None:
            rank = None
        elif type(raw_rank) is int and raw_rank >= 0:
            rank = raw_rank
        else:
            raise ValueError("future rank must be a nonnegative integer or null")
        result.append(FutureClass(control, (children[0], children[1]), rank))
    return tuple(result)


__all__ = [
    "FUTURE_CANDIDATE_FORMAT",
    "FUTURE_PROVIDER_CONTRACT",
    "FutureClass",
    "FutureControl",
    "ParsedFutureCandidate",
    "SemanticFutureProvider",
    "SemanticFutureProviderLease",
    "SemanticFutureProviderStore",
    "UnrankedChildSelection",
    "parse_future_candidate",
]
