"""Per-index resource ownership and atomic, pre-insertion budget accounting."""

from __future__ import annotations

from collections.abc import Callable, Generator, Iterable, Iterator, Sized
from contextlib import contextmanager
from dataclasses import dataclass, field
from weakref import ReferenceType, ref

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle
from number_compiler.resources.factory_containers import (
    ContainerItemT as _StoreT,
)
from number_compiler.resources.factory_containers import (
    ContainerKeyT as _StoreK,
)
from number_compiler.resources.factory_containers import (
    ContainerValueT as _StoreV,
)
from number_compiler.resources.factory_containers import (
    FactoryContainerRegistry,
)
from number_compiler.resources.ledger_records import (
    LedgerAccountStatus as LedgerAccountStatus,
)
from number_compiler.resources.ledger_records import LedgerSnapshot as LedgerSnapshot
from number_compiler.resources.ledger_records import (
    ResourceInventory as ResourceInventory,
)
from number_compiler.resources.ledger_records import ResourceScope as ResourceScope
from number_compiler.resources.metric_keys import resources as _resources_keys
from number_compiler.resources.owned_memo import (
    LedgerReservation,
    OwnedMemo,
)
from number_compiler.resources.payload_contracts import (
    PayloadAuditBinding,
    PayloadAuditContractAudit,
    PayloadAuditContribution,
    PayloadAuditStoreBinding,
    PayloadContractRegistry,
    audit_payload_contracts,
    clear_payload_audit_contracts,
    drop_owner_contracts,
    drop_root_contracts,
    register_payload_audit_contract,
    remove_payload_audit_contract,
)
from number_compiler.resources.root_audit_signature import root_audit_signature
from number_compiler.resources.stores import LedgerDict, LedgerList, TrackedDict

__all__ = ("LedgerReservation", "OwnedMemo")


def _empty_root_map() -> dict[ArenaHandle, None]:
    return {}


@dataclass(slots=True)
class _Account:
    name: str
    role: str
    scope: ResourceScope
    entries: int = 0
    nodes: int = 0
    roots: dict[ArenaHandle, None] = field(default_factory=_empty_root_map)
    container: Sized | None = None
    node_count: Callable[[], int] | None = None
    payloads: Callable[[], Iterable[object]] | None = None
    root_resolver: Callable[[], Iterable[object]] | None = None
    evict: Callable[[], None] | None = None
    composition_count: Callable[[], int] | None = None
    disposed: bool = False


class ResourceLedger(PayloadContractRegistry):
    """Reserve before publishing an allocation; rejected reservations mutate nothing.

    Nodes and cache entries are separate resource dimensions. Registering a root
    describes reachability and does not charge it again. Each allocation must
    have exactly one account even when multiple roots refer to it.
    """

    def __init__(
        self, max_nodes: int | None = None, max_cache_entries: int | None = None
    ) -> None:
        self._validate_limits(max_nodes, max_cache_entries)
        self.max_nodes = max_nodes
        self.max_cache_entries = max_cache_entries
        self.counters: dict[str, int] = {}
        self._accounts: list[_Account] = []
        self._names: dict[str, int] = {}
        self._reservations: TrackedDict[object, tuple[int, int, int]] = TrackedDict(
            self
        )
        self._factory_containers = FactoryContainerRegistry()
        self._execution_roots: dict[int, ReferenceType[object]] = {}
        self._payload_audit_contracts: dict[tuple[int, str], PayloadAuditBinding] = {}
        self._payload_audit_snapshot: PayloadAuditContractAudit | None = None
        self.entries = 0
        self.nodes = 0
        self.peak_entries = 0
        self.peak_nodes = 0
        self._mutation_version = 0
        self._payload_audit_cache: tuple[int, object | None, object] | None = None
        self._ownership_audit_cache: tuple[int, object | None, object] | None = None

    @property
    def mutation_version(self) -> int:
        """Monotonic retained-store version used by read-only audit caches."""
        return self._mutation_version

    @property
    def owner_count(self) -> int:
        """Return the registered-owner count without constructing an inventory."""
        return len(self._accounts)

    def require_fresh_owner_names(self, names: tuple[str, ...]) -> None:
        """Validate a small owner-name batch before any owner is registered."""
        if type(names) is not tuple:
            raise TypeError("resource owner names must be a tuple")
        seen: set[str] = set()
        for name in names:
            if type(name) is not str:
                raise TypeError("resource names must be strings")
            if not name:
                raise ValueError("resource names must be nonempty")
            if name in seen:
                raise ValueError("resource owner names must be distinct")
            if name in self._names:
                raise ValueError("resource owner name is already registered")
            seen.add(name)

    def note_store_mutation(self) -> None:
        """Invalidate cached object-graph evidence after an actual store change."""
        self._mutation_version += 1
        self._payload_audit_snapshot = None
        self._payload_audit_cache = None
        self._ownership_audit_cache = None

    def audit_root_signature(
        self,
    ) -> tuple[tuple[int, tuple[tuple[str, int, int | None], ...]], ...]:
        """Return a shallow live-root signature without walking retained DAGs."""
        return root_audit_signature(self.iter_execution_roots())

    def _cached_audit(
        self, cached: tuple[int, object, object] | None, root_signature: object | None
    ) -> object | None:
        if cached is None or cached[0] != self._mutation_version:
            return None
        if root_signature is not None and cached[1] != root_signature:
            return None
        return cached[2]

    def cached_payload_audit(
        self, root_signature: object | None = None
    ) -> object | None:
        cached = self._payload_audit_cache
        return self._cached_audit(cached, root_signature)

    def cache_payload_audit(
        self,
        version: int,
        audit: object,
        root_signature: object | None = None,
    ) -> None:
        if type(version) is not int or version != self._mutation_version:
            return
        self._payload_audit_cache = (version, root_signature, audit)

    def cached_ownership_audit(
        self, root_signature: object | None = None
    ) -> object | None:
        cached = self._ownership_audit_cache
        return self._cached_audit(cached, root_signature)

    def cache_ownership_audit(
        self,
        version: int,
        audit: object,
        root_signature: object | None = None,
    ) -> None:
        if type(version) is not int or version != self._mutation_version:
            return
        self._ownership_audit_cache = (version, root_signature, audit)

    def register_execution_root(self, root: object) -> None:
        """Weakly track actual execution owners, independently of cache callbacks."""
        identity = id(root)
        if (
            identity in self._execution_roots
            and self._execution_roots[identity]() is root
        ):
            return

        def expire(reference: ReferenceType[object]) -> None:
            self.expire_execution_root(identity, reference)

        reference = ref(root, expire)
        from number_compiler.resources.construction_scope import (
            forget_construction_root,
            record_construction_root,
        )

        previous = self._execution_roots.get(identity)
        record_construction_root(self, identity, reference)
        try:
            self._execution_roots[identity] = reference
        except BaseException:
            if self._execution_roots.get(identity) is reference:
                if previous is None:
                    self._execution_roots.pop(identity, None)
                else:
                    self._execution_roots[identity] = previous
            forget_construction_root(self, identity, reference)
            raise
        self.note_store_mutation()

    def owns_execution_root(self, root: object) -> bool:
        """Check exact weak-root registration without exposing the root map."""
        reference = self._execution_roots.get(id(root))
        return reference is not None and reference() is root

    def expire_execution_root(
        self,
        identity: int,
        expected: ReferenceType[object] | None = None,
    ) -> None:
        current = self._execution_roots.get(identity)
        if expected is not None and current is not expected:
            return
        self._execution_roots.pop(identity, None)
        drop_root_contracts(self, identity)
        self.note_store_mutation()

    def retire_unpublished_owner(self, owner: int) -> None:
        """Release a newly created owner after its enclosing construction fails."""
        account = self._account(owner)
        if account.disposed:
            return
        entries, nodes = account.entries, account.nodes
        container = account.container
        container_identity = None if container is None else id(container)
        if isinstance(container, (LedgerDict, LedgerList)):
            container.clear_unpublished_storage()
        self.release(owner, entries, nodes)
        self.bump(_resources_keys.RUNTIME_CONSTRUCTION_RELEASED_ENTRIES, entries)
        self.bump(_resources_keys.RUNTIME_CONSTRUCTION_RELEASED_NODES, nodes)
        if container_identity is not None:
            self._factory_containers.discard(container_identity)
        account.container = None
        account.node_count = account.payloads = account.root_resolver = None
        account.evict = account.composition_count = None
        account.roots.clear()
        self.mark_disposed(owner)

    def register_payload_audit_contract(
        self,
        root: object,
        family: str,
        stores: tuple[PayloadAuditStoreBinding, ...],
        validator: Callable[[object, object], PayloadAuditContribution],
        *,
        dependencies: tuple[object, ...] = (),
    ) -> None:
        register_payload_audit_contract(
            self, root, family, stores, validator, dependencies=dependencies
        )

    def remove_payload_audit_contract(
        self, root: object, family: str | None = None
    ) -> None:
        remove_payload_audit_contract(self, root, family)

    def clear_payload_audit_contracts(self) -> None:
        clear_payload_audit_contracts(self)

    def audit_payload_contracts(self) -> PayloadAuditContractAudit:
        return audit_payload_contracts(self)

    def tighten_limits(
        self, max_nodes: int | None, max_cache_entries: int | None
    ) -> None:
        """Honor explicit index limits even when it receives an existing ledger."""
        self._validate_limits(max_nodes, max_cache_entries)
        self._validate_limits(self.max_nodes, self.max_cache_entries)
        nodes = (
            self.max_nodes
            if max_nodes is None
            else (
                max_nodes if self.max_nodes is None else min(max_nodes, self.max_nodes)
            )
        )
        entries = (
            self.max_cache_entries
            if max_cache_entries is None
            else (
                max_cache_entries
                if self.max_cache_entries is None
                else min(max_cache_entries, self.max_cache_entries)
            )
        )
        if (
            nodes is not None
            and self.nodes > nodes
            or entries is not None
            and self.entries > entries
        ):
            raise BlockContextBudgetExceeded(
                "existing resources exceed requested index limits"
            )
        self.max_nodes, self.max_cache_entries = nodes, entries

    @staticmethod
    def _validate_limits(max_nodes: int | None, max_cache_entries: int | None) -> None:
        if (max_nodes is None or (type(max_nodes) is int and max_nodes >= 0)) and (
            max_cache_entries is None
            or (type(max_cache_entries) is int and max_cache_entries >= 0)
        ):
            return
        if max_nodes is not None:
            require_integer(max_nodes, "node budget", 0)
        if max_cache_entries is not None:
            require_integer(max_cache_entries, "cache budget", 0)

    @staticmethod
    def _validate_quantities(entries: int, nodes: int) -> None:
        if type(entries) is int and entries >= 0 and type(nodes) is int and nodes >= 0:
            return
        require_integer(entries, "cache entry count", 0)
        require_integer(nodes, "node count", 0)

    def iter_execution_roots(self) -> Iterator[object]:
        expired: list[tuple[int, ReferenceType[object]]] = []
        roots: list[object] = []
        for identity, reference in tuple(self._execution_roots.items()):
            root = reference()
            if root is None:
                expired.append((identity, reference))
            else:
                roots.append(root)
        if expired:
            removed = False
            for identity, reference in expired:
                if self._execution_roots.get(identity) is reference:
                    self._execution_roots.pop(identity, None)
                    drop_root_contracts(self, identity)
                    removed = True
            if removed:
                self.note_store_mutation()
        yield from roots

    def register(
        self, name: str, role: str, scope: ResourceScope = ResourceScope.ENGINE_OWNED
    ) -> int:
        if type(name) is not str or type(role) is not str:
            raise TypeError("resource name and role must be strings")
        if not name or not role:
            raise ValueError("resource name and role must be nonempty")
        if type(scope) is not ResourceScope:
            raise TypeError("resource scope must be a ResourceScope")
        found = self._names.get(name)
        if found is not None:
            previous = self._accounts[found]
            if previous.role != role or previous.scope != scope:
                raise ValueError(
                    "resource name already registered with another role or scope"
                )
            return found
        owner = len(self._accounts)
        from number_compiler.resources.construction_scope import (
            forget_construction_owner,
            record_construction_owner,
        )

        record_construction_owner(self, owner)
        try:
            self._accounts.append(_Account(name, role, scope))
            try:
                self._names[name] = owner
            except BaseException:
                self._accounts.pop()
                raise
        except BaseException:
            forget_construction_owner(self, owner)
            raise
        return owner

    def _account(self, owner: int) -> _Account:
        if type(owner) is not int or owner < 0 or owner >= len(self._accounts):
            raise ValueError("unregistered resource owner")
        return self._accounts[owner]

    def reserve(self, owner: int, entries: int = 0, nodes: int = 0) -> None:
        # Most publications charge exactly one owner. Keep this path free of
        # the batch staging list while preserving reserve_many's validation
        # order for the single tuple: limits, owner, disposal, quantities,
        # then capacity.
        self._validate_limits(self.max_nodes, self.max_cache_entries)
        account = self._account(owner)
        if account.disposed:
            raise RuntimeError("resource owner has been disposed")
        self._validate_quantities(entries, nodes)
        next_entries = self.entries + entries
        next_nodes = self.nodes + nodes
        self._check_capacity_totals(next_entries, next_nodes)
        account.entries += entries
        account.nodes += nodes
        self._commit_reserved_totals(next_entries, next_nodes)

    def register_reservation(self, reservation: object, owner: int) -> None:
        if type(reservation) is not LedgerReservation:
            raise TypeError("resource reservation needs its exact tracker")
        if reservation in self._reservations:
            raise ValueError("resource reservation is already registered")
        account = self._account(owner)
        if account.disposed:
            raise RuntimeError("resource owner has been disposed")
        self._reservations[reservation] = (owner, 0, 0)

    def _reservation_state(self, reservation: object) -> tuple[int, int, int]:
        if type(reservation) is not LedgerReservation:
            raise TypeError("resource reservation needs its exact tracker")
        state = self._reservations.get(reservation)
        if state is None:
            raise RuntimeError("ledger reservation has been closed or is foreign")
        return state

    def validate_reservation(self, reservation: object) -> None:
        """Confirm a tracker remains open without exposing held charges."""
        self._reservation_state(reservation)

    def reserve_for_reservation(
        self, reservation: object, *, entries: int = 0, nodes: int = 0
    ) -> None:
        owner, held_entries, held_nodes = self._reservation_state(reservation)
        next_state = (
            owner,
            held_entries + entries,
            held_nodes + nodes,
        )
        self.reserve(owner, entries=entries, nodes=nodes)
        self._reservations[reservation] = next_state

    def transfer_reservation_to(
        self,
        reservation: object,
        owner: int,
        *,
        entries: int = 0,
        nodes: int = 0,
    ) -> None:
        source, held_entries, held_nodes = self._reservation_state(reservation)
        self._validate_quantities(entries, nodes)
        if source == owner:
            raise ValueError("reservation transfer needs a different owner")
        if entries > held_entries or nodes > held_nodes:
            raise ValueError("transfer exceeds this reservation's live charges")
        next_state = (source, held_entries - entries, held_nodes - nodes)
        self.reassign_many(((source, entries, nodes),), ((owner, entries, nodes),))
        self._reservations[reservation] = next_state

    def transfer_reservation_from(
        self,
        reservation: object,
        owner: int,
        *,
        entries: int = 0,
        nodes: int = 0,
    ) -> None:
        target, held_entries, held_nodes = self._reservation_state(reservation)
        self._validate_quantities(entries, nodes)
        if target == owner:
            raise ValueError("reservation transfer needs a different owner")
        next_state = (target, held_entries + entries, held_nodes + nodes)
        self.reassign_many(((owner, entries, nodes),), ((target, entries, nodes),))
        self._reservations[reservation] = next_state

    def close_reservation(self, reservation: object) -> None:
        if type(reservation) is not LedgerReservation:
            raise TypeError("resource reservation needs its exact tracker")
        if not reservation.belongs_to(self):
            raise ValueError("cannot close a reservation from another ledger")
        state = self._reservations.get(reservation)
        if state is None:
            return
        owner, entries, nodes = state
        self.release(owner, entries=entries, nodes=nodes)
        del self._reservations[reservation]

    @contextmanager
    def reservation(
        self, owner: int, *, entries: int = 0, nodes: int = 0
    ) -> Generator[None, None, None]:
        """Temporarily reserve capacity on an existing owner, without retiring it.

        The body must drop any storage using this capacity before exit. Failed
        admission acquires nothing; nested scopes release only their own charge.
        """
        self.reserve(owner, entries=entries, nodes=nodes)
        try:
            yield
        finally:
            self.release(owner, entries=entries, nodes=nodes)

    def check_store_capacity(self, owner: int, entries: int, nodes: int) -> None:
        """Enforce pre-publication reservations at the actual store boundary."""
        self._validate_quantities(entries, nodes)
        account = self._account(owner)
        if account.disposed:
            raise RuntimeError("resource owner has been disposed")
        if entries > account.entries or nodes > account.nodes:
            raise RuntimeError(
                "retained store insertion requires a prior ledger reservation"
            )

    def make_dict(
        self,
        owner: int,
        *,
        nodes_per_entry: int = 0,
        write_once: bool = False,
        key_type: type[_StoreK] | None = None,
        value_type: type[_StoreV] | None = None,
    ) -> LedgerDict[_StoreK, _StoreV]:
        """Create a typed, ledger-accounted map."""
        return self._factory_containers.make_dict(
            self,
            owner,
            nodes_per_entry=nodes_per_entry,
            write_once=write_once,
            key_type=key_type,
            value_type=value_type,
        )

    def make_list(
        self,
        owner: int,
        *,
        nodes_per_entry: int = 1,
        append_only: bool = True,
        item_type: type[_StoreT] | None = None,
    ) -> LedgerList[_StoreT]:
        """Create a typed, ledger-accounted sequence store."""
        return self._factory_containers.make_list(
            self,
            owner,
            nodes_per_entry=nodes_per_entry,
            append_only=append_only,
            item_type=item_type,
        )

    def is_factory_container(self, container: object) -> bool:
        """Identity provenance; registered containers stay live with this ledger."""
        return self._factory_containers.contains(container)

    def check_capacity(self, *, entries: int = 0, nodes: int = 0) -> None:
        """Check a required allocation before constructing any dependent store."""
        self._validate_limits(self.max_nodes, self.max_cache_entries)
        self._validate_quantities(entries, nodes)
        next_entries = self.entries + entries
        next_nodes = self.nodes + nodes
        self._check_capacity_totals(next_entries, next_nodes)

    def _check_capacity_totals(self, next_entries: int, next_nodes: int) -> None:
        if self.max_cache_entries is not None and next_entries > self.max_cache_entries:
            raise BlockContextBudgetExceeded(
                f"cache budget exceeded before allocation: {next_entries} > {self.max_cache_entries}"
            )
        if self.max_nodes is not None and next_nodes > self.max_nodes:
            raise BlockContextBudgetExceeded(
                f"node budget exceeded before allocation: {next_nodes} > {self.max_nodes}"
            )

    def reserve_many(self, reservations: Iterable[tuple[int, int, int]]) -> None:
        """Reserve a publication spanning several owners as one atomic unit."""
        self._validate_limits(self.max_nodes, self.max_cache_entries)
        pending: list[tuple[_Account, int, int]] = []
        entries = nodes = 0
        for owner, entry_count, node_count in reservations:
            account = self._account(owner)
            if account.disposed:
                raise RuntimeError("resource owner has been disposed")
            self._validate_quantities(entry_count, node_count)
            pending.append((account, entry_count, node_count))
            entries += entry_count
            nodes += node_count
        next_entries = self.entries + entries
        next_nodes = self.nodes + nodes
        # Keep the public validation pass after iteration: arbitrary iterables
        # may tighten or corrupt mutable ledger limits while yielding items.
        self.check_capacity(entries=entries, nodes=nodes)
        for account, _, _ in pending:
            if account.disposed:
                raise RuntimeError("resource owner has been disposed")
        for account, entry_count, node_count in pending:
            account.entries += entry_count
            account.nodes += node_count
        self._commit_reserved_totals(next_entries, next_nodes)

    def _commit_reserved_totals(self, entries: int, nodes: int) -> None:
        self.entries = entries
        self.nodes = nodes
        self.peak_entries = max(self.peak_entries, entries)
        self.peak_nodes = max(self.peak_nodes, nodes)

    def reassign_many(
        self,
        releases: Iterable[tuple[int, int, int]],
        reservations: Iterable[tuple[int, int, int]],
    ) -> None:
        """Atomically move charged resources between ownership scopes.

        Construction workspaces use this operation when their already charged
        nodes become canonical retained nodes.  Capacity is checked against the
        net change, so one object is never temporarily counted as both transient
        and retained.  No account changes when validation or capacity checking
        fails.
        """
        self._validate_limits(self.max_nodes, self.max_cache_entries)
        released: dict[int, tuple[_Account, int, int]] = {}
        reserved: dict[int, tuple[_Account, int, int]] = {}
        for source, target in ((releases, released), (reservations, reserved)):
            for owner, entry_count, node_count in source:
                account = self._account(owner)
                if account.disposed:
                    raise RuntimeError("resource owner has been disposed")
                self._validate_quantities(entry_count, node_count)
                previous = target.get(owner)
                entries = entry_count + (0 if previous is None else previous[1])
                nodes = node_count + (0 if previous is None else previous[2])
                target[owner] = account, entries, nodes
        # These iterables can execute arbitrary code while yielding. Recheck
        # mutable budgets and every staged owner before changing any account.
        self._validate_limits(self.max_nodes, self.max_cache_entries)
        disposed_release = any(account.disposed for account, _, _ in released.values())
        disposed_reservation = any(
            account.disposed for account, _, _ in reserved.values()
        )
        if disposed_release or disposed_reservation:
            raise RuntimeError("resource owner has been disposed")
        for account, entries, nodes in released.values():
            if entries > account.entries or nodes > account.nodes:
                raise ValueError("reassignment release exceeds the owner's reservation")
        released_entries = sum(item[1] for item in released.values())
        released_nodes = sum(item[2] for item in released.values())
        reserved_entries = sum(item[1] for item in reserved.values())
        reserved_nodes = sum(item[2] for item in reserved.values())
        next_entries = self.entries - released_entries + reserved_entries
        next_nodes = self.nodes - released_nodes + reserved_nodes
        self._check_capacity_totals(next_entries, next_nodes)
        for account, entries, nodes in released.values():
            account.entries -= entries
            account.nodes -= nodes
        for account, entries, nodes in reserved.values():
            account.entries += entries
            account.nodes += nodes
        self._commit_reserved_totals(next_entries, next_nodes)

    def release(self, owner: int, entries: int = 0, nodes: int = 0) -> None:
        account = self._account(owner)
        self._validate_quantities(entries, nodes)
        if (
            entries < 0
            or nodes < 0
            or entries > account.entries
            or nodes > account.nodes
        ):
            raise ValueError("release exceeds the owner's reservation")
        account.entries -= entries
        account.nodes -= nodes
        self.entries -= entries
        self.nodes -= nodes

    def register_root(self, owner: int, root: object) -> None:
        account = self._account(owner)
        if account.disposed:
            raise RuntimeError("resource owner has been disposed")
        if not isinstance(root, ArenaHandle):
            raise TypeError("ledger roots must be typed arena handles")
        ArenaHandle.validate(root, root.owner, root.kind)
        account.roots[root] = None

    def unregister_root(self, owner: int, root: object) -> None:
        if not isinstance(root, ArenaHandle):
            raise TypeError("ledger roots must be typed arena handles")
        ArenaHandle.validate(root, root.owner, root.kind)
        del self._account(owner).roots[root]

    def register_container(
        self,
        owner: int,
        container: Sized,
        *,
        node_count: Callable[[], int] | None = None,
        payloads: Callable[[], Iterable[object]] | None = None,
        roots: Callable[[], Iterable[ArenaHandle]] | None = None,
        evict: Callable[[], None] | None = None,
        composition_count: Callable[[], int] | None = None,
    ) -> None:
        account = self._account(owner)
        if account.disposed:
            raise RuntimeError("resource owner has been disposed")
        if any(
            other is not account and other.container is container
            for other in self._accounts
        ):
            raise ValueError(
                "a retained container cannot belong to multiple resource owners"
            )
        if account.container is not None and account.container is not container:
            raise ValueError(
                "each retained container requires a distinct resource owner"
            )
        if evict is not None and account.role.lower().replace("-", "_") not in (
            "transfer_summary",
            "carry_range_transfer",
            "spatial_binding",
            "field_transfer_binding",
            "query_memo",
            "width_query_memo",
            "observation_memo",
            "diamond_memo",
            "macro_transfer_memo",
            "boundary_substitution_memo",
            "spatial_parent_memo",
            "image_program_memo",
            "output_function_memo",
            "unary_function_memo",
            "primitive_spatial_memo",
            "exact_microblock",
            "field_transfer",
            "field_transfer_interner",
            "completed_result_memo",
            "runtime_query_state_memo",
            "runtime_query_environment_memo",
            "runtime_operation_memo",
            "image_input_reference",
            "image_input_reference_interner",
            "image_input_reference_binding",
        ):
            raise ValueError("only explicitly registered query memos may be evicted")
        account.container = container
        account.node_count = node_count
        account.payloads = payloads
        account.root_resolver = roots
        account.evict = evict
        account.composition_count = composition_count
        self.note_store_mutation()

    def evict_query_memos(self) -> tuple[int, ...]:
        """Clear opted-in query caches; canonical programs and sources remain live."""
        evicted: list[int] = []
        for owner, account in enumerate(self._accounts):
            if account.evict is None:
                continue
            account.evict()
            if (
                account.entries
                or account.nodes
                or (account.container is not None and len(account.container))
            ):
                raise RuntimeError(
                    "query eviction did not reconcile its actual container"
                )
            evicted.append(owner)
        return tuple(evicted)

    def mark_disposed(self, owner: int) -> None:
        """Mark a cleared owner closed; no live payload may be hidden by disposal."""
        account = self._account(owner)
        if any(state[0] == owner for state in self._reservations.values()):
            raise ValueError("dispose requires closing the owner's reservations")
        if (
            account.entries
            or account.nodes
            or (account.container is not None and len(account.container))
        ):
            raise ValueError("dispose requires releasing the owner's actual resources")
        if account.disposed:
            return
        account.disposed = True
        drop_owner_contracts(self, owner)
        self.note_store_mutation()

    def iter_containers(self) -> Iterator[tuple[int, object]]:
        """Expose actual storage roots independently of user payload callbacks."""
        for owner, account in enumerate(self._accounts):
            if account.container is not None:
                yield owner, account.container

    def registered_container(self, owner: int) -> object | None:
        """Retrieve one live owner's store without an inventory scan."""
        account = self._account(owner)
        if account.disposed:
            raise RuntimeError("resource owner has been disposed")
        return account.container

    def iter_payloads(self) -> Iterator[tuple[int, object]]:
        """Expose actual registered payloads for an independent iterative audit."""
        for owner, account in enumerate(self._accounts):
            if account.payloads is not None:
                for payload in account.payloads():
                    yield owner, payload

    def bump(self, counter: str, amount: int = 1) -> None:
        if type(counter) is not str or not counter:
            raise ValueError("work counter names must be nonempty strings")
        if type(amount) is not int:
            raise TypeError("work counter increments must be integers")
        if amount < 0:
            raise ValueError("work counters are monotone")
        self.counters[counter] = self.counters.get(counter, 0) + amount

    def observe_arithmetic(self, value: int) -> int:
        """Record one local arithmetic result and enforce its 64-bit contract.

        Coordinate/exponent metadata does not pass through this method. Callers
        instrument arithmetic operations, not merely the eventual port result.
        """
        if type(value) is not int:
            raise TypeError("local arithmetic requires an integer")
        bits = value.bit_length()
        self.counters[_resources_keys.MAXIMUM_ARITHMETIC_BITS] = max(
            self.counters.get(_resources_keys.MAXIMUM_ARITHMETIC_BITS, 0), bits
        )
        if bits > 64:
            self.bump(_resources_keys.UNBOUNDED_ARITHMETIC_OBSERVATIONS)
            raise ArithmeticError(
                "local arithmetic result exceeds the 64-bit limb contract"
            )
        self.bump(_resources_keys.BOUNDED_LIMB_OPERATIONS)
        return value

    def inventory(self) -> tuple[ResourceInventory, ...]:
        return tuple(
            self.inventory_owner(owner) for owner in range(len(self._accounts))
        )

    def matches_store_account(
        self,
        owner: int,
        store: object,
        role: str,
        *,
        entries: int | None = None,
        nodes: int | None = None,
    ) -> bool:
        """Validate exact backing identity and its live charged quantities."""
        if not isinstance(store, Sized):
            return False
        try:
            account = self._account(owner)
            actual_entries = len(store)
            actual_nodes = None if account.node_count is None else account.node_count()
        except (AttributeError, TypeError, ValueError, RuntimeError):
            return False
        return (
            not account.disposed
            and account.container is store
            and account.role == role
            and account.entries == actual_entries
            and actual_nodes is not None
            and account.nodes == actual_nodes
            and (entries is None or account.entries == entries)
            and (nodes is None or account.nodes == nodes)
        )

    def refresh_payload_audit_contract(
        self,
        root: object,
        family: str,
        register: Callable[[], None],
        *,
        missing_message: str,
        restore_message: str,
    ) -> None:
        """Refresh a live contract and restore its exact binding on failure."""
        key = id(root), family
        old_binding = self._payload_audit_contracts.get(key)
        if old_binding is None or old_binding.root_reference() is not root:
            raise ValueError(missing_message)
        from number_compiler.resources.payload_contracts import (
            remove_payload_audit_contract,
        )

        remove_payload_audit_contract(self, root, family)
        try:
            register()
        except BaseException:
            try:
                self._payload_audit_contracts[key] = old_binding
                self.note_store_mutation()
            except BaseException as restore_error:
                raise RuntimeError(restore_message) from restore_error
            raise

    def account_status(self, owner: int) -> LedgerAccountStatus:
        """Read charged state and backing identity without traversing payloads."""
        account = self._account(owner)
        return LedgerAccountStatus(
            account.role,
            account.entries,
            account.nodes,
            account.disposed,
            None if account.container is None else id(account.container),
        )

    def ownership_audit_identities(self) -> tuple[int, ...]:
        """Expose bookkeeping identities without returning mutable ledger stores."""
        snapshot = self._payload_audit_snapshot
        snapshot_ids = (
            (id(snapshot),) if type(snapshot) is PayloadAuditContractAudit else ()
        )
        return (
            id(self._accounts),
            id(self._names),
            id(self._reservations),
            self._factory_containers.audit_identity,
            id(self._execution_roots),
            id(self._payload_audit_contracts),
            id(self.counters),
            *(id(account.roots) for account in self._accounts),
            *snapshot_ids,
        )

    def account_usage(self, owner: int) -> tuple[int, int]:
        """Read reservation totals without walking retained roots or payloads."""
        account = self._account(owner)
        return account.entries, account.nodes

    def inventory_owner(self, owner: int) -> ResourceInventory:
        """Audit one account without visiting unrelated owners or their resolvers."""
        account = self._account(owner)
        roots: dict[ArenaHandle, None] = {}
        for root in account.roots:
            ArenaHandle.validate(root, root.owner, root.kind)
            roots[root] = None
        if account.root_resolver is not None:
            for resolved_root in account.root_resolver():
                if not isinstance(resolved_root, ArenaHandle):
                    raise TypeError("container root resolver returned an untyped root")
                # Revalidate before hashing: Boolean/float IDs must not alias an
                # existing root in either a full or an owner-local inventory.
                ArenaHandle.validate(
                    resolved_root, resolved_root.owner, resolved_root.kind
                )
                roots[resolved_root] = None
        return ResourceInventory(
            owner,
            account.name,
            account.role,
            account.scope,
            account.entries,
            account.nodes,
            tuple(roots),
            None if account.container is None else len(account.container),
            None if account.node_count is None else account.node_count(),
            account.payloads is not None,
            account.evict is not None,
            0 if account.composition_count is None else account.composition_count(),
            account.disposed,
        )

    def snapshot(self) -> LedgerSnapshot:
        return LedgerSnapshot(
            self.entries,
            self.nodes,
            self.peak_entries,
            self.peak_nodes,
            self.counters.copy(),
            self.inventory(),
        )
