"""Per-index resource ownership and atomic, pre-insertion budget accounting."""

from __future__ import annotations

from collections.abc import Callable, Iterable, Iterator, MutableMapping, Sized
from contextlib import contextmanager
from dataclasses import dataclass, field
from enum import StrEnum
from typing import Generic, TypeVar, cast
from weakref import ReferenceType, ref

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle
from number_compiler.resources.lifecycle import clear_accounted_store
from number_compiler.resources.metric_keys import resources as _resources_keys
from number_compiler.resources.payload_contracts import (
    PayloadAuditContractAudit,
    PayloadAuditContribution,
    PayloadAuditStoreBinding,
    _drop_owner_contracts,
    _drop_root_contracts,
    _PayloadAuditBinding,
    audit_payload_contracts,
    clear_payload_audit_contracts,
    register_payload_audit_contract,
    remove_payload_audit_contract,
)
from number_compiler.resources.stores import LedgerDict, LedgerList

_StoreK = TypeVar("_StoreK")
_StoreV = TypeVar("_StoreV")
_StoreT = TypeVar("_StoreT")


class ResourceScope(StrEnum):
    ENGINE_OWNED = "ENGINE_OWNED"
    INDEX_OWNED = "INDEX_OWNED"
    SHARED_GLOBAL = "SHARED_GLOBAL"


@dataclass(frozen=True, slots=True)
class ResourceInventory:
    owner: int
    name: str
    role: str
    scope: ResourceScope
    entries: int
    nodes: int
    roots: tuple[ArenaHandle, ...]
    observed_entries: int | None = None
    observed_nodes: int | None = None
    payloads_registered: bool = False
    evictable: bool = False
    composition_entries: int = 0
    disposed: bool = False

    @property
    def accounting_delta(self) -> int | None:
        if self.observed_entries is None:
            return None
        return abs(self.observed_entries - self.entries) + (
            0 if self.observed_nodes is None else abs(self.observed_nodes - self.nodes)
        )


@dataclass(frozen=True, slots=True)
class LedgerSnapshot:
    entries: int
    nodes: int
    peak_entries: int
    peak_nodes: int
    counters: dict[str, int]
    inventory: tuple[ResourceInventory, ...]


@dataclass(slots=True)
class _Account:
    name: str
    role: str
    scope: ResourceScope
    entries: int = 0
    nodes: int = 0
    roots: dict[ArenaHandle, None] = field(default_factory=dict)
    container: Sized | None = None
    node_count: Callable[[], int] | None = None
    payloads: Callable[[], Iterable[object]] | None = None
    root_resolver: Callable[[], Iterable[ArenaHandle]] | None = None
    evict: Callable[[], None] | None = None
    composition_count: Callable[[], int] | None = None
    disposed: bool = False


class ResourceLedger:
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
        self._factory_containers: set[int] = set()
        self._execution_roots: dict[int, ReferenceType[object]] = {}
        self._payload_audit_contracts: dict[tuple[int, str], _PayloadAuditBinding] = {}
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
        rows: list[tuple[int, tuple[tuple[str, int, int | None], ...]]] = []
        for root in self.iter_execution_roots():
            try:
                attributes = dict(vars(root))
            except TypeError:
                attributes = {}
            for cls in type(root).__mro__:
                slots = cls.__dict__.get("__slots__", ())
                if isinstance(slots, str):
                    slots = (slots,)
                for name in slots:
                    if name in ("__dict__", "__weakref__") or name in attributes:
                        continue
                    if name.startswith("__") and not name.endswith("__"):
                        name = "_" + cls.__name__.lstrip("_") + name
                    try:
                        attributes[name] = getattr(root, name)
                    except AttributeError:
                        continue
            fields: list[tuple[str, int, int | None]] = []
            for name, value in attributes.items():
                try:
                    size = len(value) if isinstance(value, Sized) else None
                except (RuntimeError, TypeError, ValueError):
                    size = None
                fields.append((name, id(value), size))
            rows.append((id(root), tuple(sorted(fields))))
        return tuple(sorted(rows))

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
            self._expire_execution_root(identity, reference)

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

    def _expire_execution_root(
        self,
        identity: int,
        expected: ReferenceType[object] | None = None,
    ) -> None:
        current = self._execution_roots.get(identity)
        if expected is not None and current is not expected:
            return
        self._execution_roots.pop(identity, None)
        _drop_root_contracts(self, identity)
        self.note_store_mutation()

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
        for value, name in (
            (max_nodes, "node budget"),
            (max_cache_entries, "cache budget"),
        ):
            if value is not None:
                require_integer(value, name, 0)

    @staticmethod
    def _validate_quantities(entries: int, nodes: int) -> None:
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
                    _drop_root_contracts(self, identity)
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
        self.reserve_many(((owner, entries, nodes),))

    @contextmanager
    def reservation(
        self, owner: int, *, entries: int = 0, nodes: int = 0
    ) -> Iterator[None]:
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
        self, owner: int, *, nodes_per_entry: int = 0, write_once: bool = False
    ) -> LedgerDict[_StoreK, _StoreV]:
        require_integer(nodes_per_entry, "nodes per entry", 0)
        if type(write_once) is not bool:
            raise TypeError("mapping write-once policy must be Boolean")
        result: LedgerDict[_StoreK, _StoreV] = LedgerDict(
            self, owner, nodes_per_entry, write_once=write_once
        )
        self.register_container(
            owner,
            result,
            node_count=lambda: len(result) * nodes_per_entry,
            payloads=lambda: result._data.items(),
        )
        self._factory_containers.add(id(result))
        return result

    def make_list(
        self, owner: int, *, nodes_per_entry: int = 1, append_only: bool = True
    ) -> LedgerList[_StoreT]:
        require_integer(nodes_per_entry, "nodes per entry", 0)
        if type(append_only) is not bool:
            raise TypeError("append_only must be a boolean")
        result: LedgerList[_StoreT] = LedgerList(
            self, owner, nodes_per_entry, append_only
        )
        self.register_container(
            owner,
            result,
            node_count=lambda: len(result) * nodes_per_entry,
            payloads=lambda: result,
        )
        self._factory_containers.add(id(result))
        return result

    def is_factory_container(self, container: object) -> bool:
        """Identity provenance; registered containers stay live with this ledger."""
        return id(container) in self._factory_containers

    def check_capacity(self, *, entries: int = 0, nodes: int = 0) -> None:
        """Check a required allocation before constructing any dependent store."""
        self._validate_limits(self.max_nodes, self.max_cache_entries)
        self._validate_quantities(entries, nodes)
        next_entries, next_nodes = self.entries + entries, self.nodes + nodes
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
        self.check_capacity(entries=entries, nodes=nodes)
        for account, entry_count, node_count in pending:
            account.entries += entry_count
            account.nodes += node_count
        self.entries = next_entries
        self.nodes = next_nodes
        self.peak_entries = max(self.peak_entries, next_entries)
        self.peak_nodes = max(self.peak_nodes, next_nodes)

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
        for account, entries, nodes in released.values():
            if entries > account.entries or nodes > account.nodes:
                raise ValueError("reassignment release exceeds the owner's reservation")
        released_entries = sum(item[1] for item in released.values())
        released_nodes = sum(item[2] for item in released.values())
        reserved_entries = sum(item[1] for item in reserved.values())
        reserved_nodes = sum(item[2] for item in reserved.values())
        next_entries = self.entries - released_entries + reserved_entries
        next_nodes = self.nodes - released_nodes + reserved_nodes
        if self.max_cache_entries is not None and next_entries > self.max_cache_entries:
            raise BlockContextBudgetExceeded(
                f"cache budget exceeded before allocation: {next_entries} > {self.max_cache_entries}"
            )
        if self.max_nodes is not None and next_nodes > self.max_nodes:
            raise BlockContextBudgetExceeded(
                f"node budget exceeded before allocation: {next_nodes} > {self.max_nodes}"
            )
        for account, entries, nodes in released.values():
            account.entries -= entries
            account.nodes -= nodes
        for account, entries, nodes in reserved.values():
            account.entries += entries
            account.nodes += nodes
        self.entries, self.nodes = next_entries, next_nodes
        self.peak_entries = max(self.peak_entries, next_entries)
        self.peak_nodes = max(self.peak_nodes, next_nodes)

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

    def register_root(self, owner: int, root: ArenaHandle) -> None:
        account = self._account(owner)
        if account.disposed:
            raise RuntimeError("resource owner has been disposed")
        if not isinstance(root, ArenaHandle):
            raise TypeError("ledger roots must be typed arena handles")
        ArenaHandle.validate(root, root.owner, root.kind)
        account.roots[root] = None

    def unregister_root(self, owner: int, root: ArenaHandle) -> None:
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
        evicted = []
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
        if (
            account.entries
            or account.nodes
            or (account.container is not None and len(account.container))
        ):
            raise ValueError("dispose requires releasing the owner's actual resources")
        if account.disposed:
            return
        account.disposed = True
        _drop_owner_contracts(self, owner)
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

    def inventory_owner(self, owner: int) -> ResourceInventory:
        """Audit one account without visiting unrelated owners or their resolvers."""
        account = self._account(owner)
        roots: dict[ArenaHandle, None] = {}
        for root in account.roots:
            ArenaHandle.validate(root, root.owner, root.kind)
            roots[root] = None
        if account.root_resolver is not None:
            for root in account.root_resolver():
                if not isinstance(root, ArenaHandle):
                    raise TypeError("container root resolver returned an untyped root")
                # Revalidate before hashing: Boolean/float IDs must not alias an
                # existing root in either a full or an owner-local inventory.
                ArenaHandle.validate(root, root.owner, root.kind)
                roots[root] = None
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


_K = TypeVar("_K")
_V = TypeVar("_V")


@dataclass(frozen=True, slots=True)
class _DynamicMemoValue(Generic[_V]):
    """Payload and its retained cost stored together in the owned mapping."""

    value: _V
    nodes: int


class OwnedMemo(MutableMapping[_K, _V], Generic[_K, _V]):
    """An inventoried memo with fixed or payload-dependent node reservations."""

    def __init__(
        self,
        ledger: ResourceLedger,
        owner: int,
        *,
        nodes_per_entry: int = 0,
        node_cost: Callable[[_K, _V], int] | None = None,
        evictable: bool = False,
        composition_entries: bool = False,
    ) -> None:
        require_integer(nodes_per_entry, "nodes per entry", 0)
        if type(evictable) is not bool or type(composition_entries) is not bool:
            raise TypeError("memo policy flags must be booleans")
        if node_cost is not None and nodes_per_entry:
            raise ValueError("dynamic memo cost cannot be combined with a fixed cost")
        self.ledger = ledger
        self.owner = owner
        self.nodes_per_entry = nodes_per_entry
        self.node_cost = node_cost
        self._dynamic_nodes = 0
        self._pending_clear_entries = self._pending_clear_nodes = 0
        self._disposed = False
        self._data: MutableMapping[_K, _V | _DynamicMemoValue[_V]] = ledger.make_dict(
            owner, nodes_per_entry=nodes_per_entry
        )
        ledger.register_execution_root(self)
        ledger.register_container(
            owner,
            self._data,
            node_count=self._node_count,
            payloads=self._payloads,
            evict=self._evict if evictable else None,
            composition_count=self._entry_count if composition_entries else None,
        )

    def _check_open(self) -> None:
        if self._disposed:
            raise RuntimeError("memo has been disposed")

    def _entry_count(self) -> int:
        return len(self._data)

    def _node_count(self) -> int:
        if self.node_cost is not None:
            return self._dynamic_nodes
        return len(self._data) * self.nodes_per_entry

    def _entry_nodes(self, key: _K, value: _V) -> int:
        if self.node_cost is None:
            return self.nodes_per_entry
        payload_nodes = require_integer(
            self.node_cost(key, value), "memo payload node cost", 0
        )
        # One retained node accounts for the immutable cost metadata wrapper.
        return payload_nodes + 1

    def _payloads(self) -> Iterable[object]:
        from number_compiler.resources.payload_containers import audit_mapping_items

        for key, value in audit_mapping_items(self):
            yield key
            yield value

    def _audited_value(self, value: object) -> object:
        if self.node_cost is None:
            return value
        if not isinstance(value, _DynamicMemoValue):
            raise TypeError("dynamic memo entry has invalid cost metadata")
        return value.value

    def __getitem__(self, key: _K) -> _V:
        self._check_open()
        value = self._data[key]
        if self.node_cost is not None:
            if not isinstance(value, _DynamicMemoValue):
                raise TypeError("dynamic memo entry has invalid cost metadata")
            return cast(_V, value.value)
        return cast(_V, value)

    def __setitem__(self, key: _K, value: _V) -> None:
        self._check_open()
        if key in self._data:
            if self.node_cost is None:
                self._data[key] = value
                return
            previous = self._data[key]
            if not isinstance(previous, _DynamicMemoValue):
                raise TypeError("dynamic memo entry has invalid cost metadata")
            old_cost = previous.nodes
            new_cost = self._entry_nodes(key, value)
            difference = new_cost - old_cost
            if difference > 0:
                self.ledger.reserve(self.owner, nodes=difference)
            try:
                self._data[key] = _DynamicMemoValue(value, new_cost)
            except BaseException:
                self._data[key] = previous
                if difference > 0:
                    self.ledger.release(self.owner, nodes=difference)
                raise
            self._dynamic_nodes += difference
            if difference < 0:
                self.ledger.release(self.owner, nodes=-difference)
            return
        nodes = self._entry_nodes(key, value)
        self.ledger.reserve(self.owner, entries=1, nodes=nodes)
        try:
            if self.node_cost is not None:
                stored_value: _V | _DynamicMemoValue[_V] = _DynamicMemoValue(
                    value, nodes
                )
            else:
                stored_value = value
            self._data[key] = stored_value
        except BaseException:
            if key in self._data:
                del self._data[key]
            self.ledger.release(self.owner, entries=1, nodes=nodes)
            raise
        if self.node_cost is not None:
            self._dynamic_nodes += nodes

    def __delitem__(self, key: _K) -> None:
        self._check_open()
        value = self._data[key]
        if self.node_cost is not None:
            if not isinstance(value, _DynamicMemoValue):
                raise TypeError("dynamic memo entry has invalid cost metadata")
            nodes = value.nodes
        else:
            nodes = self.nodes_per_entry
        del self._data[key]
        if self.node_cost is not None:
            self._dynamic_nodes -= nodes
        self.ledger.release(self.owner, entries=1, nodes=nodes)

    def __len__(self) -> int:
        self._check_open()
        return len(self._data)

    def __iter__(self) -> Iterator[_K]:
        self._check_open()
        return iter(self._data)

    def clear(self) -> None:
        self._check_open()

        def measure() -> tuple[int, int]:
            size = len(self._data)
            if self.node_cost is None:
                return size, size * self.nodes_per_entry
            nodes = 0
            for value in self._data.values():
                if not isinstance(value, _DynamicMemoValue):
                    raise TypeError("dynamic memo entry has invalid cost metadata")
                nodes += value.nodes
            return size, nodes

        def clear_store() -> None:
            try:
                self._data.clear()
            finally:
                if self.node_cost is not None:
                    self._dynamic_nodes = measure()[1]

        def record_pending(entries: int, nodes: int) -> None:
            self._pending_clear_entries, self._pending_clear_nodes = entries, nodes

        clear_accounted_store(
            self.ledger,
            self.owner,
            clear_store,
            measure,
            (self._pending_clear_entries, self._pending_clear_nodes),
            record_pending,
        )

    def _evict(self) -> None:
        if not self._disposed:
            self.clear()

    def dispose(self) -> None:
        """Release actual memo values and invalidate every future lookup/update.

        A ledger owns its registered containers for its lifetime. Disposing a
        memo empties that container; dropping the owning index/ledger releases
        remaining canonical arenas through ordinary garbage collection.
        """
        if self._disposed:
            return
        self.clear()
        self.ledger.mark_disposed(self.owner)
        self._disposed = True
