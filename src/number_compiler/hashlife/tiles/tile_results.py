"""Retirement-aware completed results over canonical future tiles."""

from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING, cast

from number_compiler.arithmetic.formula.summary import BlockSummary
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.interfaces.diamond_quotient import DiamondQuotientArena
from number_compiler.hashlife.interfaces.semantic_structures import LocalInterfaceID
from number_compiler.hashlife.tiles.completed_result_validation import (
    result_operand_views as _result_operand_views,
)
from number_compiler.hashlife.tiles.completed_result_validation import (
    result_tile_ids,
    validate_interface,
    validate_leased,
    validate_result,
    validate_spatial_key,
    validate_spatial_result,
)
from number_compiler.hashlife.tiles.result_memo_publication import ResultMemoPublication
from number_compiler.hashlife.tiles.tile_boundaries import (
    BoundaryTileOperands,
    BoundaryTileView,
)
from number_compiler.hashlife.tiles.tile_ports import (
    BoundPorts,
    FusedBoundaryContract,
    ResultWiring,
)
from number_compiler.hashlife.tiles.tile_result_acquisition import (
    ResultAcquisitionLeaseOwner,
)
from number_compiler.hashlife.tiles.tile_result_lease_inventory import (
    BoundaryOperandLeaseInventory,
)
from number_compiler.hashlife.tiles.tile_result_leases import ResultLease
from number_compiler.hashlife.tiles.tile_result_records import (
    CausalInterfaceKey,
    CompletedInterfaceResult,
    CompletedResult,
    DirectedTransferKey,
    FusedInterfaceKey,
    FusedVariantKey,
    PoweredInterfaceKey,
    PoweredResultKey,
    ResultDependencyHead,
    ResultDependencyLinks,
    ResultDependencyMember,
    ResultVariantKey,
    SpatialInterfaceKey,
    fused_variant_key,
)
from number_compiler.hashlife.tiles.tile_result_types import (
    ExecutionKey as _ExecutionKey,
)
from number_compiler.hashlife.tiles.tile_result_types import (
    ExecutionValue as _ExecutionValue,
)
from number_compiler.hashlife.tiles.tile_result_types import (
    MemoKey as _MemoKey,
)
from number_compiler.hashlife.tiles.tile_result_types import (
    ReverseKey as _ReverseKey,
)
from number_compiler.hashlife.tiles.tile_result_types import (
    ReverseValue as _ReverseValue,
)
from number_compiler.hashlife.tiles.tile_result_types import (
    is_execution_key,
)
from number_compiler.hashlife.tiles.tile_result_validation import (
    normalize_output_region,
    validate_boundary_operands,
    validate_fused_request,
    validate_ports_readonly,
)
from number_compiler.hashlife.tiles.tiles import TileArena, TileID, TileLease
from number_compiler.resources.cache_gc_metrics import (
    prepare_execution_cache_event,
    record_execution_cache_event,
)
from number_compiler.resources.lifecycle import cleanup_all
from number_compiler.resources.metric_keys import (
    hashlife_tiles as _tiles_keys,
)
from number_compiler.resources.metric_keys import shared as _shared_keys
from number_compiler.resources.result_cache_kinds import (
    RemovalCause,
    ResultCacheKind,
    record_cache_removal,
    record_unattributed_post_eviction_miss,
    retained_result_memo_nodes,
)
from number_compiler.resources.stores import LedgerDict

if TYPE_CHECKING:
    from number_compiler.resources.causal_workspace import CausalTaskWorkspace
    from number_compiler.resources.tile_runtime_audit_contracts import (
        CompletedResultArenaAuditSnapshot,
    )


_MISSING = object()


class CompletedResultArena(ResultMemoPublication):
    """One charged non-owning memo with exact tile retirement indexes."""

    def __init__(
        self,
        tiles: TileArena,
        interfaces: DiamondQuotientArena,
        *,
        action_authority: object,
        validate_action: Callable[[FieldCellActionID], object],
        signature_for: Callable[[FieldCellActionID], PortSignatureID],
    ) -> None:
        if type(tiles) is not TileArena or type(interfaces) is not DiamondQuotientArena:
            raise TypeError("completed results require tile and quotient arenas")
        if tiles.ledger is not interfaces.ledger:
            raise ValueError("completed results require one index ledger")
        ledger = tiles.ledger
        roots = tuple(ledger.iter_execution_roots())
        containers = tuple(value for _, value in ledger.iter_containers())
        if (
            not any(root is action_authority for root in roots)
            or getattr(action_authority, "ledger", None) is not ledger
            or getattr(validate_action, "__self__", None) is not action_authority
            or getattr(signature_for, "__self__", None) is not action_authority
            or not any(
                value is container
                for value in vars(action_authority).values()
                for container in containers
            )
        ):
            raise ValueError("completed results require a real action authority")
        self.tiles, self.interfaces, self.ledger = tiles, interfaces, ledger
        self.action_authority = action_authority
        self.action_validator = validate_action
        self.signature_provider = signature_for
        from number_compiler.hashlife.tiles.completed_result_validation import (
            admit_validated_signature,
        )

        self.signature_validator = admit_validated_signature(action_authority)
        input_validator = getattr(action_authority, "validate_input", None)
        if input_validator is not None and (
            not callable(input_validator)
            or getattr(input_validator, "__self__", None) is not action_authority
        ):
            raise ValueError("completed results require a bound input validator")
        fused_validator = getattr(action_authority, "validate_fused_action", None)
        if fused_validator is not None and (
            not callable(fused_validator)
            or getattr(fused_validator, "__self__", None) is not action_authority
        ):
            raise ValueError("completed results require a bound fused-action validator")
        self.input_validator: Callable[[FieldCellActionID, TileID], object] | None = (
            input_validator
        )
        output_validator = getattr(action_authority, "validate_output", None)
        if output_validator is not None and (
            not callable(output_validator)
            or getattr(output_validator, "__self__", None) is not action_authority
        ):
            raise ValueError("completed results require a bound output validator")
        self.output_validator: Callable[[FieldCellActionID, TileID], object] | None = (
            output_validator
        )
        self.fused_action_validator: Callable[[FieldCellActionID], object] | None = (
            fused_validator
        )
        fused_wiring_validator = getattr(
            action_authority,
            "validate_fused_wiring",
            None,
        )
        if fused_wiring_validator is not None and (
            not callable(fused_wiring_validator)
            or getattr(fused_wiring_validator, "__self__", None) is not action_authority
        ):
            raise ValueError("completed results require a bound fused-wiring validator")
        self.fused_wiring_validator: (
            Callable[[FieldCellActionID, ResultWiring, ResultWiring], object] | None
        ) = fused_wiring_validator
        self._admitted_validators = (
            self.action_validator,
            self.signature_provider,
            self.signature_validator,
            self.input_validator,
            self.output_validator,
            self.fused_action_validator,
            self.fused_wiring_validator,
        )
        self._causal_tasks: CausalTaskWorkspace | None = None
        self._physical_supports: object | None = None
        self._interface_publication_seal = object()
        self._result_lease_seal = object()
        self._boundary_lease_count = 0
        prefix = f"completed-results-{len(ledger.inventory())}"
        self._leased_boundary_operands = BoundaryOperandLeaseInventory(ledger, prefix)
        self._lease_acquisitions = ResultAcquisitionLeaseOwner(ledger, tiles, prefix)
        self._pending_acquisition_owner = self._lease_acquisitions.owner
        self._pending_acquisitions = self._lease_acquisitions.records
        self._memo_owner = ledger.register(prefix + "-memo", "completed_result_memo")
        self._reverse_owner = ledger.register(
            prefix + "-reverse", "completed_result_reverse_index"
        )
        self._variant_owner = ledger.register(
            prefix + "-variants", "completed_result_port_variants"
        )
        self._memo: LedgerDict[_MemoKey, _ExecutionValue] = ledger.make_dict(
            self._memo_owner
        )
        self._reverse: LedgerDict[_ReverseKey, _ReverseValue] = ledger.make_dict(
            self._reverse_owner,
        )
        self._variants: LedgerDict[ResultVariantKey | FusedVariantKey, int] = (
            ledger.make_dict(self._variant_owner)
        )
        ledger.register_container(
            self._memo_owner,
            self._memo,
            node_count=lambda: retained_result_memo_nodes(self._memo.values()),
            payloads=self._memo.items,
            evict=self.clear,
        )
        ledger.register_execution_root(self)
        tiles.bind_results(self)

    def attach_causal_tasks(self, tasks: CausalTaskWorkspace) -> None:
        """Bind the single scheduler workspace used by auxiliary result tasks."""
        from number_compiler.resources.causal_workspace import CausalTaskWorkspace

        if type(tasks) is not CausalTaskWorkspace or tasks.ledger is not self.ledger:
            raise ValueError("causal task workspace belongs to another index")
        if self._causal_tasks is not None:
            raise ValueError("completed results already have a causal task workspace")
        self._causal_tasks = tasks

    def accepts_result_lease_seal(self, seal: object) -> bool:
        """Check the unforgeable issuer token used by ResultLease construction."""
        return seal is self._result_lease_seal

    def boundary_operand_is_leased(self, view: BoundaryTileView) -> bool:
        count = self._leased_boundary_operands.records.get(view, 0)
        return type(count) is int and count >= 1

    @property
    def causal_tasks(self) -> CausalTaskWorkspace | None:
        """Return the scheduler-owned causal workspace when one is attached."""
        return self._causal_tasks

    def attach_physical_supports(self, arena: object) -> None:
        from number_compiler.hashlife.tiles.ordered_boolean_support import (
            OrderedBooleanSupportArena,
        )

        if (
            not isinstance(arena, OrderedBooleanSupportArena)
            or arena.ledger is not self.ledger
        ):
            raise ValueError("physical support arena belongs to another index")
        if self._physical_supports is not None and self._physical_supports is not arena:
            raise ValueError("completed results already have a support arena")
        self._physical_supports = arena

    def validate_physical_support(self, support: object) -> None:
        from number_compiler.hashlife.tiles.ordered_boolean_support import (
            OrderedBooleanSupport,
            OrderedBooleanSupportArena,
        )

        arena = self._physical_supports
        if arena is None:
            raise ValueError("completed result has no bound physical support arena")
        if not isinstance(arena, OrderedBooleanSupportArena):
            raise TypeError("completed result has an invalid physical support arena")
        if not isinstance(support, OrderedBooleanSupport):
            raise TypeError("completed result requires an ordered Boolean support")
        if support.owner is not arena:
            raise ValueError("completed result support belongs to another scheduler")
        arena.validate(support)

    def validated_action_authority(self) -> object:
        """Keep the mutable authority field bound to its admitted validators."""
        authority = self.action_authority
        callbacks = (
            self.action_validator,
            self.signature_provider,
            self.signature_validator,
            self.input_validator,
            self.output_validator,
            self.fused_action_validator,
            self.fused_wiring_validator,
        )
        # A combined validator replaces the two separate callbacks. Their
        # retired values are not consumer authority on that execution path.
        active_start = 0 if self.signature_validator is None else 2
        if any(
            callback is not admitted
            or (
                callback is not None
                and getattr(callback, "__self__", None) is not authority
            )
            for callback, admitted in zip(
                callbacks[active_start:],
                self._admitted_validators[active_start:],
                strict=True,
            )
        ):
            raise ValueError(
                "completed result action authority changed after admission"
            )
        return authority

    def validate_ports(
        self,
        signature: PortSignatureID,
        values: tuple[int, ...],
        *,
        counted: bool = True,
    ) -> None:
        validate_ports_readonly(
            self.interfaces,
            signature,
            values,
            ledger=self.ledger if counted else None,
        )

    def validate_boundaries(
        self,
        boundaries: BoundaryTileOperands,
        expected: TileID,
    ) -> None:
        validate_boundary_operands(
            self.tiles,
            boundaries,
            expected_alphabet=self.tiles.resolve(expected).alphabet,
        )

    def validate_fusion(
        self,
        action: FieldCellActionID,
        fusion: FusedBoundaryContract,
        consumer: BoundPorts,
        expected: TileID,
        *,
        counted: bool = True,
        output: bool = False,
        action_admission: object | None = None,
    ) -> int:
        from number_compiler.hashlife.tiles.completed_result_validation import (
            validate_fusion,
        )

        return validate_fusion(
            self,
            action,
            fusion,
            consumer,
            expected,
            counted=counted,
            output=output,
            action_admission=action_admission,
        )

    def validate_boundary_allocations(self, boundaries: BoundaryTileOperands) -> None:
        from number_compiler.hashlife.tiles.completed_result_validation import (
            validate_boundary_allocations,
        )

        return validate_boundary_allocations(self, boundaries)

    def validate_bound_port_allocations(
        self, context: BoundPorts, *, counted: bool = True
    ) -> None:
        from number_compiler.hashlife.tiles.completed_result_validation import (
            validate_bound_port_allocations,
        )

        return validate_bound_port_allocations(self, context, counted=counted)

    def validate_action_wiring(
        self,
        action: FieldCellActionID,
        wiring: ResultWiring,
        *,
        action_admission: object | None = None,
    ) -> None:
        from number_compiler.hashlife.tiles.completed_result_validation import (
            validate_action_wiring,
        )

        if action_admission is None:
            return validate_action_wiring(self, action, wiring)
        return validate_action_wiring(
            self, action, wiring, action_admission=action_admission
        )

    def validate_shape(
        self,
        action: FieldCellActionID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
    ) -> None:
        """Validate an action/port request before importing source geometry."""
        self.validate_action_wiring(action, wiring)
        self.validate_ports(wiring.signature, ports)

    def validate_base(
        self,
        action: FieldCellActionID,
        input_tile: TileID,
        wiring: ResultWiring,
        *,
        action_admission: object | None = None,
    ) -> None:
        from number_compiler.hashlife.tiles.completed_result_validation import (
            validate_base,
        )

        if action_admission is None:
            return validate_base(self, action, input_tile, wiring)
        return validate_base(
            self,
            action,
            input_tile,
            wiring,
            action_admission=action_admission,
        )

    def validate_key(
        self,
        key: PoweredResultKey,
        *,
        action_admission: object | None = None,
    ) -> None:
        from number_compiler.hashlife.tiles.completed_result_validation import (
            validate_key,
        )

        return validate_key(self, key, action_admission=action_admission)

    def validate_interface_key(self, key: PoweredInterfaceKey) -> None:
        from number_compiler.hashlife.tiles.completed_result_validation import (
            validate_interface_key,
        )

        return validate_interface_key(self, key)

    def validate_fused_key(self, key: FusedInterfaceKey) -> None:
        validate_fused_request(self, key)

    def validate_interface(
        self,
        key: PoweredInterfaceKey,
        interface: LocalInterfaceID,
    ) -> None:
        return validate_interface(self, key, interface)

    def validate_spatial_key(self, key: SpatialInterfaceKey) -> None:
        return validate_spatial_key(self, key)

    def validate_spatial_result(
        self,
        key: SpatialInterfaceKey,
        result: LocalInterfaceID,
    ) -> None:
        return validate_spatial_result(self, key, result)

    def validate_result(
        self,
        key: PoweredResultKey,
        result: CompletedResult,
        *,
        action_admission: object | None = None,
    ) -> None:
        if action_admission is None:
            return validate_result(self, key, result)
        return validate_result(self, key, result, action_admission=action_admission)

    def validate_leased(
        self,
        key: PoweredResultKey,
        result: CompletedResult,
        tile: TileLease,
        boundary_tiles: tuple[TileLease, ...],
        operand_views: tuple[BoundaryTileView, ...],
    ) -> None:
        return validate_leased(self, key, result, tile, boundary_tiles, operand_views)

    @staticmethod
    def unique_tiles(values: tuple[TileID, ...]) -> tuple[TileID, ...]:
        return tuple(dict.fromkeys(values))

    def result_tile_ids(self, result: CompletedResult) -> tuple[TileID, ...]:
        return result_tile_ids(self, result)

    def audit_snapshot(self) -> CompletedResultArenaAuditSnapshot:
        """Expose read-only live store views and owner bindings to auditors."""
        from number_compiler.resources.tile_runtime_audit_contracts import (
            CompletedResultArenaAuditSnapshot,
            CompletedResultAuthorityAudit,
        )

        return CompletedResultArenaAuditSnapshot.from_stores(
            self.ledger,
            self._memo,
            self._reverse,
            self._variants,
            self.tiles.audit_snapshot(),
            self.interfaces,
            CompletedResultAuthorityAudit(
                self.action_authority,
                self.action_validator,
                self.signature_provider,
                self.signature_validator,
                self.input_validator,
                self.output_validator,
                self.fused_action_validator,
                self.fused_wiring_validator,
            ),
            self._boundary_lease_count,
            self._leased_boundary_operands,
            self._lease_acquisitions,
            self._pending_acquisitions,
        )

    def validate_output(self, action: FieldCellActionID, output: TileID) -> None:
        """Apply the bound output validator when this arena's authority has one."""
        validator = self.output_validator
        if validator is not None:
            validator(action, output)

    result_operand_views = staticmethod(_result_operand_views)

    def _result_leases(
        self,
        result: CompletedResult,
        *,
        reserved: bool,
    ) -> tuple[TileLease, tuple[TileLease, ...]]:
        tiles = self.result_tile_ids(result)
        operand_views = self.result_operand_views(result)

        def acquire_operands() -> None:
            self._leased_boundary_operands.acquire(operand_views)

        leases = self._lease_acquisitions.acquire(
            tiles,
            reserved=reserved,
            after_acquire=acquire_operands,
        )
        boundary_count = len(leases) - 1
        self._boundary_lease_count += boundary_count
        self.ledger.counters[_shared_keys.BOUNDARY_TILE_LEASE_PEAK] = max(
            self.ledger.counters.get(_shared_keys.BOUNDARY_TILE_LEASE_PEAK, 0),
            self._boundary_lease_count,
        )
        return leases[0], tuple(leases[1:])

    def retry_pending_acquisition_leases(self) -> None:
        cleanup_all(
            (
                self._lease_acquisitions.retry,
                self._leased_boundary_operands.retry_release,
            )
        )

    def release_boundary_leases(
        self,
        count: int,
        operand_views: tuple[BoundaryTileView, ...],
        *,
        operands_already_mutated: bool = False,
        on_operands_mutated: Callable[[], object] | None = None,
    ) -> None:
        if type(count) is not int or not 0 <= count <= self._boundary_lease_count:
            raise ValueError("invalid completed-result boundary lease release")
        if type(operands_already_mutated) is not bool:
            raise TypeError("boundary operand release progress must be Boolean")
        if operands_already_mutated:
            if on_operands_mutated is not None:
                raise ValueError("completed operand release cannot mutate again")
            self._leased_boundary_operands.retry_release()
        else:
            self._leased_boundary_operands.release(
                operand_views,
                on_mutated=on_operands_mutated,
            )
        self._boundary_lease_count -= count

    def _lease(self, key: PoweredResultKey, result: CompletedResult) -> ResultLease:
        output, boundaries = self._result_leases(result, reserved=False)
        return ResultLease(
            self,
            key,
            result,
            output,
            self._result_lease_seal,
            boundaries,
            self.result_operand_views(result),
        )

    def _reserved_lease(
        self,
        key: PoweredResultKey,
        result: CompletedResult,
    ) -> ResultLease:
        output, boundaries = self._result_leases(result, reserved=True)
        return ResultLease(
            self,
            key,
            result,
            output,
            self._result_lease_seal,
            boundaries,
            self.result_operand_views(result),
        )

    def lookup(
        self,
        key: PoweredResultKey,
        *,
        validate_context: Callable[[PoweredResultKey], None] | None = None,
        _action_admission: object | None = None,
    ) -> ResultLease | None:
        """Admit the key and optional execution context before any memo access."""
        if _action_admission is None:
            self.validate_key(key)
        else:
            self.validate_key(key, action_admission=_action_admission)
        if validate_context is not None:
            validate_context(key)
        key = normalize_output_region(self.tiles, key)
        found = self._memo.get(key)
        self.ledger.bump(_tiles_keys.COMPLETED_RESULT_REQUESTS)
        if found is None:
            record_execution_cache_event(
                self,
                "result",
                "miss",
                key.action,
                key.input,
                action_admission=_action_admission,
            )
            record_unattributed_post_eviction_miss(self.ledger, ResultCacheKind.RESULT)
            return None
        if type(found) is not CompletedResult:
            raise TypeError("completed result memo has another value sort")
        if _action_admission is None:
            self.validate_result(key, found)
        else:
            self.validate_result(key, found, action_admission=_action_admission)
        lease = self._lease(key, found)
        self.ledger.bump(_tiles_keys.COMPLETED_RESULT_EARLY_HITS)
        record_execution_cache_event(
            self,
            "result",
            "early_hit",
            key.action,
            key.input,
            allow_new=False,
            action_admission=_action_admission,
        )
        return lease

    def tiles_for(
        self,
        key: _ExecutionKey,
        result: _ExecutionValue,
    ) -> tuple[TileID, ...]:
        from number_compiler.hashlife.tiles.completed_result_validation import (
            tiles_for,
        )

        return tiles_for(self, key, result)

    def index_entries(self, tiles: tuple[TileID, ...]) -> int:
        from number_compiler.hashlife.tiles.result_reverse_indexes import index_entries

        return index_entries(self, tiles)

    def add_membership(self, tile: TileID, key: _ExecutionKey) -> None:
        from number_compiler.hashlife.tiles.result_reverse_indexes import (
            add_membership,
        )

        return add_membership(self, tile, key)

    def reverse_snapshot(
        self,
        tiles: tuple[TileID, ...],
        key: _ExecutionKey,
    ) -> tuple[tuple[_ReverseKey, object], ...]:
        from number_compiler.hashlife.tiles.result_reverse_indexes import (
            reverse_snapshot,
        )

        return reverse_snapshot(self, tiles, key)

    def restore_reverse(
        self,
        snapshot: tuple[tuple[_ReverseKey, object], ...],
    ) -> None:
        from number_compiler.hashlife.tiles.result_reverse_indexes import (
            restore_reverse,
        )

        return restore_reverse(self, snapshot)

    def publish(
        self,
        key: PoweredResultKey,
        result: CompletedResult,
    ) -> ResultLease:
        self.validate_key(key)
        self.validate_result(key, result)
        key = normalize_output_region(self.tiles, key)
        found = self._memo.get(key)
        self.ledger.bump(_tiles_keys.COMPLETED_RESULT_PUBLICATION_REQUESTS)
        if found is not None:
            if type(found) is not CompletedResult:
                raise ValueError("powered result memo contains another result sort")
            if found != result:
                raise ValueError("powered result already has another complete value")
            lease = self._lease(key, found)
            self.ledger.bump(_tiles_keys.COMPLETED_RESULT_LATE_DUPLICATE_REDUCTIONS)
            record_execution_cache_event(
                self, "result", "late_duplicate", key.action, key.input
            )
            return lease
        referenced = self.tiles_for(key, result)
        reverse_entries = self.index_entries(referenced)
        variant_key = ResultVariantKey(
            key.action,
            key.input,
            key.wiring,
            key.boundaries,
            None if key.fusion is None else key.fusion.producer,
            key.region,
        )
        old_variants = self._variants.get(variant_key, 0)
        bound = 1
        for port in self.interfaces.interface(key.wiring.signature).inputs:
            bound *= port.cardinality
        if type(old_variants) is not int or not 0 <= old_variants < bound:
            raise ValueError("result variants exceed the finite port signature")
        reservations = (
            (self._memo_owner, 1, 0),
            (self._reverse_owner, reverse_entries, 0),
            (self._variant_owner, int(old_variants == 0), 0),
            (self.tiles.lease_owner, len(self.result_tile_ids(result)), 0),
        )
        reverse_snapshot = self.reverse_snapshot(referenced, key)
        self.ledger.reserve_many(reservations)
        try:
            lease = self._reserved_lease(key, result)
        except BaseException:
            for owner, entries, nodes in reservations[:-1]:
                self.ledger.release(owner, entries, nodes)
            raise
        try:
            self._memo[key] = result
            for tile in referenced:
                self.add_membership(tile, key)
            self._variants[variant_key] = old_variants + 1
        except BaseException:
            from number_compiler.hashlife.tiles.result_reverse_indexes import (
                restore_variant_publication,
            )

            restore_variant_publication(
                self, key, reverse_snapshot, variant_key, old_variants
            )
            lease.close()
            # Closing the lease releases its jointly reserved lease entry.
            for owner, entries, nodes in reservations[:-1]:
                self.ledger.release(owner, entries, nodes)
            raise
        self.ledger.bump(_tiles_keys.COMPLETED_RESULT_PUBLICATIONS)
        prepare_execution_cache_event(
            self, "result", "early_hit", key.action, key.input
        )
        record_execution_cache_event(
            self, "result", "publication", key.action, key.input
        )
        self.ledger.counters[_tiles_keys.COMPLETED_RESULT_PORT_VARIANTS_PEAK] = max(
            self.ledger.counters.get(
                _tiles_keys.COMPLETED_RESULT_PORT_VARIANTS_PEAK, 0
            ),
            old_variants + 1,
        )
        return lease

    def lookup_interface(
        self,
        key: PoweredInterfaceKey,
    ) -> LocalInterfaceID | None:
        from number_compiler.hashlife.tiles.interface_publication import (
            lookup_interface,
        )

        return lookup_interface(self, key)

    def publish_interface(
        self,
        key: PoweredInterfaceKey,
        interface: LocalInterfaceID,
    ) -> LocalInterfaceID:
        from number_compiler.hashlife.tiles.interface_publication import (
            publish_interface,
        )

        return publish_interface(self, key, interface)

    def lookup_fused_interface(
        self,
        key: FusedInterfaceKey,
    ) -> LocalInterfaceID | None:
        from number_compiler.hashlife.tiles.interface_publication import (
            lookup_fused_interface,
        )

        return lookup_fused_interface(self, key)

    def publish_fused_interface(
        self,
        key: FusedInterfaceKey,
        interface: LocalInterfaceID,
    ) -> LocalInterfaceID:
        from number_compiler.hashlife.tiles.interface_publication import (
            publish_fused_interface,
        )

        return publish_fused_interface(self, key, interface)

    def lookup_spatial_interface(
        self,
        key: SpatialInterfaceKey,
    ) -> LocalInterfaceID | None:
        from number_compiler.hashlife.tiles.interface_publication import (
            lookup_spatial_interface,
        )

        return lookup_spatial_interface(self, key)

    def publish_spatial_interface(
        self,
        key: SpatialInterfaceKey,
        result: LocalInterfaceID,
    ) -> LocalInterfaceID:
        from number_compiler.hashlife.tiles.interface_publication import (
            publish_spatial_interface,
        )

        return publish_spatial_interface(self, key, result)

    def reverse_threshold_summary(
        self,
        tile: TileID,
        base: int,
    ) -> BlockSummary:
        """Return the canonical current-field reset summary for a reverse tile."""
        from number_compiler.hashlife.tiles.reverse_threshold_summary import (
            reverse_threshold_summary,
        )

        return reverse_threshold_summary(self, tile, base)

    def remove_membership(self, tile: TileID, key: _ExecutionKey) -> None:
        from number_compiler.hashlife.tiles.result_reverse_indexes import (
            remove_membership,
        )

        return remove_membership(self, tile, key)

    def _remove_key(self, key: _MemoKey) -> None:
        result = self._memo.pop(key, None)
        if result is None:
            return
        if type(key) is not SpatialInterfaceKey:
            execution_key = cast(_ExecutionKey, key)
            for tile in self.tiles_for(execution_key, result):
                self.remove_membership(tile, execution_key)
        if type(key) is PoweredResultKey:
            variant_key = ResultVariantKey(
                key.action,
                key.input,
                key.wiring,
                key.boundaries,
                None if key.fusion is None else key.fusion.producer,
                key.region,
            )
            count = self._variants[variant_key]
            if count == 1:
                del self._variants[variant_key]
                self.ledger.release(self._variant_owner, entries=1)
            else:
                self._variants[variant_key] = count - 1
        elif type(key) is FusedInterfaceKey:
            fused_variant = fused_variant_key(key)
            count = self._variants[fused_variant]
            if count == 1:
                del self._variants[fused_variant]
                self.ledger.release(self._variant_owner, entries=1)
            else:
                self._variants[fused_variant] = count - 1
        retained_nodes = retained_result_memo_nodes((result,))
        self.ledger.release(self._memo_owner, entries=1, nodes=retained_nodes)
        record_cache_removal(self.ledger, key, RemovalCause.RETIREMENT)

    def retire_tile(self, tile: TileID) -> None:
        if type(tile) is not TileID:
            raise TypeError("tile retirement requires a scoped tile ID")
        tile.validate(self.tiles.owner, "canonical-tile", size=self.tiles.tile_count)
        before = len(self._memo)
        head = self._reverse.get(ResultDependencyHead(tile))
        while is_execution_key(head):
            self.ledger.bump(_tiles_keys.COMPLETED_RESULT_RETIREMENT_TRAVERSAL_STEPS)
            member = self._reverse.get(ResultDependencyMember(tile, head))
            following = (
                member.following if type(member) is ResultDependencyLinks else None
            )
            self._remove_key(head)
            head = following
        self.ledger.bump(_tiles_keys.COMPLETED_RESULT_TILE_RETIREMENTS)
        self.ledger.bump(
            _tiles_keys.COMPLETED_RESULT_RETIREMENT_MEMO_REMOVALS,
            before - len(self._memo),
        )

    def clear(self) -> None:
        cleanup_all((self.retry_pending_acquisition_leases, self._clear_memos))

    def _clear_memos(self) -> None:
        entries, reverse_entries = len(self._memo), len(self._reverse)
        retained_nodes = retained_result_memo_nodes(self._memo.values())
        variant_entries = len(self._variants)
        for key in self._memo:
            record_cache_removal(self.ledger, key, RemovalCause.EVICTION)
        self._memo.clear()
        self._reverse.clear()
        self._variants.clear()
        if entries:
            self.ledger.bump(_tiles_keys.COMPLETED_RESULT_EVICTIONS)
            self.ledger.bump(_tiles_keys.COMPLETED_RESULT_EVICTED_ENTRIES, entries)
            self.ledger.bump(
                _tiles_keys.COMPLETED_RESULT_EVICTION_REVERSE_INDEX_ENTRIES,
                reverse_entries,
            )
        self.ledger.release(self._memo_owner, entries=entries, nodes=retained_nodes)
        self.ledger.release(self._reverse_owner, entries=reverse_entries)
        self.ledger.release(self._variant_owner, entries=variant_entries)

    @property
    def retained_results(self) -> int:
        return sum(type(value) is CompletedResult for value in self._memo.values())

    completed_entries = retained_results

    @property
    def retained_interfaces(self) -> int:
        return sum(type(key) is PoweredInterfaceKey for key in self._memo)

    @property
    def retained_interface_compositions(self) -> int:
        return sum(type(key) is SpatialInterfaceKey for key in self._memo)

    @property
    def retained_fused_interfaces(self) -> int:
        return sum(type(key) is FusedInterfaceKey for key in self._memo)

    @property
    def retained_entries(self) -> int:
        return len(self._memo)


__all__ = [
    "BoundPorts",
    "CausalInterfaceKey",
    "CompletedInterfaceResult",
    "CompletedResult",
    "CompletedResultArena",
    "DirectedTransferKey",
    "FusedBoundaryContract",
    "FusedInterfaceKey",
    "PoweredInterfaceKey",
    "PoweredResultKey",
    "ResultLease",
    "ResultWiring",
    "SpatialInterfaceKey",
]
