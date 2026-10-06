"""Retirement-aware completed results over canonical future tiles."""

from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING, NoReturn, Self, cast

from number_compiler.arithmetic.formula.summary import BlockSummary
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.interfaces.diamond_quotient import (
    DiamondQuotientArena,
    LocalInterfaceID,
)
from number_compiler.hashlife.tiles import tile_result_records as _tile_result_records
from number_compiler.hashlife.tiles.tile_boundaries import (
    BoundaryTileOperands,
    BoundaryTileView,
)
from number_compiler.hashlife.tiles.tile_ports import (
    BoundPorts,
    FusedBoundaryContract,
    ResultWiring,
)
from number_compiler.hashlife.tiles.tile_result_lease_inventory import (
    BoundaryOperandLeaseInventory,
)
from number_compiler.hashlife.tiles.tile_result_records import (
    CausalInterfaceKey,
    CompletedInterfaceResult,
    CompletedResult,
    DirectedTransferKey,
    FusedInterfaceKey,
    PoweredInterfaceKey,
    PoweredResultKey,
    SpatialInterfaceKey,
    _FusedVariantKey,
    _ResultVariantKey,
    _ReverseHead,
    _ReverseLinks,
    _ReverseMember,
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
from number_compiler.resources.result_cache_kinds import (
    record_cache_removal,
    record_unattributed_post_eviction_miss,
    retained_result_memo_nodes,
)
from number_compiler.resources.stores import LedgerDict

BehaviorBindingKey = _tile_result_records.BehaviorBindingKey
BoundaryConcatKey = _tile_result_records.BoundaryConcatKey
NormalizedRegionKey = _tile_result_records.NormalizedRegionKey
ReverseBoundOutputKey = _tile_result_records.ReverseBoundOutputKey
ReverseThresholdSummaryKey = _tile_result_records.ReverseThresholdSummaryKey
SourceRootMatchKey = _tile_result_records.SourceRootMatchKey

if TYPE_CHECKING:
    from number_compiler.resources.causal_workspace import CausalTaskWorkspace


_RESULT_LEASE_SEAL = object()
_MISSING = object()


class ResultLease:
    """A completed result whose output tile remains live until close()."""

    __slots__ = (
        "_boundary_tiles",
        "_closed",
        "_issuer",
        "_key",
        "_operand_views",
        "_result",
        "_tile",
    )

    def __init__(
        self,
        issuer: CompletedResultArena,
        key: PoweredResultKey,
        result: CompletedResult,
        tile: TileLease,
        seal: object,
        boundary_tiles: tuple[TileLease, ...] = (),
        operand_views: tuple[BoundaryTileView, ...] = (),
    ) -> None:
        if seal is not _RESULT_LEASE_SEAL:
            raise TypeError("result leases must be issued by their arena")
        self._issuer, self._key = issuer, key
        if type(boundary_tiles) is not tuple or any(
            type(value) is not TileLease for value in boundary_tiles
        ):
            raise TypeError("result boundary leases require exact tile leases")
        self._result, self._tile = result, tile
        self._boundary_tiles, self._operand_views = boundary_tiles, operand_views
        self._closed = False

    def _require_open(self) -> None:
        if type(self._closed) is not bool or self._closed:
            raise ValueError("closed or malformed result lease")
        if (
            type(self._result) is not CompletedResult
            or type(self._tile) is not TileLease
        ):
            raise ValueError("malformed result lease")
        if type(self._boundary_tiles) is not tuple or any(
            type(value) is not TileLease for value in self._boundary_tiles
        ):
            raise ValueError("malformed result boundary leases")
        if type(self._operand_views) is not tuple or any(
            type(value) is not BoundaryTileView for value in self._operand_views
        ):
            raise ValueError("malformed result boundary operand inventory")
        if type(self._issuer) is not CompletedResultArena:
            raise ValueError("malformed result lease issuer")
        self._issuer._validate_leased(
            self._key,
            self._result,
            self._tile,
            self._boundary_tiles,
            self._operand_views,
        )

    @property
    def result(self) -> CompletedResult:
        self._require_open()
        _ = self._tile.tile
        return self._result

    @property
    def output(self) -> TileID:
        self._require_open()
        return self._tile.tile

    def close(self) -> None:
        if type(self._closed) is not bool:
            raise ValueError("malformed result lease")
        if not self._closed:
            self._require_open()
            for tile in reversed(self._boundary_tiles):
                tile.close()
            self._tile.close()
            self._issuer._release_boundary_leases(
                len(self._boundary_tiles),
                self._operand_views,
            )
            self._closed = True

    def __copy__(self) -> ResultLease:
        raise TypeError("result leases cannot be copied")

    def __deepcopy__(self, _memo: object) -> ResultLease:
        raise TypeError("result leases cannot be copied")

    def __reduce__(self) -> NoReturn:
        raise TypeError("result leases cannot be serialized")

    def __enter__(self) -> Self:
        _ = self.result
        return self

    def __exit__(self, *_exception: object) -> None:
        self.close()


class CompletedResultArena:
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
        self._validate_action = validate_action
        self._signature_for = signature_for
        from number_compiler.hashlife.tiles.completed_result_validation import (
            admit_validated_signature,
        )

        self._validated_signature_for = admit_validated_signature(action_authority)
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
        self._validate_input: Callable[[FieldCellActionID, TileID], object] | None = (
            input_validator
        )
        output_validator = getattr(action_authority, "validate_output", None)
        if output_validator is not None and (
            not callable(output_validator)
            or getattr(output_validator, "__self__", None) is not action_authority
        ):
            raise ValueError("completed results require a bound output validator")
        self._validate_output: Callable[[FieldCellActionID, TileID], object] | None = (
            output_validator
        )
        self._validate_fused_action: Callable[[FieldCellActionID], object] | None = (
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
        self._validate_fused_wiring: (
            Callable[[FieldCellActionID, ResultWiring, ResultWiring], object] | None
        ) = fused_wiring_validator
        self._causal_tasks: CausalTaskWorkspace | None = None
        self._physical_supports: object | None = None
        self._interface_publication_seal = object()
        self._boundary_lease_count = 0
        prefix = f"completed-results-{len(ledger.inventory())}"
        self._leased_boundary_operands = BoundaryOperandLeaseInventory(ledger, prefix)
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
        self._variants: LedgerDict[_ResultVariantKey | _FusedVariantKey, int] = (
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
        )

        arena = self._physical_supports
        if arena is None or not isinstance(support, OrderedBooleanSupport):
            raise ValueError("completed result has no bound physical support arena")
        if support.owner is not arena:
            raise ValueError("completed result support belongs to another scheduler")
        arena.validate(support)

    def _validate_ports(
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

    def _validate_boundaries(
        self,
        boundaries: BoundaryTileOperands,
        expected: TileID,
    ) -> None:
        validate_boundary_operands(
            self.tiles,
            boundaries,
            expected_alphabet=self.tiles.resolve(expected).alphabet,
        )

    def _validate_fusion(
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
            _validate_fusion,
        )

        return _validate_fusion(
            self,
            action,
            fusion,
            consumer,
            expected,
            counted=counted,
            output=output,
            action_admission=action_admission,
        )

    def _validate_boundary_allocations(self, boundaries: BoundaryTileOperands) -> None:
        from number_compiler.hashlife.tiles.completed_result_validation import (
            _validate_boundary_allocations,
        )

        return _validate_boundary_allocations(self, boundaries)

    def _validate_bound_port_allocations(
        self, context: BoundPorts, *, counted: bool = True
    ) -> None:
        from number_compiler.hashlife.tiles.completed_result_validation import (
            _validate_bound_port_allocations,
        )

        return _validate_bound_port_allocations(self, context, counted=counted)

    def _validate_action_wiring(
        self,
        action: FieldCellActionID,
        wiring: ResultWiring,
        *,
        action_admission: object | None = None,
    ) -> None:
        from number_compiler.hashlife.tiles.completed_result_validation import (
            _validate_action_wiring,
        )

        if action_admission is None:
            return _validate_action_wiring(self, action, wiring)
        return _validate_action_wiring(
            self, action, wiring, action_admission=action_admission
        )

    def validate_shape(
        self,
        action: FieldCellActionID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
    ) -> None:
        """Validate an action/port request before importing source geometry."""
        self._validate_action_wiring(action, wiring)
        self._validate_ports(wiring.signature, ports)

    def _validate_base(
        self,
        action: FieldCellActionID,
        input_tile: TileID,
        wiring: ResultWiring,
        *,
        action_admission: object | None = None,
    ) -> None:
        from number_compiler.hashlife.tiles.completed_result_validation import (
            _validate_base,
        )

        if action_admission is None:
            return _validate_base(self, action, input_tile, wiring)
        return _validate_base(
            self,
            action,
            input_tile,
            wiring,
            action_admission=action_admission,
        )

    def _validate_key(
        self,
        key: PoweredResultKey,
        *,
        action_admission: object | None = None,
    ) -> None:
        from number_compiler.hashlife.tiles.completed_result_validation import (
            _validate_key,
        )

        return _validate_key(self, key, action_admission=action_admission)

    def _validate_interface_key(self, key: PoweredInterfaceKey) -> None:
        from number_compiler.hashlife.tiles.completed_result_validation import (
            _validate_interface_key,
        )

        return _validate_interface_key(self, key)

    def _validate_fused_key(self, key: FusedInterfaceKey) -> None:
        validate_fused_request(self, key)

    def _validate_interface(
        self,
        key: PoweredInterfaceKey,
        interface: LocalInterfaceID,
    ) -> None:
        from number_compiler.hashlife.tiles.completed_result_validation import (
            _validate_interface,
        )

        return _validate_interface(self, key, interface)

    def _validate_spatial_key(self, key: SpatialInterfaceKey) -> None:
        from number_compiler.hashlife.tiles.completed_result_validation import (
            _validate_spatial_key,
        )

        return _validate_spatial_key(self, key)

    def _validate_spatial_result(
        self,
        key: SpatialInterfaceKey,
        result: LocalInterfaceID,
    ) -> None:
        from number_compiler.hashlife.tiles.completed_result_validation import (
            _validate_spatial_result,
        )

        return _validate_spatial_result(self, key, result)

    def _validate_result(
        self,
        key: PoweredResultKey,
        result: CompletedResult,
        *,
        action_admission: object | None = None,
    ) -> None:
        from number_compiler.hashlife.tiles.completed_result_validation import (
            _validate_result,
        )

        if action_admission is None:
            return _validate_result(self, key, result)
        return _validate_result(self, key, result, action_admission=action_admission)

    def _validate_leased(
        self,
        key: PoweredResultKey,
        result: CompletedResult,
        tile: TileLease,
        boundary_tiles: tuple[TileLease, ...],
        operand_views: tuple[BoundaryTileView, ...],
    ) -> None:
        from number_compiler.hashlife.tiles.completed_result_validation import (
            _validate_leased,
        )

        return _validate_leased(self, key, result, tile, boundary_tiles, operand_views)

    @staticmethod
    def _unique_tiles(values: tuple[TileID, ...]) -> tuple[TileID, ...]:
        return tuple(dict.fromkeys(values))

    def _result_tile_ids(self, result: CompletedResult) -> tuple[TileID, ...]:
        from number_compiler.hashlife.tiles.completed_result_validation import (
            _result_tile_ids,
        )

        return _result_tile_ids(self, result)

    @staticmethod
    def _result_operand_views(result: CompletedResult) -> tuple[BoundaryTileView, ...]:
        from number_compiler.hashlife.tiles.completed_result_validation import (
            _result_operand_views,
        )

        return _result_operand_views(result)

    def _result_leases(
        self,
        result: CompletedResult,
        *,
        reserved: bool,
    ) -> tuple[TileLease, tuple[TileLease, ...]]:
        tiles = self._result_tile_ids(result)
        operand_views = self._result_operand_views(result)
        leases: list[TileLease] = []
        if not reserved:
            self.ledger.reserve(self.tiles._lease_owner, entries=len(tiles))
        try:
            for tile in tiles:
                leases.append(self.tiles._acquire_reserved(tile))
            self._leased_boundary_operands.acquire(operand_views)
        except BaseException:
            for lease in reversed(leases):
                lease.close()
            self.ledger.release(
                self.tiles._lease_owner,
                entries=len(tiles) - len(leases),
            )
            raise
        boundary_count = len(leases) - 1
        self._boundary_lease_count += boundary_count
        self.ledger.counters["boundary_tile_lease_peak"] = max(
            self.ledger.counters.get("boundary_tile_lease_peak", 0),
            self._boundary_lease_count,
        )
        return leases[0], tuple(leases[1:])

    def _release_boundary_leases(
        self,
        count: int,
        operand_views: tuple[BoundaryTileView, ...],
    ) -> None:
        if type(count) is not int or not 0 <= count <= self._boundary_lease_count:
            raise ValueError("invalid completed-result boundary lease release")
        self._boundary_lease_count -= count
        self._leased_boundary_operands.release(operand_views)

    def _lease(self, key: PoweredResultKey, result: CompletedResult) -> ResultLease:
        output, boundaries = self._result_leases(result, reserved=False)
        return ResultLease(
            self,
            key,
            result,
            output,
            _RESULT_LEASE_SEAL,
            boundaries,
            self._result_operand_views(result),
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
            _RESULT_LEASE_SEAL,
            boundaries,
            self._result_operand_views(result),
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
            self._validate_key(key)
        else:
            self._validate_key(key, action_admission=_action_admission)
        if validate_context is not None:
            validate_context(key)
        key = normalize_output_region(self.tiles, key)
        found = self._memo.get(key)
        self.ledger.bump("completed_result_requests")
        if found is None:
            record_execution_cache_event(
                self,
                "result",
                "miss",
                key.action,
                key.input,
                action_admission=_action_admission,
            )
            record_unattributed_post_eviction_miss(self.ledger, "result")
            return None
        if type(found) is not CompletedResult:
            raise TypeError("completed result memo has another value sort")
        if _action_admission is None:
            self._validate_result(key, found)
        else:
            self._validate_result(key, found, action_admission=_action_admission)
        lease = self._lease(key, found)
        self.ledger.bump("completed_result_early_hits")
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

    def _tiles_for(
        self,
        key: _ExecutionKey,
        result: _ExecutionValue,
    ) -> tuple[TileID, ...]:
        from number_compiler.hashlife.tiles.completed_result_validation import (
            _tiles_for,
        )

        return _tiles_for(self, key, result)

    def _index_entries(self, tiles: tuple[TileID, ...]) -> int:
        from number_compiler.hashlife.tiles.result_reverse_indexes import _index_entries

        return _index_entries(self, tiles)

    def _add_membership(self, tile: TileID, key: _ExecutionKey) -> None:
        from number_compiler.hashlife.tiles.result_reverse_indexes import (
            _add_membership,
        )

        return _add_membership(self, tile, key)

    def _write_reverse(self, key: _ReverseKey, value: _ReverseValue) -> None:
        """Single fault-injection boundary for reverse-index publication."""
        self._reverse[key] = value

    def _reverse_snapshot(
        self,
        tiles: tuple[TileID, ...],
        key: _ExecutionKey,
    ) -> tuple[tuple[_ReverseKey, object], ...]:
        from number_compiler.hashlife.tiles.result_reverse_indexes import (
            _reverse_snapshot,
        )

        return _reverse_snapshot(self, tiles, key)

    def _restore_reverse(
        self,
        snapshot: tuple[tuple[_ReverseKey, object], ...],
    ) -> None:
        from number_compiler.hashlife.tiles.result_reverse_indexes import (
            _restore_reverse,
        )

        return _restore_reverse(self, snapshot)

    def publish(
        self,
        key: PoweredResultKey,
        result: CompletedResult,
    ) -> ResultLease:
        self._validate_key(key)
        self._validate_result(key, result)
        key = normalize_output_region(self.tiles, key)
        found = self._memo.get(key)
        self.ledger.bump("completed_result_publication_requests")
        if found is not None:
            if found != result:
                raise ValueError("powered result already has another complete value")
            lease = self._lease(key, found)
            self.ledger.bump("completed_result_late_duplicate_reductions")
            record_execution_cache_event(
                self, "result", "late_duplicate", key.action, key.input
            )
            return lease
        referenced = self._tiles_for(key, result)
        reverse_entries = self._index_entries(referenced)
        variant_key = _ResultVariantKey(
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
            (self.tiles._lease_owner, len(self._result_tile_ids(result)), 0),
        )
        reverse_snapshot = self._reverse_snapshot(referenced, key)
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
                self._add_membership(tile, key)
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
        self.ledger.bump("completed_result_publications")
        prepare_execution_cache_event(
            self, "result", "early_hit", key.action, key.input
        )
        record_execution_cache_event(
            self, "result", "publication", key.action, key.input
        )
        self.ledger.counters["completed_result_port_variants_peak"] = max(
            self.ledger.counters.get("completed_result_port_variants_peak", 0),
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

    def _remove_membership(self, tile: TileID, key: _ExecutionKey) -> None:
        from number_compiler.hashlife.tiles.result_reverse_indexes import (
            _remove_membership,
        )

        return _remove_membership(self, tile, key)

    def _remove_key(self, key: _MemoKey) -> None:
        result = self._memo.pop(key, None)
        if result is None:
            return
        if type(key) is not SpatialInterfaceKey:
            execution_key = cast(_ExecutionKey, key)
            for tile in self._tiles_for(execution_key, result):
                self._remove_membership(tile, execution_key)
        if type(key) is PoweredResultKey:
            variant_key = _ResultVariantKey(
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
        record_cache_removal(self.ledger, key, "retirement")

    def retire_tile(self, tile: TileID) -> None:
        if type(tile) is not TileID:
            raise TypeError("tile retirement requires a scoped tile ID")
        tile.validate(self.tiles.owner, "canonical-tile", size=self.tiles._next_tile)
        before = len(self._memo)
        head = self._reverse.get(_ReverseHead(tile))
        while is_execution_key(head):
            self.ledger.bump("completed_result_retirement_traversal_steps")
            member = self._reverse.get(_ReverseMember(tile, head))
            following = member.following if type(member) is _ReverseLinks else None
            self._remove_key(head)
            head = following
        self.ledger.bump("completed_result_tile_retirements")
        self.ledger.bump(
            "completed_result_retirement_memo_removals", before - len(self._memo)
        )

    def clear(self) -> None:
        entries, reverse_entries = len(self._memo), len(self._reverse)
        retained_nodes = retained_result_memo_nodes(self._memo.values())
        variant_entries = len(self._variants)
        for key in self._memo:
            record_cache_removal(self.ledger, key, "eviction")
        self._memo.clear()
        self._reverse.clear()
        self._variants.clear()
        if entries:
            self.ledger.bump("completed_result_evictions")
            self.ledger.bump("completed_result_evicted_entries", entries)
            self.ledger.bump(
                "completed_result_eviction_reverse_index_entries", reverse_entries
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
