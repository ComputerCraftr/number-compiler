"""Store-free interface publication operations."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.interfaces.semantic_structures import (
    LocalInterfaceID,
    MacroComponents,
    QuotientRecord,
)
from number_compiler.hashlife.tiles.result_reverse_indexes import publish_indexed_result
from number_compiler.hashlife.tiles.tile_result_records import (
    FusedInterfaceKey,
    PoweredInterfaceKey,
    SpatialInterfaceKey,
    fused_variant_key,
)
from number_compiler.resources.cache_gc_metrics import (
    record_execution_cache_event,
)
from number_compiler.resources.metric_keys import (
    hashlife_tiles as _tiles_keys,
)
from number_compiler.resources.metric_keys import shared as _shared_keys
from number_compiler.resources.result_cache_kinds import (
    ResultCacheKind,
    record_unattributed_post_eviction_miss,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.tiles.tile_results import CompletedResultArena


def lookup_interface(
    self: CompletedResultArena,
    key: PoweredInterfaceKey,
) -> LocalInterfaceID | None:
    self.validate_interface_key(key)
    found = self.memo_view.get(key)
    self.ledger.bump(_tiles_keys.POWERED_INTERFACE_REQUESTS)
    if found is None:
        record_execution_cache_event(self, "interface", "miss", key.action, key.input)
        record_unattributed_post_eviction_miss(self.ledger, ResultCacheKind.INTERFACE)
        return None
    if type(found) is not LocalInterfaceID:
        raise TypeError("powered interface memo has another value sort")
    self.validate_interface(key, found)
    self.ledger.bump(_tiles_keys.POWERED_INTERFACE_EARLY_HITS)
    record_execution_cache_event(
        self, "interface", "early_hit", key.action, key.input, allow_new=False
    )
    return found


def publish_interface(
    self: CompletedResultArena,
    key: PoweredInterfaceKey,
    interface: LocalInterfaceID,
) -> LocalInterfaceID:
    self.validate_interface_key(key)
    self.validate_interface(key, interface)
    self.ledger.bump(_tiles_keys.POWERED_INTERFACE_PUBLICATION_REQUESTS)
    found = self.memo_view.get(key)
    if found is not None:
        if type(found) is not LocalInterfaceID or found != interface:
            raise ValueError("powered interface already has another complete value")
        self.ledger.bump(_tiles_keys.POWERED_INTERFACE_LATE_ALIASES)
        return found
    publish_indexed_result(self, key, interface)
    self.ledger.bump(_tiles_keys.POWERED_INTERFACE_PUBLICATIONS)
    return interface


def lookup_fused_interface(
    self: CompletedResultArena,
    key: FusedInterfaceKey,
) -> LocalInterfaceID | None:
    self.validate_fused_key(key)
    found = self.memo_view.get(key)
    self.ledger.bump(_tiles_keys.FUSED_INTERFACE_REQUESTS)
    if found is None:
        record_unattributed_post_eviction_miss(self.ledger, ResultCacheKind.INTERFACE)
        return None
    if type(found) is not LocalInterfaceID:
        raise TypeError("fused interface memo has another value sort")
    if self.interfaces.resolve(found).signature != key.wiring.signature:
        raise ValueError("fused interface has another port signature")
    self.ledger.bump(_tiles_keys.FUSED_INTERFACE_EARLY_HITS)
    return found


def lookup_execution_fused_interface(
    self: CompletedResultArena,
    key: FusedInterfaceKey,
) -> LocalInterfaceID | None:
    """Probe a scheduler-derived fused key after its edge was validated.

    This internal seam is used only while executing ``finite_pair_transfer``.
    That caller obtains the action, temporal children, tile, ports and both
    wirings from the validated causal request and live canonical operands.  A
    miss returns to :func:`lookup_fused_interface` through ``fused_interface``
    and therefore performs complete admission before construction.  Public
    and caller-authored keys never use this shortcut.
    """
    if type(key) is not FusedInterfaceKey:
        raise TypeError("expected a scheduler-derived fused-interface key")
    key.__post_init__()
    found = self.memo_view.get(key)
    self.ledger.bump(_tiles_keys.FUSED_INTERFACE_EXECUTION_PROBES)
    if found is None:
        self.ledger.bump(_tiles_keys.FUSED_INTERFACE_EXECUTION_PROBE_MISSES)
        return None
    if type(found) is not LocalInterfaceID:
        raise TypeError("fused interface memo has another value sort")
    if self.interfaces.resolve(found).signature != key.wiring.signature:
        raise ValueError("fused interface has another port signature")
    self.ledger.bump(_tiles_keys.FUSED_INTERFACE_REQUESTS)
    self.ledger.bump(_tiles_keys.FUSED_INTERFACE_EARLY_HITS)
    self.ledger.bump(_tiles_keys.FUSED_INTERFACE_EXECUTION_EARLY_HITS)
    return found


def publish_fused_interface(
    self: CompletedResultArena,
    key: FusedInterfaceKey,
    interface: LocalInterfaceID,
) -> LocalInterfaceID:
    self.validate_fused_key(key)
    if type(interface) is not LocalInterfaceID:
        raise TypeError("fused interface requires a local interface ID")
    if self.interfaces.resolve(interface).signature != key.wiring.signature:
        raise ValueError("fused interface has another port signature")
    self.ledger.bump(_tiles_keys.FUSED_INTERFACE_PUBLICATION_REQUESTS)
    found = self.memo_view.get(key)
    if found is not None:
        if type(found) is not LocalInterfaceID or found != interface:
            raise ValueError("fused interface already has another complete value")
        self.ledger.bump(_tiles_keys.FUSED_INTERFACE_LATE_ALIASES)
        return found
    variant_key = fused_variant_key(key)
    producer_wiring = variant_key.producer_wiring
    old_variants = self.variant_counts.get(variant_key, 0)
    bound = 1
    for port in self.interfaces.interface(producer_wiring.signature).inputs:
        bound *= port.cardinality
    if type(old_variants) is not int or not 0 <= old_variants < bound:
        raise ValueError("fused interface variants exceed the finite signature")
    referenced = self.tiles_for(key, interface)
    reverse_entries = self.index_entries(referenced)
    reservations = (
        (self.memo_owner, 1, 0),
        (self.reverse_owner, reverse_entries, 0),
        (self.variant_owner, int(old_variants == 0), 0),
    )
    reverse_snapshot = self.reverse_snapshot(referenced, key)
    self.ledger.reserve_many(reservations)
    try:
        self.write_memo_reserved(key, interface)
        for tile in referenced:
            self.add_membership(tile, key)
        self.write_variant(variant_key, old_variants + 1)
    except BaseException:
        from number_compiler.hashlife.tiles.result_reverse_indexes import (
            restore_variant_publication,
        )

        restore_variant_publication(
            self, key, reverse_snapshot, variant_key, old_variants
        )
        for owner, entries, nodes in reservations:
            self.ledger.release(owner, entries, nodes)
        raise
    self.ledger.bump(_tiles_keys.FUSED_INTERFACE_PUBLICATIONS)
    return interface


def lookup_spatial_interface(
    self: CompletedResultArena,
    key: SpatialInterfaceKey,
) -> LocalInterfaceID | None:
    self.validate_spatial_key(key)
    found = self.memo_view.get(key)
    self.ledger.bump(_tiles_keys.SPATIAL_INTERFACE_COMPOSITION_REQUESTS)
    if found is None:
        record_unattributed_post_eviction_miss(self.ledger, ResultCacheKind.SPATIAL)
        return None
    if type(found) is not LocalInterfaceID:
        raise TypeError("spatial interface memo has another value sort")
    self.validate_spatial_result(key, found)
    self.ledger.bump(_tiles_keys.SPATIAL_INTERFACE_COMPOSITION_EARLY_HITS)
    return found


def publish_spatial_interface(
    self: CompletedResultArena,
    key: SpatialInterfaceKey,
    result: LocalInterfaceID,
) -> LocalInterfaceID:
    self.validate_spatial_key(key)
    self.validate_spatial_result(key, result)
    self.ledger.bump(_tiles_keys.SPATIAL_INTERFACE_COMPOSITION_PUBLICATION_REQUESTS)
    found = self.memo_view.get(key)
    if found is not None:
        if type(found) is not LocalInterfaceID or found != result:
            raise ValueError("spatial interface already has another complete value")
        self.ledger.bump(_shared_keys.SPATIAL_INTERFACE_COMPOSITION_LATE_ALIASES)
        return found
    self.ledger.reserve(self.memo_owner, entries=1)
    try:
        self.write_memo_reserved(key, result)
    except BaseException:
        self.discard_memo(key)
        self.ledger.release(self.memo_owner, entries=1)
        raise
    self.ledger.bump(_shared_keys.SPATIAL_INTERFACE_COMPOSITION_PUBLICATIONS)
    return result


def publish_spatial_quotient(
    self: CompletedResultArena,
    key: SpatialInterfaceKey,
    components: MacroComponents,
) -> LocalInterfaceID:
    """Atomically publish a canonical quotient and its spatial occurrence."""
    from number_compiler.hashlife.interfaces.atomic_quotient_normalization import (
        atomic_product_is_masked,
    )
    from number_compiler.hashlife.interfaces.closed_interface_admission import (
        has_closed_components,
    )
    from number_compiler.hashlife.interfaces.quotient_publication import (
        SpatialQuotientBinding,
        publish_quotient,
    )

    self.validate_spatial_key(key)
    interface = self.interfaces.validate_components(key.wiring.signature, components)
    closed = has_closed_components(components)
    if not closed and not atomic_product_is_masked(
        self.interfaces,
        interface,
        components,
    ):
        raise ValueError(
            "spatial quotient requires a closed or already-normalized product"
        )
    self.ledger.bump(_tiles_keys.SPATIAL_INTERFACE_COMPOSITION_PUBLICATION_REQUESTS)
    result = publish_quotient(
        self.interfaces,
        QuotientRecord(key.wiring.signature, components),
        None,
        spatial=SpatialQuotientBinding(self, key),
    )
    if closed:
        self.ledger.bump(_shared_keys.QUOTIENT_ARITHMETIC_NORMALIZATIONS)
    return result
