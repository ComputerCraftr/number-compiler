"""Occurrence bindings for completed, certified future-behavior classes."""

from __future__ import annotations

from typing import TYPE_CHECKING, Any, cast

from number_compiler.resources.metric_keys import (
    hashlife_tiles as _tiles_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )

from number_compiler.hashlife.behavior.future_behavior import (
    FutureBehaviorClassID,
    FutureBehaviorProfileID,
)
from number_compiler.hashlife.tiles.tile_boundaries import (
    BoundaryTileOperands,
    BoundaryTileView,
)
from number_compiler.hashlife.tiles.tile_ports import (
    BoundPorts,
    FusedBoundaryContract,
    ResultWiring,
)
from number_compiler.hashlife.tiles.tile_result_records import (
    BehaviorBindingKey,
    CompletedBehaviorClassification,
    PoweredResultKey,
    execution_request_snapshot,
    handle_snapshot,
)
from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
from number_compiler.resources.cache_gc_metrics import (
    record_execution_cache_event,
    temporal_span,
)
from number_compiler.resources.result_cache_kinds import (
    ResultCacheKind,
    record_unattributed_post_eviction_miss,
)


class UnsupportedBehaviorBinding(ValueError):
    """The certified class does not cover this exact occurrence binding."""


_RESERVATION_SEAL = object()


class BehaviorPublicationReservation:
    """Transient result slots reserved before semantic-profile admission."""

    __slots__ = ("_arena", "_open", "_reservations", "_seal", "_tiles")

    def __init__(
        self,
        arena: CompletedResultArena,
        tiles: tuple[object, ...],
        reservations: tuple[tuple[int, int, int], ...],
        seal: object,
    ) -> None:
        if seal is not _RESERVATION_SEAL:
            raise TypeError("behavior reservations must be arena-issued")
        self._arena, self._tiles, self._reservations = arena, tiles, reservations
        self._open, self._seal = True, seal

    def close(self) -> None:
        if self._open:
            for owner, entries, nodes in self._reservations:
                self._arena.ledger.release(owner, entries, nodes)
            self._open = False


def reserve_behavior_publication(
    arena: CompletedResultArena,
    request: PoweredResultKey,
) -> BehaviorPublicationReservation:
    if type(arena) is not CompletedResultArena or type(request) is not PoweredResultKey:
        raise TypeError("behavior reservation requires a powered result request")
    arena._validate_key(request)
    tiles = arena._unique_tiles(
        (
            request.input,
            *request.boundaries.tile_ids(),
            *(
                ()
                if request.fusion is None
                else (
                    *request.fusion.producer.boundaries.tile_ids(),
                    *request.fusion.consumer.boundaries.tile_ids(),
                )
            ),
        )
    )
    reservations = (
        (arena._memo_owner, 1, 0),
        (arena._reverse_owner, arena._index_entries(tiles), 0),
    )
    arena.ledger.reserve_many(reservations)
    return BehaviorPublicationReservation(
        arena,
        tuple(tiles),
        reservations,
        _RESERVATION_SEAL,
    )


def behavior_binding_key(
    request: PoweredResultKey,
    profile: FutureBehaviorProfileID,
) -> BehaviorBindingKey:
    if type(request) is not PoweredResultKey:
        raise TypeError("behavior binding requires a powered request")
    if type(profile) is not FutureBehaviorProfileID:
        raise TypeError("behavior binding requires a scoped profile")
    return BehaviorBindingKey(request, profile)


def _detached_handle(value: Any) -> Any:
    """Copy a scoped handle while retaining its arena token authority."""
    return type(value)(value.owner, value.kind, value.local_id)


def _detached_view(value: BoundaryTileView | None) -> BoundaryTileView | None:
    if value is None:
        return None
    return BoundaryTileView(
        _detached_handle(value.tile),
        value.relative_origin,
        value.relative_extent,
        value.orientation,
        value.source_offset,
    )


def _detached_boundaries(value: BoundaryTileOperands) -> BoundaryTileOperands:
    return BoundaryTileOperands(_detached_view(value.left), _detached_view(value.right))


def _detached_wiring(value: ResultWiring) -> ResultWiring:
    return ResultWiring(
        _detached_handle(value.signature),
        value.orientation,
        value.phase,
    )


def _detached_bound(value: BoundPorts) -> BoundPorts:
    return BoundPorts(
        tuple(value.ports),
        _detached_wiring(value.wiring),
        _detached_boundaries(value.boundaries),
    )


def _detached_fusion(
    value: FusedBoundaryContract | None,
) -> FusedBoundaryContract | None:
    if value is None:
        return None
    return FusedBoundaryContract(
        _detached_bound(value.producer),
        _detached_bound(value.consumer),
    )


def _detached_key(value: BehaviorBindingKey) -> BehaviorBindingKey:
    request = value.request
    region = None if request.region is None else tuple(request.region)
    return BehaviorBindingKey(
        PoweredResultKey(
            _detached_handle(request.action),
            _detached_handle(request.input),
            tuple(request.ports),
            _detached_wiring(request.wiring),
            _detached_boundaries(request.boundaries),
            _detached_fusion(request.fusion),
            cast(tuple[int, int] | None, region),
        ),
        _detached_handle(value.profile),
    )


def _snapshot(
    key: BehaviorBindingKey,
    value: CompletedBehaviorClassification,
) -> tuple[object, ...]:
    return (
        execution_request_snapshot(key.request),
        handle_snapshot(key.profile),
        handle_snapshot(value.behavior),
    )


def _validate_key(arena: CompletedResultArena, key: BehaviorBindingKey) -> None:
    if type(arena) is not CompletedResultArena:
        raise TypeError("behavior binding requires the shared result arena")
    if type(key) is not BehaviorBindingKey:
        raise TypeError("behavior binding has another key sort")
    if type(key.request) is not PoweredResultKey:
        raise TypeError("behavior binding requires a powered request")
    arena._validate_key(key.request)
    arena.interfaces.resolve_future_profile(key.profile)


def _validate_published(
    arena: CompletedResultArena,
    key: BehaviorBindingKey,
    value: CompletedBehaviorClassification,
) -> None:
    value.__post_init__()
    if value._publication_owner is not arena._interface_publication_seal:
        raise ValueError("behavior classification was not issued by this arena")
    if value._publication_snapshot != _snapshot(key, value):
        raise ValueError("behavior publication metadata was modified")
    behavior = arena.interfaces.resolve_future_behavior(value.behavior)
    if behavior.profile != key.profile:
        raise ValueError("behavior class belongs to another profile")


def _blank_left_operand(arena: CompletedResultArena, value: object) -> bool:
    if value is None:
        return True
    tile = getattr(value, "tile", None)
    if tile is None:
        raise TypeError("blank behavior requires an exact boundary tile view")
    return arena.tiles.resolve(tile).first_active is None


def _validate_blank_proof(
    arena: CompletedResultArena,
    key: BehaviorBindingKey,
    behavior_id: FutureBehaviorClassID,
) -> None:
    """Validate the bounded induction before publishing an occurrence binding.

    This cold-only check uses immutable root summaries and finite port tables.
    Warm lookup deliberately uses only the sealed snapshot and live handles.
    """
    arena.ledger.bump(_tiles_keys.FUTURE_BEHAVIOR_CLASSIFICATION_EVALUATIONS)
    profile = arena.interfaces.resolve_future_profile(key.profile)
    behavior_class = arena.interfaces.resolve_future_behavior(behavior_id)
    certificate = arena.interfaces.future_certificate(key.profile)
    if behavior_class.profile != key.profile:
        raise ValueError("behavior class belongs to another profile")
    if arena.tiles.resolve(key.input).first_active is not None:
        raise UnsupportedBehaviorBinding(
            "quiescent behavior requires an inactive exact input"
        )
    authority = cast("PrimitiveTileKernelAdapter", arena.action_authority)
    action_record = authority._action(key.action)
    if type(action_record.homogeneous) is not bool or not action_record.homogeneous:
        raise UnsupportedBehaviorBinding(
            "quiescent behavior requires a homogeneous action"
        )
    quotient = authority.kernels.behavioral_quotient(action_record.kernel)
    if (
        quotient.source_identity != profile.kernel
        or quotient.semantic_identity != profile.continuation
        or quotient.alphabet_size != profile.alphabet_size
        or quotient.blank != profile.blank
        or certificate.semantic_digest != profile.certificate_digest
    ):
        raise ValueError("behavior profile belongs to another primitive law")

    def safe(raw: int) -> bool:
        if type(raw) is not int or not 0 <= raw < len(quotient.left_classes):
            raise ValueError("blank behavior requires a finite exact left state")
        arena.ledger.bump(_tiles_keys.BEHAVIOR_CLASSIFICATION_PORT_CHECKS)
        return quotient.left_classes[raw] in certificate.safe_blank_left_states

    initial = authority.initial_ports(key.action)[0]
    if not safe(initial):
        raise UnsupportedBehaviorBinding(
            "the action's initial left state is not blank-safe"
        )
    if key.fusion is None:
        if not key.ports or not safe(key.ports[0]):
            raise UnsupportedBehaviorBinding(
                "the request's left state is not blank-safe"
            )
        if not _blank_left_operand(arena, key.boundaries.left):
            raise UnsupportedBehaviorBinding(
                "the request has a nonblank left boundary operand"
            )
    else:
        producer, consumer = key.fusion.producer, key.fusion.consumer
        if not producer.ports or not consumer.ports:
            raise ValueError("fused blank behavior requires both finite contexts")
        if not safe(producer.ports[0]) or not safe(consumer.ports[0]):
            raise UnsupportedBehaviorBinding("a fused left state is not blank-safe")
        if not _blank_left_operand(arena, producer.boundaries.left) or not (
            _blank_left_operand(arena, consumer.boundaries.left)
        ):
            raise UnsupportedBehaviorBinding(
                "a fused request has a nonblank left boundary operand"
            )


def lookup_behavior_classification(
    arena: CompletedResultArena,
    key: BehaviorBindingKey,
) -> CompletedBehaviorClassification | None:
    _validate_key(arena, key)
    found = arena._memo.get(key)
    arena.ledger.bump(_tiles_keys.FUTURE_BEHAVIOR_REQUESTS)
    arena.ledger.bump(_tiles_keys.FUTURE_BEHAVIOR_BINDING_REQUESTS)
    if found is None:
        record_unattributed_post_eviction_miss(arena.ledger, ResultCacheKind.BEHAVIOR)
        record_execution_cache_event(
            arena,
            "behavior",
            "miss",
            key.action,
            key.input,
        )
        return None
    if type(found) is not CompletedBehaviorClassification:
        raise TypeError("behavior memo contains another value sort")
    _validate_published(arena, key, found)
    arena.ledger.bump(_tiles_keys.FUTURE_BEHAVIOR_EARLY_HITS)
    arena.ledger.bump(_tiles_keys.FUTURE_BEHAVIOR_BINDING_EARLY_HITS)
    record_execution_cache_event(
        arena,
        "behavior",
        "early_hit",
        key.action,
        key.input,
        allow_new=False,
    )
    return found


def publish_behavior_classification(
    arena: CompletedResultArena,
    key: BehaviorBindingKey,
    behavior: FutureBehaviorClassID,
    *,
    reservation: BehaviorPublicationReservation | None = None,
) -> CompletedBehaviorClassification:
    _validate_key(arena, key)
    if type(behavior) is not FutureBehaviorClassID:
        raise TypeError("behavior publication requires a scoped class")
    arena.interfaces.resolve_future_behavior(behavior)
    arena.ledger.bump(_tiles_keys.FUTURE_BEHAVIOR_PUBLICATION_REQUESTS)
    try:
        _validate_blank_proof(arena, key, behavior)
    except BaseException:
        arena.ledger.bump(_tiles_keys.FUTURE_BEHAVIOR_PUBLICATION_FAILURES)
        raise
    value = CompletedBehaviorClassification(behavior)
    value = CompletedBehaviorClassification(
        behavior,
        arena._interface_publication_seal,
        _snapshot(key, value),
    )
    _validate_published(arena, key, value)
    found = arena._memo.get(key)
    if found is not None:
        if reservation is not None:
            reservation.close()
        if type(found) is not CompletedBehaviorClassification or found != value:
            arena.ledger.bump(_tiles_keys.FUTURE_BEHAVIOR_PUBLICATION_FAILURES)
            raise ValueError("behavior binding already has another class")
        arena.ledger.bump(_tiles_keys.FUTURE_BEHAVIOR_ALIASES)
        record_execution_cache_event(
            arena,
            "behavior",
            "late_duplicate",
            key.action,
            key.input,
        )
        return found
    stored_key = _detached_key(key)
    value = CompletedBehaviorClassification(
        behavior,
        arena._interface_publication_seal,
        _snapshot(stored_key, value),
    )
    referenced = arena._tiles_for(stored_key, value)
    reverse_entries = arena._index_entries(referenced)
    reservations = (
        (arena._memo_owner, 1, 0),
        (arena._reverse_owner, reverse_entries, 0),
    )
    if reservation is None:
        try:
            arena.ledger.reserve_many(reservations)
        except BaseException:
            arena.ledger.bump(_tiles_keys.FUTURE_BEHAVIOR_PUBLICATION_FAILURES)
            raise
    elif (
        type(reservation) is not BehaviorPublicationReservation
        or not reservation._open
        or reservation._seal is not _RESERVATION_SEAL
        or reservation._arena is not arena
        or reservation._tiles != tuple(referenced)
        or reservation._reservations != reservations
    ):
        raise ValueError("behavior publication reservation does not match its request")
    reverse_snapshot = None
    try:
        reverse_snapshot = arena._reverse_snapshot(referenced, stored_key)
        arena._memo[stored_key] = value
        for tile in referenced:
            arena._add_membership(tile, stored_key)
    except BaseException:
        if reverse_snapshot is not None:
            arena._memo.pop(stored_key, None)
            arena._restore_reverse(reverse_snapshot)
        for owner, entries, nodes in reservations:
            arena.ledger.release(owner, entries, nodes)
        if reservation is not None:
            reservation._open = False
        arena.ledger.bump(_tiles_keys.FUTURE_BEHAVIOR_PUBLICATION_FAILURES)
        raise
    if reservation is not None:
        reservation._open = False
    arena.ledger.bump(_tiles_keys.FUTURE_BEHAVIOR_BINDING_PUBLICATIONS)
    level = arena.tiles.resolve(key.input).level
    arena.tiles._cache_metrics.prepare(
        "behavior",
        "early_hit",
        spatial_level=level,
        temporal_span=temporal_span(arena.action_authority, key.action),
    )
    record_execution_cache_event(
        arena,
        "behavior",
        "publication",
        key.action,
        key.input,
    )
    return value


__all__ = [
    "BehaviorPublicationReservation",
    "UnsupportedBehaviorBinding",
    "behavior_binding_key",
    "lookup_behavior_classification",
    "publish_behavior_classification",
    "reserve_behavior_publication",
]
