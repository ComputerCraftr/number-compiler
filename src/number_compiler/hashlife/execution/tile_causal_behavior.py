"""Certified blank-output reuse within the existing causal scheduler.

This is an output dependency optimization, not a replacement executor.  The
finite certificate proves a homogeneous action preserves a blank region for
every right context.  The consumer can therefore use the already canonical
input view.  Producer exits and physical weights are *not* fabricated: the
ordinary result tasks still compute them when an observation requires them.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.hashlife.behavior.future_behavior import (
    FutureBehaviorClassID,
    FutureBehaviorProfileID,
    UnsupportedFutureBehaviorProfile,
)
from number_compiler.hashlife.execution.tile_causal_results import (
    PrimitiveCausalPorts,
    causal_result_key,
)
from number_compiler.hashlife.tiles.tile_behavior_memo import (
    UnsupportedBehaviorBinding,
    behavior_binding_key,
    lookup_behavior_classification,
    publish_behavior_classification,
    reserve_behavior_publication,
)
from number_compiler.hashlife.tiles.tile_boundaries import (
    BoundaryTileOperands,
    BoundaryTileView,
)
from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
from number_compiler.hashlife.tiles.tile_result_validation import (
    validate_boundary_operands,
)
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)
from number_compiler.resources.metric_keys import shared as _shared_keys

if TYPE_CHECKING:
    from number_compiler.hashlife.actions.field_actions import FieldCellActionID
    from number_compiler.hashlife.execution.tile_causal import CausalTileEngine


def _blank_view(engine: CausalTileEngine, view: BoundaryTileView | None) -> bool:
    if view is None:
        return True
    validate_boundary_operands(engine.tiles, BoundaryTileOperands(view))
    # A wholly inactive parent proves every clipped subregion inactive too.
    # Active parents deliberately decline here; no output or leaf scan occurs.
    engine.ledger.bump(_execution_keys.BEHAVIOR_CLASSIFICATION_SUMMARY_CHECKS)
    return engine.tiles.resolve(view.tile).first_active is None


def quiescent_boundary(
    engine: CausalTileEngine,
    action: FieldCellActionID,
    side: int,
    view: BoundaryTileView,
    anchor: object,
    argument: object,
    *,
    discharged_extent: int | None = None,
) -> BoundaryTileView | None:
    """Reuse exact blank content after a completed behavioral proof.

    Only the dependency's output is observed here.  In particular, this does
    not turn the class into a complete result with made-up outgoing ports.
    """
    if type(side) is not int or side not in (0, 1):
        raise ValueError("behavioral dependency requires an exact direction")
    if discharged_extent is None:
        discharged_extent = view.relative_extent
    if (
        type(discharged_extent) is not int
        or not 0 <= discharged_extent <= view.relative_extent
    ):
        raise ValueError("behavioral discharge extent escaped the requested view")
    token = engine._action_admission_token
    if token is None:
        record = engine.adapter._action(action)
        kernel_id = record.kernel
    else:
        from number_compiler.resources.causal_workspace import (
            CausalActionAdmission,
        )

        if type(token) is not CausalActionAdmission:
            raise TypeError("behavior requires a causal admission lease")
        _signature, kernel_id, record = (
            engine.scheduler._causal_tasks.admitted_action_metadata(
                token, engine.adapter, action
            )
        )
    if not record.homogeneous or not _blank_view(engine, view):
        engine.ledger.bump(_execution_keys.EXACT_CAUSAL_FALLBACK_REQUESTS)
        return None
    left, right = (argument, anchor) if side else (anchor, argument)
    key: PoweredResultKey | None
    if record.children is None:
        if type(left) is not int or type(right) is not int:
            raise TypeError("primitive behavior requires two finite contexts")
        key = causal_result_key(
            engine.scheduler.results,
            action,
            view.tile,
            PrimitiveCausalPorts(left, right),
            engine._wiring(action),
            action_admission=engine._action_admission_token,
        )
    else:
        key = engine._composite_key(action, view.tile, left, right)
        if key is None:
            engine.ledger.bump(_execution_keys.EXACT_CAUSAL_FALLBACK_REQUESTS)
            return None
    # The action record is authenticated above when a run admission is live.
    # Composite actions refer to their primitive behavioral kernel, so resolve
    # that admitted kernel ID without asking the adapter to treat the composite
    # action itself as a primitive law.
    kernel = engine.adapter.kernels.kernel(kernel_id)
    behavior = kernel.behavior
    if behavior is None:
        engine.ledger.bump(_execution_keys.EXACT_CAUSAL_FALLBACK_REQUESTS)
        return None
    # The profile and certificate are admitted once per immutable kernel in
    # the existing quotient arena.  Warm bindings bypass proof evaluation.
    admitted = engine.adapter.quotients.lookup_quiescent_blank(behavior)
    reservation = (
        reserve_behavior_publication(engine.scheduler.results, key)
        if admitted is None
        else None
    )
    admitted_now = False
    profile: FutureBehaviorProfileID | None = None
    behavior_class: FutureBehaviorClassID | None = None
    try:
        if admitted is None:
            try:
                profile, behavior_class = (
                    engine.adapter.quotients.admit_quiescent_blank(behavior)
                )
                admitted_now = True
            except UnsupportedFutureBehaviorProfile:
                engine.ledger.bump(_execution_keys.EXACT_CAUSAL_FALLBACK_REQUESTS)
                return None
        else:
            profile, behavior_class = admitted
        binding = behavior_binding_key(key, profile)
        completed = lookup_behavior_classification(engine.scheduler.results, binding)
        if completed is None:
            try:
                completed = publish_behavior_classification(
                    engine.scheduler.results,
                    binding,
                    behavior_class,
                    reservation=reservation,
                )
            except UnsupportedBehaviorBinding:
                if admitted_now:
                    engine.adapter.quotients.rollback_quiescent_blank_admission(
                        behavior,
                        profile,
                        behavior_class,
                    )
                    admitted_now = False
                engine.ledger.bump(_execution_keys.EXACT_CAUSAL_FALLBACK_REQUESTS)
                return None
        if completed.behavior != behavior_class:
            raise ValueError("behavior binding resolved another certified class")
    except BaseException:
        if admitted_now:
            assert profile is not None and behavior_class is not None
            engine.adapter.quotients.rollback_quiescent_blank_admission(
                behavior,
                profile,
                behavior_class,
            )
        raise
    finally:
        if reservation is not None:
            reservation.close()
    engine.ledger.bump(
        _shared_keys.CAUSAL_EXTENT_DISCHARGED_BY_BEHAVIOR, discharged_extent
    )
    engine.ledger.bump(_execution_keys.TILE_CAUSAL_QUIESCENT_BOUNDARY_REUSES)
    return BoundaryTileView(
        view.tile,
        0,
        view.relative_extent,
        view.orientation,
        view.source_offset,
    )


__all__ = ["quiescent_boundary"]
