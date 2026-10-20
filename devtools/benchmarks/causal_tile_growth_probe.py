"""Cold causal-tile growth evidence in separate work and space units."""

from __future__ import annotations

import argparse
import itertools
import json
from collections.abc import Iterable
from dataclasses import asdict, dataclass
from time import perf_counter
from typing import TYPE_CHECKING, TypedDict

from number_compiler.resources.temporal_diagnostics import METRICS_SCHEMA_VERSION

if TYPE_CHECKING:
    from number_compiler.hashlife.actions.field_actions import FieldCellActionID
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )
    from number_compiler.hashlife.execution.tile_scheduler import (
        TileScheduler,
        TileSchedulerAuditSnapshot,
    )
    from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
    from number_compiler.hashlife.tiles.tile_ports import BoundPorts, ResultWiring
    from number_compiler.hashlife.tiles.tiles import TileArena
    from number_compiler.resources.ledger import ResourceLedger


WORK_FIELDS = (
    "future_behavior_requests",
    "future_behavior_binding_requests",
    "future_behavior_binding_early_hits",
    "future_behavior_classification_evaluations",
    "future_behavior_refinement_observation_checks",
    "future_behavior_refinement_successor_checks",
    "behavior_classification_summary_checks",
    "behavior_classification_port_checks",
    "behavior_point_observations",
    "behavior_width_observations",
    "exact_causal_fallback_requests",
    "tile_region_application_validation_visits",
    "causal_frames",
    "task_memo_evaluations",
    "task_memo_hits",
    "primitive_emits",
    "finite_pair_transfers",
    "finite_transfer_parent_observations",
    "result_evaluations",
    "result_hits",
    "midpoint_reuse",
    "demand_descents",
    "boundary_output_requests",
    "boundary_output_hits",
    "boundary_output_evaluations",
    "boundary_output_completions",
    "boundary_output_failures",
    "boundary_output_piece_normalizations",
    "spatial_buffer_allocations",
    "spatial_buffer_appends",
    "spatial_buffer_reversal_visits",
    "boundary_transfer_requests",
    "boundary_transfer_frames",
    "boundary_transfer_parent_observations",
    "boundary_transfer_descents",
    "directed_transfer_requests",
    "directed_transfer_early_hits",
    "directed_transfer_publication_requests",
    "directed_transfer_publications",
    "directed_transfer_late_duplicates",
    "directed_transfer_leaf_evaluations",
    "directed_transfer_parent_evaluations",
    "causal_frame_publications",
    "causal_frame_payload_reference_publications",
    "completed_result_port_validation_requests",
    "completed_result_port_validation_visits",
    "directed_transfer_validation_requests",
    "directed_transfer_validation_visits",
)
SPACE_FIELDS = (
    "action_nodes",
    "action_composition_entries",
    "completed_result_entries",
    "directed_transfer_entries",
    "causal_interface_entries",
    "powered_interface_entries",
    "fused_interface_entries",
    "spatial_interface_entries",
    "other_result_memo_entries",
    "canonical_tile_nodes",
    "retained_entries",
    "retained_nodes",
    "peak_entries",
    "peak_nodes",
    "spatial_buffer_peak_slots",
    "spatial_buffer_peak_bytes",
    "boundary_transfer_workspace_peak",
    "directed_transfer_workspace_peak",
    "causal_frame_peak_slots",
)


@dataclass(frozen=True, slots=True)
class CausalGrowthRow:
    scenario: str
    temporal_steps: int
    spatial_width: int
    coordinate: int
    temporal_exponent: int
    spatial_exponent: int
    action_physical_ticks: int
    digit: int
    setup_seconds: float
    observation_seconds: float
    diagnostics_seconds: float
    cold_seconds: float
    causal_accounting_version: int
    causal_frames: int
    task_memo_evaluations: int
    task_memo_hits: int
    primitive_emits: int
    finite_pair_transfers: int
    finite_transfer_parent_observations: int
    result_evaluations: int
    result_hits: int
    midpoint_reuse: int
    demand_descents: int
    workspace_peak_slots: int
    boundary_output_requests: int | None
    boundary_output_hits: int | None
    boundary_output_evaluations: int
    boundary_output_completions: int
    boundary_output_failures: int | None
    boundary_requested_extent: int
    boundary_cached_extent: int
    boundary_output_piece_normalizations: int
    spatial_buffer_allocations: int
    spatial_buffer_allocated_bytes: int
    spatial_buffer_appends: int
    spatial_buffer_reversal_visits: int
    spatial_buffer_live_slots: int
    spatial_buffer_live_bytes: int
    spatial_buffer_peak_slots: int
    spatial_buffer_peak_bytes: int
    boundary_transfer_requests: int
    boundary_transfer_frames: int
    boundary_transfer_parent_observations: int
    boundary_transfer_descents: int
    boundary_transfer_workspace_peak: int
    directed_transfer_requests: int
    directed_transfer_early_hits: int
    directed_transfer_publication_requests: int
    directed_transfer_publications: int
    directed_transfer_late_duplicates: int
    directed_transfer_leaf_evaluations: int
    directed_transfer_parent_evaluations: int
    directed_transfer_workspace_peak: int
    causal_frame_publications: int
    causal_frame_payload_reference_publications: int
    causal_frame_peak_slots: int
    completed_result_port_validation_requests: int
    completed_result_port_validation_visits: int
    directed_transfer_validation_requests: int
    directed_transfer_validation_visits: int
    action_nodes: int
    action_composition_entries: int
    completed_result_entries: int
    directed_transfer_entries: int
    causal_interface_entries: int
    powered_interface_entries: int
    fused_interface_entries: int
    spatial_interface_entries: int
    other_result_memo_entries: int
    canonical_tile_nodes: int
    retained_entries: int
    retained_nodes: int
    peak_entries: int
    peak_nodes: int
    semantic_contract_classes: int
    temporal_edge_classes: int
    retained_spatial_interval_bindings: int
    retained_spatial_interval_union_cells: int
    sequential_generation_advances: int
    whole_word_sweeps: int
    whole_word_symbol_visits: int
    proof_machine_applications: int
    future_behavior_requests: int | None = None
    future_behavior_binding_requests: int | None = None
    future_behavior_binding_early_hits: int | None = None
    future_behavior_classification_evaluations: int | None = None
    future_behavior_refinement_observation_checks: int | None = None
    future_behavior_refinement_successor_checks: int | None = None
    behavior_classification_summary_checks: int | None = None
    behavior_classification_port_checks: int | None = None
    behavior_point_observations: int | None = None
    behavior_width_observations: int | None = None
    exact_causal_fallback_requests: int | None = None
    tile_region_application_validation_visits: int | None = None
    causal_extent_discharged_by_behavior: int | None = None


@dataclass(frozen=True, slots=True)
class _IntervalDiagnostics:
    semantic_contract_classes: int
    temporal_edge_classes: int
    spatial_interval_bindings: int
    spatial_interval_union_cells: int


def _exact_counter(counters: dict[str, int], name: str) -> int:
    value = counters.get(name, 0)
    if type(value) is not int or value < 0:
        raise AssertionError(("causal-probe-counter", name, value))
    return value


def _versioned_counter(
    counters: dict[str, int], name: str, accounting_version: int
) -> int | None:
    if accounting_version < 1:
        return None
    return _exact_counter(counters, name)


def _pair_from_integer(value: int, base: int) -> tuple[int, ...]:
    if type(value) is not int or value < 0 or type(base) is not int or base < 2:
        raise ValueError("causal probe source requires a nonnegative integer and radix")
    digits: list[int] = []
    current = value
    while current:
        digits.append(current % base)
        current //= base
    if not digits:
        digits.append(0)
    return tuple(digit + digits[-1 - index] for index, digit in enumerate(digits))


def power_of_two_at_least(value: int) -> int:
    if type(value) is not int or value < 1:
        raise ValueError("causal probe width requires a positive exact integer")
    return 1 << (value - 1).bit_length()


def runtime(
    base: int,
) -> tuple[
    ResourceLedger,
    TileArena,
    PrimitiveTileKernelAdapter,
    FieldCellActionID,
    TileScheduler,
]:
    from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
    from number_compiler.arithmetic.functions.semantic_functions import (
        SemanticFunctionArena,
    )
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
    from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena
    from number_compiler.hashlife.interfaces.diamond_quotient import (
        DiamondQuotientArena,
    )
    from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
    from number_compiler.hashlife.tiles.tiles import TileArena
    from number_compiler.resources.ledger import ResourceLedger

    ledger = ResourceLedger()
    kernels = DiamondKernelArena(ledger)
    interfaces = DiamondQuotientArena(SemanticFunctionArena(ledger))
    tiles = TileArena(ledger)
    adapter = PrimitiveTileKernelAdapter(tiles, kernels, interfaces)
    action = adapter.admit(BaseBlockEffect(base))
    results = CompletedResultArena(
        tiles,
        interfaces,
        action_authority=adapter,
        validate_action=adapter.validate_action,
        signature_for=adapter.signature_for,
    )
    adapter.attach_results(results)
    return ledger, tiles, adapter, action, TileScheduler(tiles, results, adapter)


def _wiring_key(wiring: ResultWiring) -> tuple[int, int, int]:
    return wiring.signature.local_id, wiring.orientation, wiring.phase


def _bound_semantics(bound: BoundPorts) -> tuple[tuple[int, ...], tuple[int, int, int]]:
    return bound.ports, _wiring_key(bound.wiring)


def _interval_diagnostics(
    scheduler: TileScheduler,
    application: int,
    scheduler_view: TileSchedulerAuditSnapshot,
) -> _IntervalDiagnostics:
    """Compare semantic contracts with exact spatial interval bindings.

    This reads IDs, action edges, ports, and relative intervals only. It never
    resolves a tile symbol or observes a future digit.
    """
    semantic: set[tuple[object, ...]] = set()
    edges: set[tuple[int, int | None, int | None]] = set()
    spatial: set[tuple[object, ...]] = set()
    intervals: dict[tuple[int, int], list[tuple[int, int]]] = {}

    def add_view(view: BoundaryTileView | None) -> None:
        if view is None:
            return
        identity = view.tile.local_id, view.orientation
        intervals.setdefault(identity, []).append(
            (view.source_offset, view.source_offset + view.relative_extent)
        )

    for owner, key in scheduler_view.pins:
        if owner != application:
            continue
        children = scheduler.adapter.action_children(key.action)
        before = None if children is None else children[0].local_id
        after = None if children is None else children[1].local_id
        edges.add((key.action.local_id, before, after))
        fusion = None
        if key.fusion is not None:
            fusion = (
                _bound_semantics(key.fusion.producer),
                _bound_semantics(key.fusion.consumer),
            )
        semantic.add((key.action.local_id, key.ports, _wiring_key(key.wiring), fusion))
        views = [key.boundaries.left, key.boundaries.right]
        if key.fusion is not None:
            views.extend(
                (
                    key.fusion.producer.boundaries.left,
                    key.fusion.producer.boundaries.right,
                    key.fusion.consumer.boundaries.left,
                    key.fusion.consumer.boundaries.right,
                )
            )
        spatial.add(
            (
                key.action.local_id,
                key.input.local_id,
                key.region,
                tuple(
                    None
                    if view is None
                    else (
                        view.tile.local_id,
                        view.source_offset,
                        view.relative_extent,
                        view.orientation,
                        view.relative_origin,
                    )
                    for view in views
                ),
            )
        )
        for view in views:
            add_view(view)
    union = 0
    for pieces in intervals.values():
        end = -1
        for low, high in sorted(pieces):
            if high <= end:
                continue
            union += high - max(low, end)
            end = high
    return _IntervalDiagnostics(len(semantic), len(edges), len(spatial), union)


def cold_row(
    scenario: str,
    temporal_steps: int,
    spatial_width: int,
    *,
    coordinate: int,
    seed: int = 196,
    base: int = 10,
) -> tuple[CausalGrowthRow, object]:
    """Run one point on a fresh index and return its ledger identity separately."""
    cold_started = perf_counter()
    if scenario not in ("fixed-width", "fixed-depth", "growing-196"):
        raise ValueError("unknown causal growth scenario")
    if type(temporal_steps) is not int or temporal_steps < 1:
        raise ValueError("causal temporal depth requires a positive exact integer")
    if (
        type(spatial_width) is not int
        or spatial_width < 1
        or spatial_width & (spatial_width - 1)
    ):
        raise ValueError("causal spatial width requires a positive power of two")
    if type(coordinate) is not int or not 0 <= coordinate < spatial_width:
        raise ValueError("causal coordinate lies outside its spatial probe")
    ledger, tiles, adapter, primitive, scheduler = runtime(base)
    pair = _pair_from_integer(seed, base)
    if len(pair) > spatial_width:
        raise ValueError("causal spatial width cannot contain the source pair")
    blank = adapter.primitive_law(primitive).blank
    from number_compiler.arithmetic.contracts.exact_tree_context import (
        OriginalSourceConstruction,
    )
    from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
    from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
    from number_compiler.hashlife.observation.tile_projection import import_exact_source

    exact = ExactSource(
        pair,
        base,
        blank=blank,
        extent=spatial_width,
        alphabet_size=blank,
    )
    construction = OriginalSourceConstruction(exact)
    geometry = SourceGeometry(ledger, exact, construction)
    source = import_exact_source(exact, geometry, tiles, adapter.alphabet(primitive))
    if scenario == "growing-196":
        from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect

        terminal = adapter.admit(DigitNormalizeBlockEffect(base))
        action = (
            terminal
            if temporal_steps == 1
            else adapter.compose(adapter.power(primitive, temporal_steps - 1), terminal)
        )
    else:
        action = adapter.power(primitive, temporal_steps)
    action_ticks = adapter.action_cocycle(action).physical_ticks
    observation_started = perf_counter()
    setup_seconds = observation_started - cold_started
    try:
        with scheduler.application(
            action,
            source.tile,
            adapter.initial_ports(action),
            adapter.wiring(action),
        ) as application:
            digit = application.point(coordinate)
            observation_finished = perf_counter()
            observation_seconds = observation_finished - observation_started
            cold_seconds = observation_finished - cold_started
            diagnostics_started = perf_counter()
            scheduler_view = scheduler.audit_snapshot()
            diagnostics = _interval_diagnostics(
                scheduler, application.identity, scheduler_view
            )
            result_view = scheduler.results.audit_snapshot()
            adapter_view = adapter.audit_snapshot()
            tile_view = tiles.audit_snapshot()
            snapshot = ledger.snapshot()
            counters = dict(snapshot.counters)
            memo_key_counts: dict[str, int] = {}
            for memo_key in result_view.memo:
                name = type(memo_key).__name__
                memo_key_counts[name] = memo_key_counts.get(name, 0) + 1
            diagnostics_seconds = perf_counter() - diagnostics_started
            accounting_version = _exact_counter(
                counters, "tile_causal_accounting_version"
            )
            row = CausalGrowthRow(
                scenario=scenario,
                temporal_steps=temporal_steps,
                spatial_width=spatial_width,
                coordinate=coordinate,
                temporal_exponent=max(0, temporal_steps.bit_length() - 1),
                spatial_exponent=max(0, spatial_width.bit_length() - 1),
                action_physical_ticks=action_ticks,
                digit=digit,
                setup_seconds=setup_seconds,
                observation_seconds=observation_seconds,
                diagnostics_seconds=diagnostics_seconds,
                cold_seconds=cold_seconds,
                causal_accounting_version=accounting_version,
                causal_frames=_exact_counter(counters, "tile_causal_frames"),
                task_memo_evaluations=_exact_counter(
                    counters, "tile_causal_task_memo_evaluations"
                ),
                task_memo_hits=_exact_counter(counters, "tile_causal_task_memo_hits"),
                primitive_emits=_exact_counter(counters, "tile_causal_primitive_emits"),
                finite_pair_transfers=_exact_counter(
                    counters, "tile_causal_finite_pair_transfers"
                ),
                finite_transfer_parent_observations=_exact_counter(
                    counters, "tile_causal_finite_transfer_parent_observations"
                ),
                result_evaluations=_exact_counter(
                    counters, "tile_causal_result_evaluations"
                ),
                result_hits=_exact_counter(counters, "tile_causal_result_hits"),
                midpoint_reuse=_exact_counter(counters, "tile_causal_midpoint_reuse"),
                demand_descents=_exact_counter(
                    counters, "tile_scheduler_demand_descents"
                ),
                workspace_peak_slots=_exact_counter(
                    counters, "tile_causal_workspace_peak"
                ),
                boundary_output_requests=_versioned_counter(
                    counters,
                    "tile_causal_boundary_output_requests",
                    accounting_version,
                ),
                boundary_output_hits=_versioned_counter(
                    counters, "tile_causal_boundary_output_hits", accounting_version
                ),
                boundary_output_evaluations=_exact_counter(
                    counters, "tile_causal_boundary_output_evaluations"
                ),
                boundary_output_completions=_exact_counter(
                    counters, "tile_causal_boundary_output_completions"
                ),
                boundary_output_failures=_versioned_counter(
                    counters,
                    "tile_causal_boundary_output_failures",
                    accounting_version,
                ),
                boundary_requested_extent=_exact_counter(
                    counters, "tile_causal_boundary_output_requested_extent"
                ),
                boundary_cached_extent=_exact_counter(
                    counters, "tile_causal_boundary_output_cached_extent"
                ),
                boundary_output_piece_normalizations=_exact_counter(
                    counters, "tile_causal_boundary_output_piece_normalizations"
                ),
                spatial_buffer_allocations=_exact_counter(
                    counters, "tile_causal_spatial_buffer_allocations"
                ),
                spatial_buffer_allocated_bytes=_exact_counter(
                    counters, "tile_causal_spatial_buffer_allocated_bytes"
                ),
                spatial_buffer_appends=_exact_counter(
                    counters, "tile_causal_spatial_buffer_appends"
                ),
                spatial_buffer_reversal_visits=_exact_counter(
                    counters, "tile_causal_spatial_buffer_reversal_visits"
                ),
                spatial_buffer_live_slots=(
                    scheduler_view.causal_workspace.slots
                    if scheduler_view.causal_workspace is not None
                    else 0
                ),
                spatial_buffer_live_bytes=(
                    scheduler_view.causal_workspace.object_bytes
                    + scheduler_view.causal_workspace.reference_store.backing_bytes
                    + scheduler_view.causal_workspace.buffer_store.backing_bytes
                    if scheduler_view.causal_workspace is not None
                    else 0
                ),
                spatial_buffer_peak_slots=_exact_counter(
                    counters, "tile_causal_spatial_buffer_peak_slots"
                ),
                spatial_buffer_peak_bytes=_exact_counter(
                    counters, "tile_causal_spatial_buffer_peak_bytes"
                ),
                boundary_transfer_requests=_exact_counter(
                    counters, "tile_boundary_transfer_requests"
                ),
                boundary_transfer_frames=_exact_counter(
                    counters, "tile_boundary_transfer_frames"
                ),
                boundary_transfer_parent_observations=_exact_counter(
                    counters, "tile_boundary_transfer_parent_observations"
                ),
                boundary_transfer_descents=_exact_counter(
                    counters, "tile_boundary_transfer_descents"
                ),
                boundary_transfer_workspace_peak=_exact_counter(
                    counters, "tile_boundary_transfer_workspace_peak"
                ),
                directed_transfer_requests=_exact_counter(
                    counters, "tile_directed_transfer_requests"
                ),
                directed_transfer_early_hits=_exact_counter(
                    counters, "tile_directed_transfer_early_hits"
                ),
                directed_transfer_publication_requests=_exact_counter(
                    counters, "tile_directed_transfer_publication_requests"
                ),
                directed_transfer_publications=_exact_counter(
                    counters, "tile_directed_transfer_publications"
                ),
                directed_transfer_late_duplicates=_exact_counter(
                    counters, "tile_directed_transfer_late_duplicates"
                ),
                directed_transfer_leaf_evaluations=_exact_counter(
                    counters, "tile_directed_transfer_leaf_evaluations"
                ),
                directed_transfer_parent_evaluations=_exact_counter(
                    counters, "tile_directed_transfer_parent_evaluations"
                ),
                directed_transfer_workspace_peak=_exact_counter(
                    counters, "tile_directed_transfer_workspace_peak"
                ),
                causal_frame_publications=_exact_counter(
                    counters, "tile_causal_frame_publications"
                ),
                causal_frame_payload_reference_publications=_exact_counter(
                    counters, "tile_causal_frame_payload_reference_publications"
                ),
                causal_frame_peak_slots=_exact_counter(
                    counters, "tile_causal_frame_peak_slots"
                ),
                completed_result_port_validation_requests=_exact_counter(
                    counters, "completed_result_port_validation_requests"
                ),
                completed_result_port_validation_visits=_exact_counter(
                    counters, "completed_result_port_validation_visits"
                ),
                directed_transfer_validation_requests=_exact_counter(
                    counters, "tile_directed_transfer_validation_requests"
                ),
                directed_transfer_validation_visits=_exact_counter(
                    counters, "tile_directed_transfer_validation_visits"
                ),
                action_nodes=len(adapter_view.actions),
                action_composition_entries=len(adapter_view.compositions),
                completed_result_entries=memo_key_counts.get("PoweredResultKey", 0),
                directed_transfer_entries=memo_key_counts.get("DirectedTransferKey", 0),
                causal_interface_entries=memo_key_counts.get("CausalInterfaceKey", 0),
                powered_interface_entries=memo_key_counts.get("PoweredInterfaceKey", 0),
                fused_interface_entries=memo_key_counts.get("FusedInterfaceKey", 0),
                spatial_interface_entries=memo_key_counts.get("SpatialInterfaceKey", 0),
                other_result_memo_entries=sum(memo_key_counts.values())
                - sum(
                    memo_key_counts.get(name, 0)
                    for name in (
                        "PoweredResultKey",
                        "DirectedTransferKey",
                        "CausalInterfaceKey",
                        "PoweredInterfaceKey",
                        "FusedInterfaceKey",
                        "SpatialInterfaceKey",
                    )
                ),
                canonical_tile_nodes=len(tile_view.nodes),
                retained_entries=snapshot.entries,
                retained_nodes=snapshot.nodes,
                peak_entries=snapshot.peak_entries,
                peak_nodes=snapshot.peak_nodes,
                semantic_contract_classes=diagnostics.semantic_contract_classes,
                temporal_edge_classes=diagnostics.temporal_edge_classes,
                retained_spatial_interval_bindings=diagnostics.spatial_interval_bindings,
                retained_spatial_interval_union_cells=diagnostics.spatial_interval_union_cells,
                sequential_generation_advances=_exact_counter(
                    counters, "sequential_generation_advances"
                ),
                whole_word_sweeps=_exact_counter(counters, "whole_word_sweeps"),
                whole_word_symbol_visits=_exact_counter(
                    counters, "whole_word_symbol_visits"
                ),
                proof_machine_applications=_exact_counter(
                    counters, "proof_machine_applications"
                ),
                future_behavior_requests=_exact_counter(
                    counters, "future_behavior_requests"
                ),
                future_behavior_binding_requests=_exact_counter(
                    counters, "future_behavior_binding_requests"
                ),
                future_behavior_binding_early_hits=_exact_counter(
                    counters, "future_behavior_binding_early_hits"
                ),
                future_behavior_classification_evaluations=_exact_counter(
                    counters, "future_behavior_classification_evaluations"
                ),
                future_behavior_refinement_observation_checks=_exact_counter(
                    counters, "future_behavior_refinement_observation_checks"
                ),
                future_behavior_refinement_successor_checks=_exact_counter(
                    counters, "future_behavior_refinement_successor_checks"
                ),
                behavior_classification_summary_checks=_exact_counter(
                    counters, "behavior_classification_summary_checks"
                ),
                behavior_classification_port_checks=_exact_counter(
                    counters, "behavior_classification_port_checks"
                ),
                behavior_point_observations=_exact_counter(
                    counters, "behavior_point_observations"
                ),
                behavior_width_observations=_exact_counter(
                    counters, "behavior_width_observations"
                ),
                exact_causal_fallback_requests=_exact_counter(
                    counters, "exact_causal_fallback_requests"
                ),
                tile_region_application_validation_visits=_exact_counter(
                    counters,
                    "tile_region_application_validation_visits",
                ),
                causal_extent_discharged_by_behavior=_exact_counter(
                    counters, "causal_extent_discharged_by_behavior"
                ),
            )
    finally:
        source.close()
    return row, ledger


def _growth_steps(
    rows: tuple[CausalGrowthRow, ...], axis: str, field: str
) -> list[dict[str, int | None]]:
    output: list[dict[str, int | None]] = []
    for previous, current in itertools.pairwise(rows):
        before = getattr(previous, axis)
        after = getattr(current, axis)
        old = getattr(previous, field)
        new = getattr(current, field)
        if old is not None and type(old) is not int:
            raise AssertionError((field, old))
        if new is not None and type(new) is not int:
            raise AssertionError((field, new))
        output.append(
            {
                "previous_axis": before,
                "current_axis": after,
                "previous": old,
                "current": new,
                "increment": None if old is None or new is None else new - old,
                "twice_previous_excess": (
                    None if old is None or new is None else new - 2 * old
                ),
            }
        )
    return output


class CausalSeriesReport(TypedDict):
    status: str
    measurements_complete: bool
    axis: str
    expected_axis: list[int]
    observed_axis: list[int]
    rows: list[dict[str, object]]
    raw_work_growth: dict[str, list[dict[str, int | None]]]
    raw_space_growth: dict[str, list[dict[str, int | None]]]
    raw_boundary_extent_growth: list[dict[str, int | None]]
    raw_boundary_cached_extent_growth: list[dict[str, int | None]]
    raw_buffer_byte_growth: list[dict[str, int | None]]
    units: dict[str, str]
    doubling_envelopes: dict[str, bool | None]
    logarithmic_increment_envelopes: dict[str, bool | None]
    forbidden_execution_zero: bool
    release_blockers: list[str]
    logarithmic_execution_claim: bool
    interval_union_scope: str


def series_report(
    rows: Iterable[CausalGrowthRow],
    expected_axis: Iterable[int],
    *,
    axis: str,
) -> CausalSeriesReport:
    """Analyze each counter independently and fail closed on missing samples."""
    values = tuple(rows)
    expected = tuple(expected_axis)
    observed = tuple(getattr(row, axis) for row in values)
    complete = len(values) >= 2 and observed == expected
    work_steps = {field: _growth_steps(values, axis, field) for field in WORK_FIELDS}
    space_steps = {field: _growth_steps(values, axis, field) for field in SPACE_FIELDS}
    linear_envelopes: dict[str, bool | None] = {}
    logarithmic_envelopes: dict[str, bool | None] = {}
    for field in (*WORK_FIELDS, *SPACE_FIELDS):
        if not values or not complete:
            linear_envelopes[field] = None
            logarithmic_envelopes[field] = None
            continue
        bootstrap = getattr(values[0], field)
        observed_field = tuple(getattr(row, field) for row in values)
        if any(value is None for value in observed_field):
            linear_envelopes[field] = None
            logarithmic_envelopes[field] = None
            continue
        if type(bootstrap) is not int:
            raise AssertionError((field, bootstrap))
        pairs = tuple(itertools.pairwise(values))
        linear_envelopes[field] = all(
            getattr(current, axis) == 2 * getattr(previous, axis)
            and int(getattr(current, field))
            <= 2 * int(getattr(previous, field)) + bootstrap
            for previous, current in pairs
        )
        logarithmic_envelopes[field] = all(
            getattr(current, axis) == 2 * getattr(previous, axis)
            and int(getattr(current, field))
            <= int(getattr(previous, field)) + bootstrap
            for previous, current in pairs
        )
    forbidden = all(
        row.sequential_generation_advances == 0
        and row.whole_word_sweeps == 0
        and row.whole_word_symbol_visits == 0
        and row.proof_machine_applications == 0
        for row in values
    )
    blockers: list[str] = []
    if not complete:
        blockers.append("measurement_series_incomplete")
    else:
        if not forbidden:
            blockers.append("forbidden_execution_work_observed")
        for field in WORK_FIELDS:
            if logarithmic_envelopes[field] is None:
                blockers.append(f"{field}_measurement_unavailable")
            elif logarithmic_envelopes[field] is False:
                blockers.append(f"{field}_exceeds_logarithmic_increment_envelope")
        for field in SPACE_FIELDS:
            if linear_envelopes[field] is False:
                blockers.append(f"{field}_exceeds_doubling_envelope")
    return {
        "status": "RED" if blockers else "MEASURED_PASS",
        "measurements_complete": complete,
        "axis": axis,
        "expected_axis": list(expected),
        "observed_axis": list(observed),
        "rows": [asdict(row) for row in values],
        "raw_work_growth": work_steps,
        "raw_space_growth": space_steps,
        "raw_boundary_extent_growth": _growth_steps(
            values, axis, "boundary_requested_extent"
        ),
        "raw_boundary_cached_extent_growth": _growth_steps(
            values, axis, "boundary_cached_extent"
        ),
        "raw_buffer_byte_growth": _growth_steps(
            values, axis, "spatial_buffer_allocated_bytes"
        ),
        "units": {
            "work": "monotone operation counts",
            "space": "retained or peak counts, analyzed per field",
            "boundary_requested_extent": "sum of requested source cells",
            "spatial_buffer_allocated_bytes": "cumulative backing bytes allocated",
        },
        "doubling_envelopes": linear_envelopes,
        "logarithmic_increment_envelopes": logarithmic_envelopes,
        "forbidden_execution_zero": forbidden,
        "release_blockers": blockers,
        "logarithmic_execution_claim": False,
        "interval_union_scope": (
            "retained application result keys only; evicted requests and cache-hit "
            "coverage are unavailable"
        ),
    }


def cold_rows(
    requests: Iterable[tuple[str, int, int, int]],
) -> tuple[CausalGrowthRow, ...]:
    rows: list[CausalGrowthRow] = []
    ledgers: list[object] = []
    for scenario, temporal, width, coordinate in requests:
        row, ledger = cold_row(
            scenario,
            temporal,
            width,
            coordinate=coordinate,
        )
        if any(ledger is previous for previous in ledgers):
            raise AssertionError("causal cold probe reused an index ledger")
        ledgers.append(ledger)
        rows.append(row)
    return tuple(rows)


def run_probe(
    *,
    temporal_steps: Iterable[int] = (4, 8, 16),
    spatial_widths: Iterable[int] = (4, 8, 16),
    fixed_width: int = 8,
    fixed_depth: int = 8,
) -> dict[str, object]:
    temporal = tuple(temporal_steps)
    widths = tuple(spatial_widths)
    if any(
        type(value) is not int or value < 1 or value & (value - 1)
        for value in (*temporal, *widths)
    ):
        raise ValueError("causal growth axes require positive exact powers of two")
    fixed_width_rows = cold_rows(
        ("fixed-width", steps, fixed_width, min(2, fixed_width - 1))
        for steps in temporal
    )
    fixed_depth_rows = cold_rows(
        ("fixed-depth", fixed_depth, width, min(2, width - 1)) for width in widths
    )
    growing_requests: list[tuple[str, int, int, int]] = []
    for steps in temporal:
        width = power_of_two_at_least(3 + steps)
        growing_requests.append(("growing-196", steps, width, 0))
    growing_rows = cold_rows(growing_requests)
    reports = {
        "fixed_width_temporal": series_report(
            fixed_width_rows,
            temporal,
            axis="temporal_steps",
        ),
        "fixed_depth_spatial": series_report(
            fixed_depth_rows,
            widths,
            axis="spatial_width",
        ),
        "growing_196": series_report(
            growing_rows,
            temporal,
            axis="temporal_steps",
        ),
    }
    complete = all(bool(report["measurements_complete"]) for report in reports.values())
    blocked = any(report["status"] == "RED" for report in reports.values())
    return {
        "metrics_schema_version": METRICS_SCHEMA_VERSION,
        "probe_policy": "fresh-index-single-cold-point-no-acceleration",
        "measurements_complete": complete,
        "status": "RED" if blocked or not complete else "MEASURED_PASS",
        "logarithmic_execution_claim": False,
        "coordinate_policy": (
            "scaling series observes coordinate zero; midpoint and last-active "
            "coordinates are separate explicit cold_row diagnostics"
        ),
        "series": reports,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-exponent", type=int, default=4)
    args = parser.parse_args(argv)
    if not 2 <= args.max_exponent <= 10:
        parser.error("--max-exponent must lie between 2 and 10")
    axis = tuple(1 << exponent for exponent in range(2, args.max_exponent + 1))
    print(
        json.dumps(
            run_probe(temporal_steps=axis), sort_keys=True, separators=(",", ":")
        )
    )
    return 0


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
