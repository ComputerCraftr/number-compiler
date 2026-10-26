"""Compact reporting for already-issued Mahler center transfers."""

from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from number_compiler.sequences.antihydra.mahler_center_depth_matrix import (
        MahlerCertifiedCenterDepthTransfer,
    )


def center_transfer_packet(
    transfer: MahlerCertifiedCenterDepthTransfer,
    *,
    include_rows: bool = False,
    trace: bool = False,
) -> dict[str, object]:
    """Render one checked source-fiber relation without reissuing its cones."""
    transfer.require_issued()
    actual_edge = next(
        (
            edge
            for edge in transfer.source_fiber_edges
            if edge.source == transfer.pointed_sources[0]
        ),
        None,
    )
    if actual_edge is None or actual_edge.endpoint != transfer.pointed_sources[-1]:
        raise ArithmeticError("Mahler transfer lost its pointed source-fiber edge")
    packet: dict[str, object] = {
        **transfer.matrix.compact_packet(include_rows=include_rows),
        "conditional_matrix": transfer.conditional_composition.compact_packet(
            include_rows=include_rows
        ),
        "source_authority": "source-finite-trace",
        "safety_nonempty_rows": transfer.safety_matrix.nonempty_rows,
        "source_certified_physical_ticks": transfer.steps,
        "source_fiber_edges_certified": len(transfer.source_fiber_edges),
        "temporal_matrix_join_mode": (
            "source-fiber-action-composition"
            if transfer.composition_joins
            else "direct-source-issuance"
        ),
        "composition_joins": transfer.composition_joins,
        "equal_span_joins": transfer.equal_span_joins,
        "reissued_intermediate_source_cones_on_join": False,
        "pointed_first_center": transfer.pointed_centers[0],
        "pointed_last_center": transfer.pointed_centers[-1],
        "candidate_source_roots_refused_by_join": transfer.rejected_source_paths,
        "conditional_matrix_nonzero_entries": transfer.conditional_composition.edges,
        "conditional_relation_work": transfer.relation_work.packet(),
        "source_witness_pruned_relation_entries": sum(
            (a & ~b).bit_count()
            for a, b in zip(
                transfer.conditional_composition.rows, transfer.matrix.rows, strict=True
            )
        ),
        "fractional_and_ledger_safety": (
            "exact full-source prefix guard; ledger checked from supplied balance"
            if transfer.initial_ledger is not None
            else "exact full-source prefix guard; starting ledger not supplied"
        ),
        "actual_pointed_path_fractional_guard_nonempty": not actual_edge.future.guard.empty,
        "actual_pointed_path_ledger_safe": (
            None
            if transfer.initial_ledger is None
            else actual_edge.ledger_safe(transfer.initial_ledger)
        ),
        "indefinite_carry_driver_certified": False,
        "temporal_repeat_certified": False,
        "scope": "pointed finite full-source successor relation; width births recentered explicitly",
    }
    if trace:
        packet["trace"] = {
            "pointed_center_path": transfer.pointed_centers,
            "center_lsd_positions": transfer.center_positions,
            "width_birth_ticks": transfer.width_births,
            "low_border_carry_ports": tuple(
                None if port is None else port.packet()
                for port in transfer.low_border_carries
            ),
            "low_border_radix4_two_tick_ports": tuple(
                port.packet() for port in transfer.radix4_two_tick_ports
            ),
            "low_border_matrix_inlet_owner": "source-certified spatial carry action",
            "source_certified_bidirectional_port_punctures": tuple(
                tuple(port.packet() for port in frame)
                for frame in transfer.source_port_punctures
            ),
            "punctured_port_constraints_active": any(
                bool(frame) for frame in transfer.source_port_punctures
            ),
            "first_separating_port_punctures": transfer.first_separating_port_punctures(),
            "punctured_source_frame_counts": tuple(
                len(frame) for frame in transfer.source_port_punctures
            ),
            "source_mod99_path": transfer.radix99,
            "source_mod198_path": transfer.radix198,
            "pointed_source_decimal_widths": tuple(
                len(str(source)) for source in transfer.pointed_sources
            ),
        }
    return packet


__all__ = ["center_transfer_packet"]
