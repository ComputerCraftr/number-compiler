"""Snapshot-only accounting for guarded cellular temporal composition."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass


@dataclass(frozen=True, slots=True)
class CellularTemporalWork:
    """Actual construction counts, separate from represented physical time."""

    family: str
    primitive_transformations: int | None
    direct_two_step_squares: int | None
    represented_growth_cells: int | None
    powered_publications: int | None
    represented_two_step_steps: int | None
    cone_misses: int | None
    cone_hits: int | None
    boundary_classifications: int | None
    boundary_node_visits: int | None
    tile_selections: int | None
    weighted_carry_ports: int | None
    moment_ports: int | None
    affine_ports: int | None
    bit_budget_refusals: int | None


def collect_cellular_work(
    counters: Mapping[str, int],
) -> tuple[CellularTemporalWork, ...]:
    """Read instrumented counts only; an absent counter is never measured zero."""
    prefix = "double_reverse_"
    if not any(name.startswith(prefix) for name in counters):
        return ()
    names = (
        "spatial_transducer_applications",
        "temporal_square_applications",
        "represented_growth_cells",
        "temporal_hashlife_publications",
        "hashlife_powered_t2_steps",
        "hashlife_cones",
        "hashlife_cone_hits",
        "boundary_classifications",
        "boundary_node_visits",
        "hashlife_tile_selections",
        "weighted_carry_port_publications",
        "temporal_moment_port_publications",
        "temporal_affine_port_publications",
        "hashlife_bit_budget_refusals",
    )
    values = tuple(counters.get(prefix + name) for name in names)
    if any(
        value is not None and (type(value) is not int or value < 0) for value in values
    ):
        raise ValueError("cellular construction counters must be nonnegative integers")
    return (CellularTemporalWork("2rev10", *values),)
