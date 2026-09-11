"""One named projection of a captured index snapshot into powered-term views."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import fields
from typing import TypeVar, cast

from number_compiler.resources.metric_records import (
    HashLifeProjectionMetrics,
    LedgerMetrics,
)

_MetricT = TypeVar("_MetricT", bound=LedgerMetrics)

# Renames retained by the public reverse/add view; values come from the index.
_ALIASES = {
    "hashlife_section_cache_entries": "section_cache_entries",
    "hashlife_section_cache_hits": "section_cache_hits",
    "hashlife_tile_roots": "canonical_tile_roots",
    "hashlife_leaf_cache_entries": "leaf_word_cache_entries",
    "hashlife_leaf_cache_hits": "leaf_word_cache_hits",
    "hashlife_boundary_cache_entries": "boundary_cache_entries",
    "hashlife_boundary_cache_hits": "boundary_cache_hits",
    "hashlife_forest_chunks": "dyadic_forest_chunks",
    "hashlife_max_level": "dyadic_max_level",
    "hashlife_temporal_leaf_applications": "temporal_leaf_applications",
    "hashlife_high_level_tile_hits": "high_level_tile_hits",
    "hashlife_finite_action_unique": "finite_action_unique",
    "hashlife_finite_action_alias_hits": "finite_action_alias_hits",
    "hashlife_finite_action_tile_hits": "finite_action_tile_hits",
    "hashlife_finite_action_retained_entries": "finite_action_retained_entries",
    "hashlife_finite_action_mirror_alias_hits": "finite_action_mirror_alias_hits",
    "hashlife_finite_action_conjugate_alias_hits": "finite_action_conjugate_alias_hits",
    "hashlife_peak_live_tile_roots": "peak_live_tile_roots",
    "hashlife_tile_observations": "tile_observations",
    "hashlife_direct_powered_point_queries": "direct_powered_point_queries",
    "hashlife_high_level_tile_misses": "high_level_tile_misses",
}

# These retired subsystem counters no longer have columns on the index view.
# Read their observed runtime value, including absence, from its same snapshot.
_RETIRED_COUNTERS = frozenset(
    (
        "run_action_cache_entries",
        "spacetime_primitive_field_steps",
        "spacetime_primitive_slab_steps",
        "spacetime_slab_jump_entries",
        "spacetime_jump_entries",
        "spacetime_affine_apply_entries",
        "spacetime_carry_projection_entries",
        "spacetime_carry_projection_hits",
        "spacetime_carry_unique_actions",
        "spacetime_carry_action_alias_hits",
        "spacetime_carry_mirror_alias_hits",
        "spacetime_carry_conjugate_alias_hits",
        "spacetime_domain_canonical_refs",
        "spacetime_finite_cell_alphabet",
        "spacetime_terminal_projection_entries",
        "spacetime_forcing_classes",
        "spacetime_forcing_history_aliases",
        "spacetime_forcing_source_hits",
        "spacetime_forcing_carry_behavior_classes",
        "spacetime_forcing_carry_behavior_aliases",
        "spacetime_primitive_forcing_steps",
        "spacetime_forcing_jump_entries",
        "spacetime_forcing_occurrences",
        "spacetime_forcing_action_aliases",
        "spacetime_forcing_successor_conflicts",
        "spacetime_forcing_exact_target_conflicts",
    )
)


def project_powered_metrics(
    kind: type[_MetricT],
    point: HashLifeProjectionMetrics,
    **metadata: object,
) -> _MetricT:
    """Forward all engine fields once, without positional placeholders/audits."""
    names = {field.name for field in fields(kind)}
    if not metadata.keys() <= names:
        raise ValueError("unknown powered metric metadata")
    observed = {field.name: getattr(point, field.name) for field in fields(point)}
    values = dict(metadata)
    for name in names - values.keys():
        source = _ALIASES.get(name, name)
        if source in observed:
            values[name] = observed[source]
        elif name in _RETIRED_COUNTERS:
            values[name] = point.resource_work_counters.get(name, 0)
        else:
            raise ValueError(f"powered metric has no observation: {name}")
    constructor = cast(Callable[..., _MetricT], kind)
    return constructor(**values)


__all__ = ["project_powered_metrics"]
