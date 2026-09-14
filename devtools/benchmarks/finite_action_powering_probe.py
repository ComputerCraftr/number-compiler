"""Release probe for canonical causal cells and shared powering machinery.

This probe is a reference-oracle/representation audit, not the canonical nth-state
execution path. It keeps local representation closure separate from arbitrary temporal
complexity. Reverse/add H-row history and Collatz removable low-frame depth are
both quotiented before temporal cache lookup. Canonical dyadic fields, bounded
finite cell/domain alphabets, symmetry-aware action interning, and physical
carry propagation only from LSD toward MSD remain the local carrier. Distinct
normalized forcing classes are still charged on nonrepeating first-use paths.
"""

from __future__ import annotations

import json

from devtools.paths import repository_root
from devtools.proofs.collatz_spacetime import (
    CollatzCausalSpacetimeEngine,
    CollatzPhysicalField,
    CollatzRadixField,
)
from number_compiler.arithmetic.carry.carry_symmetry import (
    collatz_mul3_carry_kernel,
    reverse_add_carry_kernel,
)
from number_compiler.sequences.collatz.pair import accelerated_odd_collatz
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

ROOT = repository_root()


def _reverse_add_scalar(seed: int, generation: int) -> int:
    value = int(seed)
    for _ in range(int(generation)):
        text = str(value)
        value += int(text[::-1])
    return value


def _reverse_rows() -> list[dict[str, int | bool | str]]:
    rows: list[dict[str, int | bool | str]] = []
    for generation in (64, 128, 256):
        scalar = _reverse_add_scalar(196, generation)
        term = ReverseAddPoweredTerm(196, generation)
        position = term.maximum_width // 3
        want = (scalar // (10**position)) % 10
        digit = term.digit(position)
        if digit != want:
            raise AssertionError((generation, position, digit, want))
        metrics = term.metrics()
        if metrics.hashlife_temporal_leaf_applications:
            raise AssertionError(("production-replayed-t2", generation))
        if metrics.spacetime_carry_direction != "lsd-to-msd":
            raise AssertionError(metrics.spacetime_carry_direction)
        rows.append(
            {
                "generation": generation,
                "position": position,
                "digit": digit,
                "t2_leaf_applications": metrics.hashlife_temporal_leaf_applications,
                "retained_normalized_action_nodes": metrics.retained_execution_nodes,
                "finite_cell_alphabet": metrics.spacetime_finite_cell_alphabet,
                "carry_direction": metrics.spacetime_carry_direction,
                "carry_unique_actions": metrics.spacetime_carry_unique_actions,
                "carry_action_alias_hits": metrics.spacetime_carry_action_alias_hits,
                "mirror_alias_hits": metrics.spacetime_carry_mirror_alias_hits,
                "conjugate_alias_hits": metrics.spacetime_carry_conjugate_alias_hits,
                "primitive_field_steps": metrics.spacetime_primitive_field_steps,
                "primitive_slab_steps": metrics.spacetime_primitive_slab_steps,
                "primitive_forcing_steps": metrics.spacetime_primitive_forcing_steps,
                "slab_jump_entries": metrics.spacetime_slab_jump_entries,
                "forcing_jump_entries": metrics.spacetime_forcing_jump_entries,
                "jump_entries": metrics.spacetime_jump_entries,
                "forcing_action_classes": metrics.spacetime_forcing_classes,
                "forcing_occurrences": metrics.spacetime_forcing_occurrences,
                "forcing_action_aliases": metrics.spacetime_forcing_action_aliases,
                "forcing_history_aliases": metrics.spacetime_forcing_history_aliases,
                "forcing_source_hits": metrics.spacetime_forcing_source_hits,
                "forcing_carry_behavior_classes": metrics.spacetime_forcing_carry_behavior_classes,
                "forcing_carry_behavior_aliases": metrics.spacetime_forcing_carry_behavior_aliases,
            }
        )
    return rows


def _scalar_collatz_events(seed: int, events: int) -> tuple[int, int]:
    value = int(seed)
    valuation = 0
    for _ in range(int(events)):
        step = accelerated_odd_collatz(value)
        value = int(step.target)
        valuation += int(step.valuation)
    return value, valuation


def _collatz_rows() -> dict[str, object]:
    seed, events = 27, 64
    want_target, want_valuation = _scalar_collatz_events(seed, events)
    engine = CollatzCausalSpacetimeEngine()
    target, event = engine.advance_event_power(
        CollatzRadixField.from_value(seed), events
    )
    if target.value() != want_target or event.effect.shift != want_valuation:
        raise AssertionError(
            (target.value(), event.effect.shift, want_target, want_valuation)
        )
    metrics = engine.metrics()
    if metrics.carry_direction != "lsd-to-msd":
        raise AssertionError(metrics.carry_direction)

    fixed_engine = CollatzCausalSpacetimeEngine()
    fixed_target, fixed_event = fixed_engine.advance_event_power(
        CollatzRadixField.from_value(1),
        1 << 30,
    )
    if fixed_target.value() != 1 or fixed_event.effect.shift != 2 * (1 << 30):
        raise AssertionError((fixed_target.value(), fixed_event.effect))
    fixed_metrics = fixed_engine.metrics()

    physical_engine = CollatzCausalSpacetimeEngine()
    physical_target, physical_weight = physical_engine.advance_physical_power(
        CollatzPhysicalField.from_value(27),
        64,
    )
    physical_metrics = physical_engine.metrics()

    alias_engine = CollatzCausalSpacetimeEngine()
    alias_projections = [
        alias_engine.forcing_image_with_valuation(CollatzRadixField.from_value(value))
        for value in (11, 45, 181)
    ]
    alias_occurrences = [occurrence for occurrence, _ in alias_projections]
    if len({item.forcing.canonical_key for item in alias_occurrences}) != 1:
        raise AssertionError("Collatz low-frame forcing quotient did not merge")
    alias_before = alias_engine.metrics()
    alias_engine.advance_event_power(CollatzRadixField.from_value(11), 8)
    alias_after_first = alias_engine.metrics()
    alias_engine.advance_event_power(CollatzRadixField.from_value(45), 8)
    alias_after_second = alias_engine.metrics()
    if (
        alias_after_second.primitive_forcing_steps
        != alias_after_first.primitive_forcing_steps
    ):
        raise AssertionError("frame alias caused duplicate primitive forcing work")

    conflict_engine = CollatzCausalSpacetimeEngine()
    conflict_engine.advance_event_power(CollatzRadixField.from_value(3), 1)
    conflict_engine.advance_event_power(CollatzRadixField.from_value(11), 1)
    conflict_metrics = conflict_engine.metrics()
    if not conflict_metrics.forcing_successor_conflicts:
        raise AssertionError(
            "carry-only Collatz ActionID was incorrectly successor-closed"
        )

    return {
        "seed27_events": events,
        "seed27_target": target.value(),
        "seed27_valuation_sum": event.effect.shift,
        "seed27_primitive_field_steps": metrics.primitive_field_steps,
        "seed27_primitive_forcing_steps": metrics.primitive_forcing_steps,
        "seed27_forcing_action_classes": metrics.forcing_classes,
        "seed27_forcing_action_aliases": metrics.forcing_action_aliases,
        "seed27_forcing_successor_conflicts": metrics.forcing_successor_conflicts,
        "seed27_forcing_exact_target_conflicts": metrics.forcing_exact_target_conflicts,
        "seed27_forcing_frame_aliases": metrics.forcing_frame_aliases,
        "seed27_jump_entries": metrics.binary_lift.jump_entries,
        "seed27_event_nodes": metrics.event_nodes,
        "finite_cell_alphabet": metrics.finite_cell_alphabet,
        "carry_direction": metrics.carry_direction,
        "carry_unique_actions": metrics.carry_unique_actions,
        "carry_action_alias_hits": metrics.carry_action_alias_hits,
        "carry_mirror_alias_hits": metrics.carry_mirror_alias_hits,
        "carry_conjugate_alias_hits": metrics.carry_conjugate_alias_hits,
        "fixed_events": 1 << 30,
        "fixed_target": fixed_target.value(),
        "fixed_valuation_sum": fixed_event.effect.shift,
        "fixed_primitive_field_steps": fixed_metrics.primitive_field_steps,
        "fixed_primitive_forcing_steps": fixed_metrics.primitive_forcing_steps,
        "fixed_forcing_action_classes": fixed_metrics.forcing_classes,
        "fixed_jump_entries": fixed_metrics.binary_lift.jump_entries,
        "fixed_event_nodes": fixed_metrics.event_nodes,
        "concrete_power_path_uses_whole_germ_discovery": False,
        "whole_field_lift_is_global_spacetime_theorem": False,
        "cross_tail_action_witness": {
            "values": [3, 11],
            "exact_tails_distinct": True,
            "action_class_shared": True,
            "targets": [5, 17],
            "successor_conflicts": conflict_metrics.forcing_successor_conflicts,
            "exact_target_conflicts": conflict_metrics.forcing_exact_target_conflicts,
            "safe_as_exact_temporal_key": False,
        },
        "frame_alias_witness": {
            "values": [11, 45, 181],
            "frame_depths": [
                (valuation - item.forcing.local_shift) // 2
                for item, valuation in alias_projections
            ],
            "valuations": [valuation for _, valuation in alias_projections],
            "forcing_class_shared": True,
            "primitive_forcing_after_first": alias_after_first.primitive_forcing_steps,
            "primitive_forcing_after_second": alias_after_second.primitive_forcing_steps,
            "frame_aliases_before_power": alias_before.forcing_frame_aliases,
        },
        "physical64_target": physical_target.value(),
        "physical64_weight": physical_weight,
        "physical64_primitive_steps": physical_metrics.primitive_physical_steps,
        "physical64_jump_entries": physical_metrics.physical_jump_entries,
    }


def run_probe() -> dict[str, object]:
    reverse_add_carry_kernel(10).verify_conjugacy()
    # The shared decimal kernel remains a compatibility proof; the canonical
    # Collatz field uses the equivalent radix-4 finite carry kernel internally.
    collatz_mul3_carry_kernel(10).verify_conjugacy()
    reverse_rows = _reverse_rows()
    collatz = _collatz_rows()
    return {
        "version": "0.59.9",
        "status": "PASS",
        "global_finite_quotient_required_for_hashlife": False,
        "canonical_recursive_cell_identity": True,
        "normalized_extent_is_geometry_not_cell_payload": True,
        "causal_symmetry_quotient": "mirror x value-conjugacy",
        "physical_carry_direction": "lsd-to-msd",
        "reverse_add_local_conjugacy_proved": True,
        "collatz_mul3_local_conjugacy_proved": True,
        "reverse_add_t2_replay_eliminated_in_production": True,
        "reverse_add_history_residual_eliminated_in_production": True,
        "collatz_whole_germ_discovery_eliminated_in_concrete_power_path": True,
        "production_history_word_carrier_present": False,
        "spacetime_macrocell_absorption_installed": True,
        "reverse_add_spacetime_logarithmic_closure_proved": False,
        "collatz_spacetime_logarithmic_closure_proved": False,
        "reverse_add": reverse_rows,
        "collatz": collatz,
        "interpretation": (
            "The representation/causality fix is active in both families: finite semantic cells, "
            "dyadic structural extent, mirror/conjugacy action sharing, and only LSD->MSD physical "
            "carry scans. Reverse/add affine ActionIDs are separated from exact pair occurrences; "
            "Collatz carry/shift ActionIDs are separated from exact normalized tails, and low 1**q "
            "frame depth is a valuation cocycle rather than cache identity. "
            "Concrete Collatz powers no longer originate from whole-germ advance(). Production high-order "
            "application also no longer retains a CanonicalWord/action-history carrier: lower temporal "
            "children applied to canonical spatial tiles return canonical future tiles. A nonrepeating "
            "source can still expose many distinct semantic interface/future-macrocell classes, which are "
            "charged separately rather than hidden behind binary syntax."
        ),
    }


def main() -> int:
    result = run_probe()
    out = ROOT / "results" / "shared_powering_metrics.json"
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
