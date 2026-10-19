"""Schema-seven separates runtime field actions from retained proof oracles."""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.metric_registry import ALGEBRAIC_FIELD_WORK_COUNTERS
from number_compiler.resources.stores import LedgerDict, LedgerList
from tests.support.assertions import collect_counter_quantities

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
    from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
    from number_compiler.resources.ledger import LedgerSnapshot


def test_schema_eight_does_not_report_historical_proof_sizes_as_runtime_metrics() -> (
    None
):
    report = collect_ledger_metrics(ResourceLedger())
    assert report.metrics_schema_version == 8
    assert not hasattr(report, "collatz_c4_proof_left_state_classes")
    assert not hasattr(report, "collatz_c4_proof_right_state_classes")
    assert report.production_residual_state_classes == 0
    assert report.algebraic_instrumentation_complete == 0


def test_public_collatz_accounts_for_shared_images_without_retired_tiles() -> None:
    from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm

    term = PoweredCollatzTerm(27, 16)
    assert term.digit(0) == 1
    snapshot = term.resource_ledger.snapshot()
    report = term.metrics()
    expected = {
        "runtime_query_state_nodes": ("runtime_query_state_memo", "observed_nodes"),
        "runtime_query_environment_nodes": (
            "runtime_query_environment_memo",
            "observed_nodes",
        ),
        "runtime_operation_memo_entries": (
            "runtime_operation_memo",
            "observed_entries",
        ),
    }
    for field, (role, quantity) in expected.items():
        assert getattr(report, field) == sum(
            getattr(row, quantity) or 0
            for row in snapshot.inventory
            if row.role == role
        )
    assert report.runtime_query_state_nodes == 0
    assert report.runtime_query_environment_nodes == 0
    assert report.runtime_operation_memo_entries == 0
    assert report.recursive_field_image_nodes == 0
    assert report.canonical_tile_nodes == 0
    assert report.local_interface_nodes == 0
    assert report.tile_scheduler_demand_descents == 0
    assert report.powered_absorption_requests == 0
    # The migrated owner retains source-bound actions, support and images.
    # Requiring legacy spatial tiles here would require restoring the retired
    # executor. Inspect real reservations rather than treating absent work as 0.
    retained_roles = (
        "dyadic_return_action",
        "dyadic_return_source",
        "dyadic_return_support",
        "dyadic_return_image",
        "source_image",
    )
    retained = {
        role: sum(
            row.observed_nodes or 0 for row in snapshot.inventory if row.role == role
        )
        for role in retained_roles
    }
    assert all(count > 0 for count in retained.values())
    assert snapshot.counters["source_image_publications"] > 0
    assert snapshot.counters["source_image_primitive_applications"] > 0
    source_work = snapshot.counters["collatz_physical_temporal_run_actions"]
    publications = snapshot.counters["source_image_publications"]
    assert source_work > 0
    term.resource_ledger.evict_query_memos()
    after = term.metrics()
    assert after.runtime_query_state_nodes == 0
    assert after.runtime_query_environment_nodes == 0
    assert after.runtime_operation_memo_entries == 0
    assert after.recursive_field_image_nodes == 0
    assert after.canonical_tile_nodes == 0
    refreshed = term.resource_ledger.snapshot()
    assert {
        role: sum(
            row.observed_nodes or 0 for row in refreshed.inventory if row.role == role
        )
        for role in retained_roles
    } == retained
    assert term.digit(0) == 1
    assert term.resource_ledger.counters["source_image_publications"] == publications
    assert (
        term.resource_ledger.counters["collatz_physical_temporal_run_actions"]
        == source_work
    )


def test_field_action_work_is_forwarded_from_one_ledger_snapshot() -> None:
    ledger = ResourceLedger()
    for name in ALGEBRAIC_FIELD_WORK_COUNTERS:
        ledger.bump(name, 0)
    ledger.bump("temporal_parent_requests", 7)
    ledger.bump("temporal_parent_early_hits", 4)
    ledger.bump("temporal_parent_compositions", 2)
    ledger.bump("temporal_parent_late_duplicate_reductions", 1)
    ledger.bump("radial_action_operations", 11)
    ledger.bump("carry_action_operations", 13)
    ledger.bump("production_residual_state_classes", 5)
    ledger.bump("concrete_port_task_evaluations", 17)
    ledger.bump("concrete_port_task_frames", 101)
    ledger.bump("concrete_provider_layer_publications", 7)
    ledger.bump("concrete_provider_layer_alias_hits", 19)
    ledger.bump("concrete_virtual_interface_evaluations", 3)
    ledger.bump("concrete_port_task_requests", 7)
    ledger.bump("concrete_port_task_early_hits", 5)
    ledger.bump("concrete_virtual_interface_requests", 2)
    ledger.bump("concrete_virtual_interface_early_hits", 3)

    report = collect_ledger_metrics(ledger)
    assert report.algebraic_instrumentation_complete == 1
    assert report.temporal_parent_requests == 7
    assert report.temporal_parent_early_hits == 4
    assert report.temporal_parent_compositions == 2
    assert report.temporal_parent_late_duplicate_reductions == 1
    assert report.radial_action_operations == 11
    assert report.carry_action_operations == 13
    assert report.production_residual_state_classes == 5
    assert report.concrete_port_task_evaluations == 17
    assert report.concrete_port_task_frames == 101
    assert report.concrete_provider_layer_publications == 7
    assert report.concrete_provider_layer_alias_hits == 19
    assert report.concrete_virtual_interface_evaluations == 3
    assert report.concrete_port_task_requests == 12
    assert report.concrete_port_task_early_hits == 5
    assert report.concrete_virtual_interface_requests == 5
    assert report.concrete_virtual_interface_early_hits == 3
    assert report.total_internal_action_work == 147
    assert report.whole_word_sweeps == 0
    assert report.whole_word_symbol_visits == 0
    assert report.proof_machine_applications == 0
    assert report.resource_work_counters["production_residual_state_classes"] == 5


def test_reverse_frobenius_plan_metric_is_compilation_work_only() -> None:
    ledger = ResourceLedger()
    ledger.bump("reverse_frobenius_plan_compositions", 3)
    ledger.bump("reverse_field_action_source_annihilation_derivations", 2)
    ledger.bump("collatz_field_action_source_annihilation_derivations", 1)
    report = collect_ledger_metrics(ledger)
    assert report.reverse_frobenius_plan_compositions == 3
    assert report.reverse_field_action_source_annihilation_derivations == 2
    assert report.collatz_field_action_source_annihilation_derivations == 1
    assert report.radial_action_operations == 0
    assert report.innovation_action_operations == 0
    assert report.source_annihilations == 0


def test_reporting_captures_the_ledger_snapshot_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    calls = 0
    original = ResourceLedger.snapshot

    def counted_snapshot(self: ResourceLedger) -> LedgerSnapshot:
        nonlocal calls
        calls += 1
        return original(self)

    monkeypatch.setattr(ResourceLedger, "snapshot", counted_snapshot)
    report = collect_ledger_metrics(ledger)
    assert report.resource_ledger_entries == 0
    assert calls == 1


def test_missing_one_field_action_counter_does_not_claim_complete_instrumentation() -> (
    None
):
    ledger = ResourceLedger()
    for name in ALGEBRAIC_FIELD_WORK_COUNTERS[:-1]:
        ledger.bump(name, 0)
    report = collect_ledger_metrics(ledger)
    assert report.algebraic_instrumentation_complete == 0


def test_retired_checkpoint_counters_do_not_masquerade_as_runtime_work() -> None:
    ledger = ResourceLedger()
    ledger.bump("family_bisimulation_machine_applications", 17)
    ledger.bump("family_bisimulation_symbol_visits", 100_000)
    report = collect_ledger_metrics(ledger)
    assert report.algebraic_instrumentation_complete == 0
    assert report.whole_word_sweeps == report.proof_machine_applications == 0
    assert report.whole_word_symbol_visits == 0
    assert report.proof_machine_artifacts_loaded_by_runtime == 0
    assert (
        report.resource_work_counters["family_bisimulation_machine_applications"] == 17
    )
    assert report.resource_work_counters["family_bisimulation_symbol_visits"] == 100_000


def test_diamond_work_maps_to_schema_without_claiming_complete_field_instrumentation() -> (
    None
):
    ledger = ResourceLedger()
    ledger.bump("diamond_temporal_composition_requests", 9)
    ledger.bump("diamond_temporal_composition_hits", 6)
    ledger.bump("diamond_temporal_composition_evaluations", 3)
    ledger.bump("quotient_semantic_interner_hits", 2)
    ledger.bump("spatial_parent_cache_hits", 4)
    ledger.bump("spatial_parent_early_hits", 5)
    ledger.bump("width_descent_steps", 7)
    ledger.bump("finite_expression_component_checks", 11)
    ledger.bump("new_field_image_nodes", 3)
    ledger.bump("field_image_binding_requests", 8)
    ledger.bump("field_image_binding_early_hits", 5)
    ledger.bump("quotient_semantic_interner_evaluations", 2)
    ledger.bump("quotient_normal_form_early_hits", 4)
    ledger.bump("spatial_parent_evaluations", 7)
    ledger.bump("boundary_substitution_evaluations", 13)
    report = collect_ledger_metrics(ledger)
    assert report.algebraic_instrumentation_complete == 0
    assert report.temporal_parent_requests == 9
    assert report.temporal_parent_early_hits == 6
    assert report.temporal_parent_compositions == 3
    # A quotient interner alias is not a temporal-parent late reduction.
    assert report.temporal_parent_late_duplicate_reductions == 0
    assert report.spatial_parent_cache_hits == 9
    assert report.spatial_descents == 7
    assert report.canonical_expression_node_visits == 11
    assert report.new_canonical_field_images_published == 3
    assert report.new_field_image_nodes == 3
    assert report.field_image_binding_requests == 8
    assert report.field_image_binding_early_hits == 5
    assert report.field_image_publication_requests == 8
    assert report.field_image_early_hits == 5
    assert report.field_interface_publications == 2
    assert report.field_interface_early_hits == 4
    assert report.total_internal_action_work == 3 + 11 + 7 + 13


def test_microblock_payload_metrics_forward_current_and_peak_bytes() -> None:
    ledger = ResourceLedger()
    ledger.bump("microblock_payload_bytes", 8)
    ledger.bump("microblock_payload_high_water_bytes", 24)
    ledger.bump("microblock_entry_high_water", 3)
    report = collect_ledger_metrics(ledger)
    assert report.microblock_payload_bytes == 8
    assert report.microblock_payload_high_water_bytes == 24
    assert report.microblock_entry_high_water == 3


def test_radix_recursive_work_is_public_and_part_of_internal_work() -> None:
    ledger = ResourceLedger()
    counters = {
        "radix_provider_digit_requests": 17,
        "radix_provider_digit_early_hits": 3,
        "radix_provider_digit_evaluations": 14,
        "radix_temporal_action_requests": 19,
        "radix_temporal_action_early_hits": 7,
        "radix_temporal_action_evaluations": 12,
        "radix_recursive_transfer_requests": 29,
        "radix_recursive_transfer_early_hits": 11,
        "radix_recursive_transfer_evaluations": 18,
        "radix_recursive_descents": 23,
        "radix_source_bit_visits": 31,
        "radix_limb_operations": 37,
    }
    report = collect_counter_quantities(ledger, counters)
    assert report.total_internal_action_work == 12 + 18 + 23 + 31 + 37


def test_family_publication_and_higher_work_are_forwarded_without_zero_stubs() -> None:
    ledger = ResourceLedger()
    ledger.bump("reverse_field_action_publications", 3)
    ledger.bump("collatz_field_action_publications", 5)
    ledger.bump("higher_interface_publications", 7)
    ledger.bump("higher_interface_normal_form_hits", 11)
    ledger.bump("higher_semantic_evaluations", 13)
    ledger.bump("higher_spatial_transfer_publications", 17)
    ledger.bump("higher_range_dyadic_cells", 19)
    ledger.bump("higher_concrete_operation_evaluations", 41)
    ledger.bump("higher_concrete_operation_hits", 43)
    ledger.bump("opaque_higher_operation_publications", 47)
    ledger.bump("higher_operation_early_hits", 53)
    ledger.bump("higher_point_observations", 29)
    ledger.bump("higher_width_observations", 31)
    ledger.bump("higher_observation_fallback", 37)
    ledger.bump("spatial_observation_descents", 23)
    ledger.bump("higher_concrete_force_evaluations", 59)
    ledger.bump("higher_primitive_step_hits", 61)
    ledger.bump("higher_primitive_step_publications", 67)
    ledger.bump("higher_primitive_output_hits", 71)
    ledger.bump("higher_primitive_output_publications", 73)
    ledger.bump("higher_summary_temporal_compositions", 79)
    ledger.bump("higher_summary_spatial_compositions", 83)
    ledger.bump("higher_context_spatial_compositions", 89)
    ledger.bump("reverse_temporal_leaf_substitutions", 97)
    ledger.bump("reverse_temporal_parent_substitutions", 101)
    ledger.bump("reverse_temporal_prefix_image_observations", 103)
    ledger.bump("collatz_temporal_leaf_substitutions", 107)
    ledger.bump("collatz_temporal_parent_substitutions", 109)
    ledger.bump("collatz_temporal_prefix_image_observations", 113)
    ledger.bump("collatz_complete_leaf_interface_observations", 127)
    report = collect_ledger_metrics(ledger)
    assert report.field_action_publications == 8
    assert report.field_interface_publications == 7
    assert report.field_interface_early_hits == 11
    assert report.higher_point_observations == 29
    assert report.higher_width_observations == 31
    assert report.higher_observation_fallback == 37
    assert report.higher_range_dyadic_cells == 19
    assert report.higher_concrete_operation_evaluations == 41
    assert report.higher_concrete_operation_hits == 43
    assert report.opaque_higher_operation_publications == 47
    assert report.higher_operation_early_hits == 53
    assert report.higher_concrete_force_evaluations == 59
    assert report.higher_primitive_step_hits == 61
    assert report.higher_primitive_step_publications == 67
    assert report.higher_primitive_output_hits == 71
    assert report.higher_primitive_output_publications == 73
    assert report.higher_summary_temporal_compositions == 79
    assert report.higher_summary_spatial_compositions == 83
    assert report.higher_context_spatial_compositions == 89
    assert report.reverse_temporal_leaf_substitutions == 97
    assert report.reverse_temporal_parent_substitutions == 101
    assert report.reverse_temporal_prefix_image_observations == 103
    assert report.collatz_temporal_leaf_substitutions == 107
    assert report.collatz_temporal_parent_substitutions == 109
    assert report.collatz_temporal_prefix_image_observations == 113
    assert report.collatz_complete_leaf_interface_observations == 127
    assert report.total_internal_action_work == (
        13 + 17 + 19 + 23 + 41 + 43 + 47 + 53 + 103 + 113 + 61 + 67 + 71 + 73
    )


def test_field_image_and_interface_populations_come_from_registered_records() -> None:
    from number_compiler.arithmetic.functions.semantic_functions import (
        SemanticFunctionArena,
    )
    from number_compiler.hashlife.interfaces.diamond_quotient import (
        DiamondQuotientArena,
    )

    ledger = ResourceLedger()
    arena = DiamondQuotientArena(SemanticFunctionArena(ledger))
    assert arena is not None
    report = collect_ledger_metrics(ledger)
    assert report.field_image_nodes == report.image_action_nodes == 0
    assert report.field_interface_nodes == report.semantic_signature_nodes == 0
    assert report.new_canonical_field_images_published == 0


def test_field_runtime_populations_share_the_ledger_snapshot_inventory() -> None:
    ledger = ResourceLedger()
    expected = {
        "source_cell": 2,
        "field_transfer": 3,
        "field_image": 4,
        "diamond_quotient": 5,
        "output_morphism": 6,
    }
    for serial, (role, count) in enumerate(expected.items()):
        owner = ledger.register(f"schema-seven-{serial}", role)
        records: LedgerList[object]
        records = ledger.make_list(owner)
        ledger.reserve(owner, entries=count, nodes=count)
        records.extend(f"{role}-{index}" for index in range(count))
    binding_owner = ledger.register(
        "schema-seven-transfer-bindings", "field_transfer_binding"
    )
    bindings: LedgerDict[object, object]
    bindings = ledger.make_dict(binding_owner)
    ledger.reserve(binding_owner, entries=7)
    bindings.update((index, index) for index in range(7))
    report = collect_ledger_metrics(ledger)
    assert (
        report.source_cell_nodes,
        report.field_transfer_nodes,
        report.recursive_field_image_nodes,
        report.local_interface_nodes,
        report.output_morphism_nodes,
        report.field_transfer_binding_entries,
    ) == (2, 3, 4, 5, 6, 7)


def test_schema_six_counts_current_higher_and_source_forest_roles() -> None:
    ledger = ResourceLedger()
    populations = {
        "source_forest": 2,
        "higher_local_interface": 3,
        "coordinate_output_morphism": 4,
        "higher_semantic_expression": 5,
        "higher_semantic_function": 6,
        "higher_port_signature": 7,
        "reverse_local_action": 8,
        "reverse_port_state": 9,
    }
    for serial, (role, count) in enumerate(populations.items()):
        owner = ledger.register(f"current-runtime-{serial}", role)
        records: LedgerList[object]
        records = ledger.make_list(owner)
        ledger.reserve(owner, entries=count, nodes=count)
        records.extend((role, index) for index in range(count))
    report = collect_ledger_metrics(ledger)
    assert report.source_cell_nodes == 2
    assert report.local_interface_nodes == 3
    assert report.output_morphism_nodes == 4
    assert report.semantic_function_nodes == 11
    assert report.semantic_signature_nodes == 7
    assert report.algebraic_component_nodes == 8
    assert report.finite_port_state_nodes == 9


def test_live_quotient_records_and_independent_higher_interfaces_are_distinct() -> None:
    from number_compiler.arithmetic.functions.semantic_functions import (
        SemanticFunctionArena,
    )
    from number_compiler.hashlife.interfaces.diamond_quotient import (
        DiamondQuotientArena,
    )

    ledger = ResourceLedger()
    arena = DiamondQuotientArena(SemanticFunctionArena(ledger))
    synthetic_quotient_owner = ledger.register(
        "synthetic-quotient-slots", "diamond_quotient"
    )
    synthetic_quotient: LedgerList[object] = ledger.make_list(synthetic_quotient_owner)
    ledger.reserve(synthetic_quotient_owner, entries=5, nodes=5)
    synthetic_quotient.extend(range(5))
    higher_owner = ledger.register(
        "independent-higher-interfaces", "higher_local_interface"
    )
    higher: LedgerList[object] = ledger.make_list(higher_owner)
    ledger.reserve(higher_owner, entries=3, nodes=3)
    higher.extend(range(3))

    report = collect_ledger_metrics(ledger)
    assert len(arena._nodes) == 0
    # Retained node charge includes the synthetic quotient slots as well as
    # the independent higher interfaces.  Semantic interface population is a
    # separate record-count unit and excludes the synthetic charged slots
    # while a live quotient arena supplies its authoritative record count.
    assert report.diamond_quotient_nodes == 8
    assert report.field_interface_nodes == 3
    assert report.local_interface_nodes == 3


def test_post_publish_merge_gate_is_an_independent_measured_counter() -> None:
    ledger = ResourceLedger()
    ledger.bump("post_publish_equivalence_merges", 2)
    report = collect_ledger_metrics(ledger)
    assert report.post_publish_equivalence_merges == 2
    assert report.temporal_parent_late_duplicate_reductions == 0


def test_reverse_field_actions_are_owner_validated_semantic_nodes() -> None:
    from number_compiler.resources.field_action_payload_audit import (
        audit_field_action_payloads,
    )
    from number_compiler.sequences.reverse_add.field_action import (
        ReverseActionAutomorphisms,
        ReverseFieldActionArena,
    )

    arena = ReverseFieldActionArena(
        base=10,
        order=16,
        residual_identity=("residual",),
        output_identity=("output",),
        residual_compose=lambda before, after: before,
        output_compose=lambda before, after: before,
        automorphisms=ReverseActionAutomorphisms.trivial(),
    )
    report = collect_ledger_metrics(arena.ledger)
    assert report.field_action_nodes == 1
    assert report.production_residual_state_nodes == 1
    assert report.algebraic_component_nodes == 1
    # The migrated action arena is validated by its canonical production owner.
    assert report.resource_audit_unknown_payloads == 0
    assert not audit_field_action_payloads(arena.ledger).invalid


def test_unbounded_reverse_semantic_key_rejects_before_publication() -> None:
    from number_compiler.sequences.reverse_add.field_action import (
        ReverseActionAutomorphisms,
        ReverseFieldActionArena,
    )

    with pytest.raises(TypeError, match="scalar ID aliases"):
        ReverseFieldActionArena(
            base=10,
            order=16,
            residual_identity=("residual",),
            output_identity=("unbounded", 1 << 100),
            residual_compose=lambda before, after: before,
            output_compose=lambda before, after: before,
            automorphisms=ReverseActionAutomorphisms.trivial(),
        )


def test_collatz_field_actions_are_owner_validated_semantic_nodes() -> None:
    from number_compiler.arithmetic.contracts.scoped_handles import (
        ActionProgramID,
        ArenaToken,
    )
    from number_compiler.sequences.collatz.defect_arena import CollatzDefectArena
    from number_compiler.sequences.collatz.field_action import CollatzFieldActionArena

    class Programs:
        def __init__(self) -> None:
            self.owner = ArenaToken("schema-seven-programs")
            self.ids = {
                role: ActionProgramID(self.owner, role, 0)
                for role in (
                    "root",
                    "affine",
                    "output",
                    "physical-tick",
                    "valuation",
                    "frame",
                )
            }

        def identity(self, role: str) -> ActionProgramID:
            return self.ids[role]

        def validate(self, role: str, reference: ActionProgramID) -> int:
            if reference != self.ids[role]:
                raise ValueError("foreign symbolic program")
            return reference.local_id

        def semantic_identity(
            self, role: str, reference: ActionProgramID
        ) -> SemanticIdentity:
            from number_compiler.arithmetic.contracts.semantic_identity import (
                SemanticIdentity,
            )

            self.validate(role, reference)
            return SemanticIdentity("", ("schema-seven-program-v1", role))

        def audit_semantic_identity(
            self, role: str, reference: ActionProgramID
        ) -> SemanticIdentity:
            from number_compiler.arithmetic.contracts.semantic_identity import (
                SemanticIdentity,
            )

            self.validate(role, reference)
            return SemanticIdentity("", ("schema-seven-program-v1", role))

        def composed_semantic_identity(
            self, role: str, before: ActionProgramID, after: ActionProgramID
        ) -> SemanticIdentity:
            self.validate(role, before)
            self.validate(role, after)
            return self.semantic_identity(role, before)

        def compose(
            self, role: str, before: ActionProgramID, after: ActionProgramID
        ) -> ActionProgramID:
            self.validate(role, before)
            self.validate(role, after)
            return before

    ledger = ResourceLedger()
    defects = CollatzDefectArena(((0,),), identity=0, ledger=ledger)
    arena = CollatzFieldActionArena(Programs(), defects, ledger=ledger)
    _ = arena.identity
    report = collect_ledger_metrics(ledger)
    assert report.field_action_nodes == 1
    assert report.resource_audit_unknown_payloads == 0
    assert report.forbidden_future_payloads == 0


def test_bounded_port_work_includes_primitive_lookups_and_state_visits() -> None:
    from number_compiler.resources.metric_registry import schema7_work_values

    counters = {
        "higher_runtime_composition_requests": 7,
        "higher_finite_transfer_state_visits": 31,
        "higher_primitive_step_hits": 43,
        "higher_primitive_step_publications": 11,
        "higher_primitive_output_hits": 17,
        "higher_primitive_output_publications": 5,
    }
    report = schema7_work_values(counters)
    assert report["total_internal_action_work"] == sum(counters.values())
    for name, value in counters.items():
        assert report[name] == value
