from __future__ import annotations

import pytest

from tests.support.source_image_assertions import assert_physical_source_work

from number_compiler.api.number_api import NumberCompiler, PoweredCollatzTermPayload
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

# This module executes the public families at release-scale temporal depths and
# audits their complete scheduler/accounting bridge. Keep it in the exhaustive
# validation suite rather than repeating those end-to-end runs in fast units.
pytestmark = pytest.mark.validation


def _assert_diamond_bridge(
    term: PoweredCollatzTerm | ReverseAddPoweredTerm,
    *,
    family: str,
    retained_proof: tuple[int, int] | None = None,
) -> None:
    metrics = term.metrics()
    behavior = term.behavior_metrics()
    assert metrics.metrics_schema_version == 8
    collatz = isinstance(term, PoweredCollatzTerm)
    if collatz:
        assert isinstance(term, PoweredCollatzTerm)
        counters = metrics.resource_work_counters
        assert metrics.temporal_parent_requests == 0
        assert metrics.temporal_parent_compositions == 0
        assert metrics.tile_temporal_action_publications == 0
        assert metrics.field_action_nodes == 0
        assert_physical_source_work(counters)
        assert term._power is None
    else:
        assert metrics.temporal_parent_requests == (
            metrics.temporal_parent_early_hits + metrics.temporal_parent_compositions
        )
        assert metrics.temporal_parent_compositions > 0
        assert metrics.tile_temporal_action_publications > 0
        assert (
            metrics.bounded_application_temporal_state_classes
            == metrics.local_interface_nodes
            > 0
        )
        assert (
            metrics.bounded_application_temporal_action_classes
            == metrics.field_action_nodes
        )
    assert metrics.whole_word_sweeps == metrics.whole_word_symbol_visits == 0
    assert metrics.proof_machine_applications == 0
    assert metrics.sequential_generation_advances == 0
    assert metrics.exact_endpoint_nodes == 0
    assert metrics.forbidden_future_payloads == 0
    assert metrics.representation_boundary_complete == 1
    assert behavior.temporal_quotient_family == family
    if collatz:
        assert behavior.temporal_quotient_state_class_bound == 0
        assert behavior.temporal_quotient_action_class_bound == 0
        assert behavior.seed_application_temporal_action_nodes > 0
    else:
        assert (
            behavior.temporal_quotient_state_class_bound
            == metrics.local_interface_nodes
            > 0
        )
        assert (
            behavior.temporal_quotient_action_class_bound == metrics.field_action_nodes
        )
    assert behavior.bounded_temporal_runtime_cutover_complete == 1
    assert behavior.bounded_temporal_runtime_cutover_blocker == ""
    if retained_proof is not None:
        assert (
            metrics.collatz_c4_proof_left_state_classes,
            metrics.collatz_c4_proof_right_state_classes,
        ) == retained_proof


@pytest.mark.parametrize("generation", (16, 32, 64, 128, 256))
def test_reverse_diamond_reports_proof_populations_only_as_metadata(
    generation: int,
) -> None:
    term = ReverseAddPoweredTerm(196, generation)
    assert 0 <= term.digit(0) <= 9
    _assert_diamond_bridge(term, family="reverse-add-tile-hashlife")


@pytest.mark.parametrize("steps", (16, 32, 64, 128, 256))
def test_collatz_diamond_reports_proof_populations_only_as_metadata(steps: int) -> None:
    term = PoweredCollatzTerm(140137, steps)
    assert term.digit(0) in (0, 1)
    _assert_diamond_bridge(
        term,
        family="collatz-dyadic-source-image",
        retained_proof=(50, 90),
    )


def test_public_family_and_radix_paths_report_no_sequential_backend_work() -> None:
    reverse = ReverseAddPoweredTerm(196, 64)
    assert reverse.width() > 0
    assert 0 <= reverse.digit(0) <= 9
    collatz = PoweredCollatzTerm(140137, 11)
    assert collatz.width() > 0
    assert collatz.digit(0) in (0, 1)
    projected_term = _checked_radix_projection()
    for term in (reverse, collatz, projected_term):
        metrics = term.metrics()
        assert metrics.sequential_generation_advances == 0
        assert metrics.higher_concrete_operation_evaluations == 0


def test_former_collatz_radix_timeout_reports_actual_diamond_work() -> None:
    projected_term = _checked_radix_projection()
    metrics = projected_term.metrics()
    assert metrics.temporal_parent_requests == 0
    assert metrics.temporal_parent_compositions == 0
    counters = metrics.resource_work_counters
    assert counters.get("source_image_publications", 0) > 0
    assert counters.get("collatz_image_radix_demands", 0) > 0
    assert projected_term._power is None
    assert metrics.whole_word_sweeps == metrics.proof_machine_applications == 0
    assert metrics.sequential_generation_advances == 0
    assert metrics.forbidden_future_payloads == 0


def test_identical_warm_point_does_not_rebuild_temporal_parents() -> None:
    term = ReverseAddPoweredTerm(196, 128)
    first = term.digit(0)
    compositions = term.metrics().temporal_parent_compositions
    assert compositions > 0
    assert term.digit(0) == first
    after = term.metrics()
    assert after.temporal_parent_compositions == compositions
    assert after.resource_work_counters.get("point_response_cache_hits", 0) >= 1


def _checked_radix_projection() -> PoweredCollatzTerm:
    projected = NumberCompiler().project_nth("collatz", 11, seed=140137, radix=3)
    assert 0 <= projected.digit(3) < 3
    assert isinstance(projected.payload, PoweredCollatzTermPayload)
    return projected.payload.term
