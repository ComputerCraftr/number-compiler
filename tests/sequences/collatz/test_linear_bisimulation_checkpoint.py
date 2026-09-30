from __future__ import annotations

import pytest

from number_compiler.api.number_api import NumberCompiler, PoweredCollatzTermPayload
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from tests.support.source_image_assertions import assert_physical_source_work

# This module executes the public families at release-scale temporal depths and
# audits their complete scheduler/accounting bridge. Keep it in the exhaustive
# validation suite rather than repeating those end-to-end runs in fast units.
pytestmark = pytest.mark.validation


def _reverse_value(steps: int) -> int:
    value = 196
    for _ in range(steps):
        value += int(str(value)[::-1])
    return value


def _assert_runtime_image_bridge(
    term: PoweredCollatzTerm | ReverseAddPoweredTerm,
    *,
    family: str,
) -> None:
    first = term.digit(0)
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
        counters = metrics.resource_work_counters
        assert counters.get("source_image_publications", 0) > 0
        assert counters.get("source_image_projection_publications", 0) > 0
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
        assert behavior.temporal_quotient_state_class_bound == 0
        assert behavior.temporal_quotient_action_class_bound == 0
        assert behavior.seed_application_temporal_action_nodes > 0
    counters = metrics.resource_work_counters
    publication_counter = "source_image_publications"
    projection_counter = "source_image_projection_publications"
    image_publications = counters.get(publication_counter, 0)
    image_projection_publications = counters.get(projection_counter, 0)
    assert image_publications > 0 and image_projection_publications > 0
    before = dict(term._ledger.counters)
    assert term.digit(0) == first
    after = term._ledger.counters
    assert after.get(publication_counter, 0) == before.get(publication_counter, 0)
    assert after.get(projection_counter, 0) == before.get(projection_counter, 0)
    assert metrics.resource_audit_complete == 1
    assert metrics.resource_accounting_mismatch == 0


@pytest.mark.parametrize("generation", (16, 32, 64, 128, 256))
def test_reverse_runtime_reports_exact_source_image_outputs_and_publications(
    generation: int,
) -> None:
    term = ReverseAddPoweredTerm(196, generation)
    assert term.materialize(max_bits=10_000) == _reverse_value(generation)
    assert 0 <= term.digit(0) <= 9
    _assert_runtime_image_bridge(term, family="reverse-add-source-cylinder")


@pytest.mark.parametrize("steps", (16, 32, 64, 128, 256))
def test_collatz_runtime_reports_actual_source_image_publications(steps: int) -> None:
    term = PoweredCollatzTerm(140137, steps)
    assert term.digit(0) in (0, 1)
    _assert_runtime_image_bridge(term, family="collatz-dyadic-source-image")


def test_public_family_and_radix_paths_report_no_sequential_backend_work() -> None:
    reverse = ReverseAddPoweredTerm(196, 64)
    assert reverse.materialize(max_bits=10_000) == _reverse_value(64)
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
    assert term.materialize(max_bits=10_000) == _reverse_value(128)
    first = term.digit(0)
    metrics = term.metrics()
    publications = metrics.resource_work_counters["source_image_publications"]
    projection_publications = metrics.resource_work_counters[
        "source_image_projection_publications"
    ]
    assert publications > 0 and projection_publications > 0
    assert term.digit(0) == first
    after = term.metrics()
    assert after.resource_work_counters["source_image_publications"] == publications
    assert (
        after.resource_work_counters["source_image_projection_publications"]
        == projection_publications
    )


def _checked_radix_projection() -> PoweredCollatzTerm:
    projected = NumberCompiler().project_nth("collatz", 11, seed=140137, radix=3)
    assert 0 <= projected.digit(3) < 3
    assert isinstance(projected.payload, PoweredCollatzTermPayload)
    return projected.payload.term
