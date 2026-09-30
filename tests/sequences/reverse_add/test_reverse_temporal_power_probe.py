from pathlib import Path

import pytest

from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from tests.support.report_values import object_record, text_values
from tests.support.source_policy import module_sources


def test_reverse_temporal_binary_operator_construction_is_logarithmic_and_lazy() -> (
    None
):
    for generation in (16, 256, 1_000_000, 10**18):
        term = ReverseAddPoweredTerm(196, generation)
        metrics = term.metrics()
        bits = max(1, generation.bit_length())
        assert metrics.operator_nodes <= 4 * bits
        assert metrics.compose_operations <= 4 * bits
        assert metrics.point_queries == 0
        assert metrics.run_action_cache_entries == 0


@pytest.mark.validation
def test_reverse_production_requires_exact_output_and_source_image_evidence() -> None:
    """Exercise exact N=256 output and source-image publication accounting."""
    term = ReverseAddPoweredTerm(196, 256)
    value = 196
    for _ in range(256):
        text = str(value)
        value += int(text[::-1])
    position = term.maximum_width // 3
    expected_digits = str(value)[::-1]
    assert term.digit(position) == int(expected_digits[position])
    assert term.digits() == tuple(map(int, expected_digits))
    assert collect_ledger_metrics(term._ledger).resource_audit_complete == 1
    metrics = term.metrics()
    counters = metrics.resource_work_counters
    assert counters.get("source_image_publications", 0) > 0
    assert counters.get("source_image_projection_publications", 0) > 0
    assert metrics.resource_audit_complete == 1
    assert metrics.resource_accounting_mismatch == 0
    assert metrics.sequential_generation_advances == 0
    assert metrics.higher_action_continuation_requests == 0
    assert metrics.higher_concrete_operation_evaluations == 0
    before_replay = dict(term._ledger.counters)
    assert term.digits() == tuple(map(int, expected_digits))
    assert (
        term._ledger.counters["source_image_publications"]
        == before_replay["source_image_publications"]
    )
    assert (
        term._ledger.counters["source_image_projection_publications"]
        == before_replay["source_image_projection_publications"]
    )


def test_reverse_power_source_has_no_slow_temporal_backend() -> None:
    import devtools.verification.block_runtime as runtime
    import number_compiler.hashlife.observation.hashlife_projection as hashlife
    import number_compiler.sequences.reverse_add.power as reverse_power

    power_text, hash_text, runtime_text = module_sources(
        reverse_power, hashlife, runtime
    )
    assert "ReverseAddCausalSpacetimeEngine" not in power_text
    assert "BlockPointIndex" not in power_text
    assert "def _partition3" not in hash_text
    assert "def _leaf_partition3" not in hash_text
    assert "def output_word" not in hash_text
    assert "def point(" not in hash_text
    assert "program_pop_last" not in runtime_text


@pytest.mark.validation
def test_hashlife_projection_respects_explicit_context_budget() -> None:
    """Run the N=128 exhausted-budget and successful production applications."""
    import pytest

    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )

    with pytest.raises(BlockContextBudgetExceeded):
        ReverseAddPoweredTerm(196, 128, max_context_nodes=0, max_cache_entries=0)
    # Every retained action, source and publication is charged. The bounded
    # application must refuse atomically; an unbounded application still has
    # to construct and return the exact powered output.
    constrained = ReverseAddPoweredTerm(
        196, 128, max_context_nodes=100, max_cache_entries=100
    )
    with pytest.raises(BlockContextBudgetExceeded):
        constrained.digit(constrained.maximum_width // 3)
    term = ReverseAddPoweredTerm(196, 128)
    value = 196
    for _ in range(128):
        value += int(str(value)[::-1])
    assert term.materialize(max_bits=10_000) == value
    assert collect_ledger_metrics(term._ledger).resource_audit_complete == 1
    metrics = term.metrics()
    assert metrics.resource_work_counters.get("source_image_publications", 0) > 0
    assert (
        metrics.resource_work_counters.get("source_image_projection_publications", 0)
        > 0
    )
    assert metrics.resource_audit_complete == 1
    assert metrics.resource_accounting_mismatch == 0
    assert metrics.proof_machine_applications == metrics.whole_word_sweeps == 0


def test_hashlife_contract_does_not_require_a_global_finite_quotient_module() -> None:
    import number_compiler

    package = Path(number_compiler.__file__).resolve().parent
    assert not (package / "powering_closure.py").exists()


@pytest.mark.validation
def test_reverse_release_probe_requires_measured_source_image_execution(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Run the real multi-size release benchmark and validate its full report."""
    import devtools.benchmarks.reverse_temporal_power_probe as probe

    monkeypatch.setattr(probe, "CONSTRUCTION_INDICES", (16, 32))
    monkeypatch.setattr(probe, "PROJECTION_INDICES", (16, 32))
    result = probe.run_probe()
    assert result["version"] == "0.63.0-schema8-certified-execution"
    assert result["status"] == ("RED" if result["release_blockers"] else "GREEN")
    assert result["execution_available"] is True
    assert result["execution_status"] == "available"
    assert result["measurements_complete"] is True
    assert result["execution_rejection_type"] is None
    assert object_record(result["source_audit"])["history_word_carrier_deleted"]
    assert object_record(result["source_audit"])["exact_future_tile_output_deleted"]
    assert result["projection"]
    assert result["measured_scaling_gate"] == (
        "BLOCKED" if result["release_blockers"] else "PASS"
    )
    assert "source_image_runtime_contract_unverified" not in text_values(
        result["release_blockers"]
    )
    assert not result["temporal_continuation_interpreter_present"]
    assert "powered_output_still_replays_temporal_interpreter" not in text_values(
        result["release_blockers"]
    )
    projection = result["projection"]
    assert isinstance(projection, list)
    for row in projection:
        record = object_record(row)
        assert record["runtime_image_matches_scalar"] is True
        assert record["source_image_replay_stable"] is True
        assert record["resource_accounting_exact"] is True
        publications = record["source_image_publications"]
        projection_publications = record["source_image_projection_publications"]
        assert type(publications) is int and publications > 0
        assert type(projection_publications) is int and projection_publications > 0
