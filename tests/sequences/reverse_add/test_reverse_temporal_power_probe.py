from pathlib import Path

import pytest

from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from tests.support.report_values import object_record, text_values


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
def test_reverse_production_has_only_direct_powered_hashlife_path() -> None:
    """Exercise the complete public N=256 route and its release counters."""
    term = ReverseAddPoweredTerm(196, 256)
    value = 196
    for _ in range(256):
        text = str(value)
        value += int(text[::-1])
    position = term.maximum_width // 3
    expected_digits = str(value)[::-1]
    assert term.digit(position) == int(expected_digits[position])
    metrics = term.metrics()
    runtime = term._point_index().metrics()
    assert (
        metrics.hashlife_temporal_leaf_applications
        == runtime.tile_scheduler_leaf_function_applications
    )
    assert runtime.sequential_generation_advances == 0
    assert runtime.higher_action_continuation_requests == 0
    assert runtime.temporal_leaf_diamond_descents == 0
    assert metrics.hashlife_direct_powered_point_queries == 1
    assert metrics.hashlife_section_cache_entries == 0
    assert metrics.hashlife_leaf_cache_entries == 0
    assert (
        metrics.hashlife_boundary_cache_entries <= 6 * term.maximum_width.bit_length()
    )
    # All old whole-field causal metrics are hard zero because the engine is no
    # longer reachable from ReverseAddPoweredTerm.
    assert metrics.spacetime_primitive_field_steps == 0
    assert metrics.spacetime_primitive_slab_steps == 0
    assert metrics.spacetime_primitive_forcing_steps == 0


def test_reverse_power_source_has_no_slow_temporal_backend() -> None:
    import devtools.proofs.block_runtime as runtime
    import number_compiler.hashlife.observation.hashlife_projection as hashlife
    import number_compiler.sequences.reverse_add.power as reverse_power

    power_text = Path(reverse_power.__file__).read_text()
    hash_text = Path(hashlife.__file__).read_text()
    runtime_text = Path(runtime.__file__).read_text()
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
    # Every action, interner slot, and parent binding is now charged.  The old
    # 100-entry success expectation counted only a subset of those stores.
    # Keep it as an exhausted-budget regression.  Correctness is exercised on
    # a separate unbounded ledger; the performance probe below remains RED and
    # records the current higher-interface retention instead of disguising it
    # behind a larger arbitrary cap.
    constrained = ReverseAddPoweredTerm(
        196, 128, max_context_nodes=100, max_cache_entries=100
    )
    with pytest.raises(BlockContextBudgetExceeded):
        constrained.digit(constrained.maximum_width // 3)
    term = ReverseAddPoweredTerm(196, 128)
    assert 0 <= term.digit(term.maximum_width // 3) <= 9
    metrics = term.metrics()
    assert metrics.temporal_parent_requests == (
        metrics.temporal_parent_early_hits + metrics.temporal_parent_compositions
    )
    assert metrics.proof_machine_applications == metrics.whole_word_sweeps == 0


def test_hashlife_contract_does_not_require_a_global_finite_quotient_module() -> None:
    import number_compiler

    package = Path(number_compiler.__file__).resolve().parent
    assert not (package / "powering_closure.py").exists()


def test_release_probe_does_not_call_direct_cutover_logarithmic_until_action_retention_closes() -> (
    None
):
    from devtools.benchmarks.reverse_temporal_power_probe import (
        _projection_closure_flags,
    )

    production = [
        {
            "index_bits": 9,
            "temporal_leaf_applications": 0,
            "direct_powered_point_queries": 1,
            "section_cache_entries": 0,
            "leaf_cache_entries": 0,
            "retained_action_nodes": 11_000,
        }
    ]
    carrier_fixed, legacy_removed, polylog_sample, closure = _projection_closure_flags(
        production
    )
    assert carrier_fixed
    assert legacy_removed
    assert not polylog_sample
    assert not closure


@pytest.mark.validation
def test_reverse_release_probe_reports_available_schema6_execution_as_red(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Run the real multi-size release benchmark and validate its full report."""
    import devtools.benchmarks.reverse_temporal_power_probe as probe

    monkeypatch.setattr(probe, "CONSTRUCTION_INDICES", (16, 32))
    monkeypatch.setattr(probe, "PROJECTION_INDICES", (16, 32))
    result = probe.run_probe()
    assert result["version"] == "0.62.0-schema6-certified-execution"
    assert result["status"] == "RED"
    assert result["execution_available"] is True
    assert result["execution_status"] == "available"
    assert result["measurements_complete"] is True
    assert result["execution_rejection_type"] is None
    assert not result["linear_bisimulation_checkpoint_installed"]
    assert not result["history_word_carrier_present"]
    assert not result["spacetime_macrocell_absorption_installed"]
    assert not result["lazy_program_projection_installed"]
    assert object_record(result["source_audit"])["history_word_carrier_deleted"]
    assert object_record(result["source_audit"])["exact_future_tile_output_deleted"]
    assert result["projection"]
    assert result["measured_scaling_gate"] == "BLOCKED"
    assert "certified_path_published_no_tile_actions" not in text_values(
        result["release_blockers"]
    )
    assert "successor_closure_unproved" not in text_values(result["release_blockers"])
    assert "completed_result_entries_exceeds_doubling_envelope" in text_values(
        result["release_blockers"]
    )
    assert not result["temporal_continuation_interpreter_present"]
    assert "powered_output_still_replays_temporal_interpreter" not in text_values(
        result["release_blockers"]
    )
    assert not result["spacetime_logarithmic_closure_proved"]
