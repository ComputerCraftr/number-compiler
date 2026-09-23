from __future__ import annotations

import random
from typing import Never

import pytest

from number_compiler.api.number_api import NumberCompiler
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from tests.support.report_values import object_record, text_values


def _physical(value: int) -> int:
    return 3 * value + 1 if value & 1 else value // 2


@pytest.mark.validation  # Forty independent complete public orbit projections.
def test_physical_collatz_block_power_matches_scalar_randomly() -> None:
    rng = random.Random(0xC011A72)
    for _ in range(40):
        seed = rng.randrange(1, 1 << 12)
        steps = rng.randrange(0, 18)
        expected = seed
        for _ in range(steps):
            expected = _physical(expected)
        term = PoweredCollatzTerm(seed, steps)
        assert term.materialize(max_bits=10_000) == expected


@pytest.mark.validation
def test_collatz_powered_point_uses_admitted_source_image_without_replay() -> None:
    """Exercise the complete N=256 public point route and its work envelope."""
    term = PoweredCollatzTerm(27, 256)
    assert term.digit(0) == 0
    metrics = term.metrics()
    assert metrics.temporal_leaf_applications == 0
    assert metrics.direct_powered_point_queries == 1
    assert metrics.operator_nodes <= 2 * (256).bit_length()
    assert metrics.compose_operations <= 2 * (256).bit_length()
    # The compatibility descriptor above is not the executor. Check actual
    # source-image construction and bounded-base work as well as the digit.
    pairs = 256 // 2
    assert term.maximum_width == (
        (term.seed + 2).bit_length() + (19 * pairs + 31) // 32 + 2
    )
    counters = term._ledger.snapshot().counters
    assert counters["collatz_physical_macro_bounded_base_steps"] > 0
    assert counters["source_image_postorder_frames"] > 0
    assert counters["source_image_primitive_applications"] > 0
    from devtools.benchmarks.collatz_temporal_power_probe import _source_image_work

    source_work, operand_bits, seal_bytes = _source_image_work(metrics)
    assert source_work < 25_000
    assert operand_bits > 0
    assert seal_bytes > 0
    assert counters["source_image_publications"] > 0
    assert counters["source_image_projection_publications"] > 0
    assert counters.get("higher_concrete_operation_evaluations", 0) == 0
    assert metrics.resource_audit_complete
    assert metrics.resource_accounting_mismatch == 0


@pytest.mark.validation  # N=64 source-bound production contract.
def test_collatz_production_uses_dyadic_source_image_morphism(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.collatz.powered_local_codec import (
        CollatzPoweredLocalCodec,
    )

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("raw radix-4 word codec received a binary source")

    monkeypatch.setattr(CollatzPoweredLocalCodec, "source_action", forbidden)
    term = PoweredCollatzTerm(27, 64)
    assert term.digit(0) == 1
    counters = term._ledger.snapshot().counters
    assert counters["collatz_physical_macro_bounded_base_steps"] > 0
    assert counters["collatz_physical_action_publications"] > 0
    assert counters["source_image_publications"] > 0
    assert counters["source_image_projection_publications"] > 0
    assert counters["collatz_image_radix_demands"] > 0
    assert counters.get("sequential_generation_advances", 0) == 0


def test_collatz_recursive_images_do_not_use_retired_spatial_or_replay_paths(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.hashlife.execution.continuations.higher_bimachine import (
        HigherBimachineRuntime,
    )
    from number_compiler.hashlife.execution.continuations.higher_macro_composer import (
        HigherSpatialMacroComposer,
    )

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("retired whole-source Collatz path was reached")

    monkeypatch.setattr(HigherSpatialMacroComposer, "compile", forbidden)
    monkeypatch.setattr(HigherBimachineRuntime, "point", forbidden)
    monkeypatch.setattr(HigherBimachineRuntime, "width", forbidden)
    term = PoweredCollatzTerm(27, 16)
    assert term.digit(0) == 1
    assert term.width() == 7
    counters = term._ledger.snapshot().counters
    assert counters.get("higher_observation_fallback", 0) == 0
    assert counters.get("whole_word_symbol_visits", 0) == 0


@pytest.mark.validation
def test_public_collatz_radices_share_the_same_physical_powered_backend() -> None:
    """Run the end-to-end public radix 2/3/6/12 projection matrix."""
    compiler = NumberCompiler()
    for radix in (2, 3, 6, 12):
        term = compiler.project_nth("collatz", 10, seed=27, radix=radix)
        assert term.metrics.projection_work == 0
        assert term.materialize(max_bits=10_000) == 214


@pytest.mark.validation
def test_collatz_temporal_release_probe_reports_source_image_execution_as_red(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Run the real multi-size Collatz release benchmark and full report audit."""
    import devtools.benchmarks.collatz_temporal_power_probe as probe

    monkeypatch.setattr(probe, "CONSTRUCTION_STEPS", (16, 32))
    monkeypatch.setattr(probe, "PROJECTION_STEPS", (16, 32))
    result = probe.run_probe()
    assert result["version"] == "0.62.0-schema8-source-image-observation"
    assert result["status"] == "RED"
    assert result["execution_available"] is True
    assert result["execution_status"] == "available"
    assert result["measurements_complete"] is True
    assert result["execution_rejection_type"] is None
    assert not result["whole_state_successor_loop_present"]
    assert result["parity_itinerary_required_for_physical_nth_state"]
    assert not result["history_word_carrier_present"]
    assert not result["spacetime_macrocell_absorption_installed"]
    assert not result["lazy_program_projection_installed"]
    assert not result["linear_bisimulation_checkpoint_installed"]
    assert result["schema_version"] == 8
    assert result["projection"]
    assert result["public_radix_exactness"] == {"2": 214, "3": 214, "6": 214}
    assert result["public_radix_exactness_available"] is True
    assert result["measured_scaling_gate"] == "PASS"
    assert result["bounded_temporal_runtime_cutover_complete"] is False
    assert "certified_path_published_no_recursive_field_images" not in text_values(
        result["release_blockers"]
    )
    assert "source_image_composition_exceeds_binary_envelope" not in text_values(
        result["release_blockers"]
    )
    assert "successor_closure_unproved" not in text_values(result["release_blockers"])
    assert "source_global_powered_construction_bound_unproved" in text_values(
        result["release_blockers"]
    )
    projection = result["projection"]
    assert isinstance(projection, list)
    for row in projection:
        record = object_record(row)
        for name in (
            "collatz_physical_macro_bounded_base_steps",
            "source_image_publications",
        ):
            measured = record[name]
            assert type(measured) is int and measured > 0
    assert object_record(result["source_audit"])["history_word_carrier_deleted"]
    assert object_record(result["source_audit"])["exact_future_tile_output_deleted"]


def test_collatz_probe_rejects_missing_source_image_work(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A missing production counter cannot be reported as a cheap jump."""
    from dataclasses import replace

    import devtools.benchmarks.collatz_temporal_power_probe as probe
    from number_compiler.resources.collatz_power_metrics import (
        CollatzPhysicalBlockMetrics,
    )

    original_metrics = PoweredCollatzTerm.metrics

    def missing_work(self: PoweredCollatzTerm) -> CollatzPhysicalBlockMetrics:
        metrics = original_metrics(self)
        counters = dict(metrics.resource_work_counters)
        counters.pop("source_image_postorder_frames", None)
        return replace(metrics, resource_work_counters=counters)

    monkeypatch.setattr(probe, "PROJECTION_STEPS", (16,))
    monkeypatch.setattr(PoweredCollatzTerm, "metrics", missing_work)
    with pytest.raises(AssertionError, match="source-image-work-measurement-missing"):
        probe._projection_rows()
