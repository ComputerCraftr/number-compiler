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
    assert metrics.operator_nodes == 0
    assert metrics.compose_operations == 0
    assert term._power is None
    assert len(term._compiler.nodes) == 1
    # The exact digit is owned by the source image; no compatibility
    # BlockPower descriptor or scheduler child traversal is constructed.
    pairs = 256 // 2
    assert term.maximum_width == (
        (term.seed + 2).bit_length() + (19 * pairs + 31) // 32 + 2
    )
    counters = term._ledger.snapshot().counters
    assert counters["collatz_physical_temporal_run_actions"] > 0
    assert counters.get("collatz_physical_transient_leaf_steps", 0) == 0
    assert counters["source_image_postorder_frames"] > 0
    assert counters.get("source_image_primitive_applications", 0) == 0
    assert counters.get("source_image_demanded_composite_applications", 0) == 1
    workspace = term._workspace
    assert workspace is not None
    assert len(workspace.support) == 1
    assert workspace.support[0].saturated
    from devtools.benchmarks.collatz_temporal_power_probe import _source_image_work
    from number_compiler.resources.metric_collection import collect_ledger_metrics

    source_work, operand_bits, seal_bytes = _source_image_work(metrics)
    assert source_work < 25_000
    assert operand_bits > 0
    assert seal_bytes > 0
    assert counters["source_image_publications"] > 0
    assert counters["source_image_projection_publications"] > 0
    assert counters.get("higher_concrete_operation_evaluations", 0) == 0
    assert collect_ledger_metrics(term._ledger).resource_audit_complete
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
    assert counters["collatz_physical_temporal_run_actions"] > 0
    assert counters.get("collatz_physical_macro_bounded_base_steps", 0) == 0
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


@pytest.mark.parametrize("seed,steps", ((1, 1), (27, 16), (17, 29), (255, 33)))
def test_collatz_width_uses_admitted_affine_width_without_output_numerator(
    seed: int, steps: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("width demand constructed the affine output numerator")

    monkeypatch.setattr(PoweredCollatzTerm, "_source_numerator", forbidden)
    expected = seed
    for _ in range(steps):
        expected = _physical(expected)

    term = PoweredCollatzTerm(seed, steps)
    assert term.width() == expected.bit_length()
    assert term._ledger.counters["affine_width_requests"] == 1
    assert term.width() == expected.bit_length()
    assert term._ledger.counters["affine_width_requests"] == 1


def test_collatz_huge_cycle_width_uses_constant_image_without_huge_denominator(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("cycle width constructed an affine output numerator")

    monkeypatch.setattr(PoweredCollatzTerm, "_source_numerator", forbidden)
    steps = 10**12
    term = PoweredCollatzTerm(1, steps)
    assert term.width() == (1, 4, 2)[steps % 3].bit_length()
    assert term._ledger.counters["affine_width_requests"] == 1
    assert term._ledger.counters.get("collatz_physical_aggregate_demands", 0) == 0
    workspace = term._workspace
    assert workspace is not None
    image = workspace.image_node(workspace.root_payload)
    assert image.summary.transfer.upper == 0
    assert image.summary.transfer.lower == 1


@pytest.mark.parametrize("seed,steps", [(27, 16), (1, 10**12)])
def test_collatz_requested_clock_width_uses_sealed_tape_summary(
    seed: int,
    steps: int,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.collatz import block_power

    term = PoweredCollatzTerm(seed, steps)
    clock = term.s_arithmetic_clock()
    workspace = term._workspace
    assert workspace is not None
    summary = workspace.tape_width_summary
    assert summary is not None
    assert summary.physical_ticks == steps
    assert clock.events == summary.odd_steps
    affine_width_requests = term._ledger.counters.get("affine_width_requests", 0)
    aggregate_demands = term._ledger.counters.get(
        "collatz_physical_aggregate_demands", 0
    )
    if seed == 1:
        expected = (1, 4, 2)[steps % 3]
    else:
        expected = seed
        for _ in range(steps):
            expected = _physical(expected)

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("sealed tape width fell through to affine width work")

    monkeypatch.setattr(PoweredCollatzTerm, "_source_numerator", forbidden)
    monkeypatch.setattr(block_power, "nonnegative_affine_width", forbidden)
    assert term.width() == summary.source_width + summary.blank.delta
    assert term.width() == summary.target_width == expected.bit_length()
    assert (
        term._ledger.counters.get("affine_width_requests", 0) == affine_width_requests
    )
    assert (
        term._ledger.counters.get("collatz_physical_aggregate_demands", 0)
        == aggregate_demands
    )


def test_collatz_requested_clock_width_rejects_changed_action_binding() -> None:
    term = PoweredCollatzTerm(27, 16)
    term.s_arithmetic_clock()
    workspace = term._workspace
    assert workspace is not None
    assert workspace.tape_width_summary is not None

    term.steps += 1
    with pytest.raises(ValueError, match="another source/action"):
        term.width()


@pytest.mark.validation
def test_high_entropy_collatz_point_uses_balanced_source_cylinder() -> None:
    """A cold N-bit source publishes one root and charges balanced precision."""
    steps = 4096
    rng = random.Random(0xF50B1A)
    seed = (1 << (steps - 1)) | rng.getrandbits(steps - 1) | 1
    term = PoweredCollatzTerm(seed, steps)
    assert term.digit(0) in (0, 1)
    counters = term._ledger.counters
    leaves = (steps + 63) // 64
    assert counters.get("collatz_physical_composite_cutover_chunks", 0) == 0
    assert counters["collatz_physical_balanced_effect_compositions"] <= leaves
    assert counters["collatz_physical_balanced_effect_composition_operand_bits"] <= (
        2 * steps * steps.bit_length()
    )
    assert 0 < counters["collatz_physical_transient_leaf_steps"] < steps
    assert (
        counters["collatz_physical_transient_leaf_steps"]
        == counters["collatz_physical_finite_block_cold_steps"]
    )
    assert counters["collatz_physical_finite_block_hits"] > 0
    assert counters["collatz_physical_finite_block_lookups"] == (
        counters["collatz_physical_finite_block_hits"]
        + counters["collatz_physical_finite_block_misses"]
    )
    assert counters["collatz_physical_transient_leaf_operand_bits"] > 0
    assert counters["collatz_physical_balanced_stack_frames"] > 0
    assert term._power is None
    assert len(term._compiler.nodes) == 1
    workspace = term._workspace
    assert workspace is not None
    assert len(workspace.support) == 1
    assert workspace.support[0].saturated
    assert not workspace.balanced_stack


@pytest.mark.validation
def test_public_collatz_radices_share_the_same_physical_powered_backend() -> None:
    """Run the end-to-end public radix 2/3/6/12 projection matrix."""
    compiler = NumberCompiler()
    for radix in (2, 3, 6, 12):
        term = compiler.project_nth("collatz", 10, seed=27, radix=radix)
        assert term.metrics.projection_work == 0
        assert term.materialize(max_bits=10_000) == 214


@pytest.mark.validation
def test_collatz_temporal_release_probe_reports_measured_source_image_execution(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Run the real multi-size Collatz release benchmark and full report audit."""
    import devtools.benchmarks.collatz_temporal_power_probe as probe

    monkeypatch.setattr(probe, "CONSTRUCTION_STEPS", (16, 32))
    monkeypatch.setattr(probe, "PROJECTION_STEPS", (16, 32))
    result = probe.run_probe()
    assert result["version"] == "0.62.0-schema8-source-image-observation"
    assert result["status"] == "GREEN"
    assert result["execution_available"] is True
    assert result["execution_status"] == "available"
    assert result["measurements_complete"] is True
    assert result["execution_rejection_type"] is None
    assert result["schema_version"] == 8
    assert result["projection"]
    assert result["public_radix_exactness"] == {"2": 214, "3": 214, "6": 214}
    assert result["public_radix_exactness_available"] is True
    assert result["measured_scaling_gate"] == "PASS"
    assert result["source_image_runtime_contract"] is True
    assert "certified_path_published_no_recursive_field_images" not in text_values(
        result["release_blockers"]
    )
    assert "source_image_composition_exceeds_binary_envelope" not in text_values(
        result["release_blockers"]
    )
    assert "source_image_runtime_contract_unverified" not in text_values(
        result["release_blockers"]
    )
    projection = result["projection"]
    assert isinstance(projection, list)
    for row in projection:
        record = object_record(row)
        for name in (
            "collatz_physical_temporal_run_actions",
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
