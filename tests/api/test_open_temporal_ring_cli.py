"""Finite source-ring demands are explicit and never claim full-root pumping."""

from __future__ import annotations

import json

import pytest

from number_compiler.api import cli


@pytest.mark.parametrize(
    "family,index,count", (("reverse-add", 2, 1), ("2rev10", 64, 4))
)
def test_open_ring_is_explicit_finite_information(
    family: str, index: int, count: int, capsys: pytest.CaptureFixture[str]
) -> None:
    assert (
        cli.main(
            [
                family,
                "--seed",
                "196",
                "--nth",
                str(index),
                "--no-value",
                "--info",
                "temporal.open-ring",
                "--info",
                "metrics",
                "--spatial-bank-morphism-count",
                str(count),
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    assert packet["value"] is None
    observation = packet["info"]["temporal.open-ring"]
    assert observation["kind"] == "temporal.open-ring"
    assert observation["temporal_repeat_certified"] is False
    assert observation["status"] == "available"
    measured = packet["info"]["metrics"]["execution_metrics"]["observations"]
    if family == "reverse-add":
        assert observation["complete_integer_certified"] is False
        assert len(observation["source_pair_domains"]) == count
        assert measured["reverse_q19_temporal_ring_constraint_cells"] > 0
        assert measured["double_reverse_open_ring_source_ports"] is None
        phases = observation["joint_cyclotomic_center"]["correlated_carry_phases"]
        for frame in phases:
            for phase in frame:
                witnesses = phase["first_reset_witnesses"]
                assert witnesses
                assert set(phase["first_reset_positions"]) == {
                    witness["position"] for witness in witnesses
                }
                assert set(phase["middle_transfers"]) == {
                    witness["middle_transfer"] for witness in witnesses
                }
    else:
        assert observation["pair_count"] == count
        assert len(observation["output_words"]["carry_xor"]) == count
        assert measured["double_reverse_open_ring_window_publications"] > 0
        assert measured["reverse_q19_temporal_ring_constraint_cells"] is None


@pytest.mark.parametrize("family", ("2rev10", "reverse-add"))
def test_metrics_does_not_construct_harmonic_banks(
    family: str, capsys: pytest.CaptureFixture[str]
) -> None:
    assert (
        cli.main(
            [
                family,
                "--seed",
                "196",
                "--nth",
                "64",
                "--no-value",
                "--info",
                "metrics",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    observed = packet["info"]["metrics"]["execution_metrics"]["observations"]
    assert observed["double_reverse_open_ring_source_ports"] is None
    assert observed["double_reverse_birth_layer_source_port_reads"] is None
    assert observed["reverse_q19_temporal_ring_constraint_cells"] is None


def test_open_ring_lookback_budget_rejects_before_execution(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "196",
                "--nth",
                "64",
                "--no-value",
                "--info",
                "temporal.open-ring",
                "--temporal-open-ring-lookback",
                "33",
            ]
        )
        == 2
    )
    assert "32" in capsys.readouterr().err


@pytest.mark.parametrize("family", ("2rev10", "reverse-add"))
def test_unadmitted_open_ring_reports_unavailable(
    family: str,
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(
            [
                family,
                "--seed",
                "196",
                "--nth",
                "0",
                "--no-value",
                "--info",
                "temporal.open-ring",
                "--format",
                "json",
            ]
        )
        == 3
    )
    packet = json.loads(capsys.readouterr().out)
    assert packet["info"]["temporal.open-ring"]["status"] == "unavailable"
