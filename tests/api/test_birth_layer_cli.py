"""Birth-layer demand preserves finite source scope and lazy observations."""

import json

import pytest

from number_compiler.api import cli
from number_compiler.api.cli_types import DoubleReverseObservationOptions
from number_compiler.api.observation_types import ObservationId


def test_birth_layer_cli_is_a_finite_source_observation(
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
                "temporal.birth-layers",
                "--info",
                "metrics",
                "--spatial-bank-morphism-count",
                "3",
                "--temporal-open-ring-lookback",
                "8",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    assert packet["value"] is None
    birth = packet["info"]["temporal.birth-layers"]
    assert birth["status"] == "available"
    assert birth["pairs"] == 3
    assert birth["f_steps"] == 8
    assert birth["indefinite_source_authorized"] is False
    assert len(birth["final_pairs"]) == 3
    measured = packet["info"]["metrics"]["execution_metrics"]["observations"]
    assert measured["double_reverse_birth_layer_publications"] == 1
    assert measured["double_reverse_birth_layer_strip_steps"] == 8
    assert measured["double_reverse_birth_layer_source_port_reads"] == 18


def test_birth_horizon_does_not_relax_ray_observer_budget() -> None:
    birth = ObservationId.TEMPORAL_BIRTH_LAYERS
    ray = ObservationId.TEMPORAL_OPEN_RING
    assert DoubleReverseObservationOptions(info=(birth,), open_ring_lookback=160)
    with pytest.raises(ValueError, match="32"):
        DoubleReverseObservationOptions(info=(birth, ray), open_ring_lookback=33)
    with pytest.raises(ValueError, match="160"):
        DoubleReverseObservationOptions(info=(birth,), open_ring_lookback=161)
