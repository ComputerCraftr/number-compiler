"""Explicit matrix demands start at the selected term; other observers stay lazy."""

import json

import pytest

from number_compiler.api.cli import main


@pytest.mark.parametrize(
    ("family", "index", "horizon"),
    [("reverse-add", 79, 2), ("2rev10", 32, 4)],
)
def test_matrix_cli_demand_and_default_laziness(
    family: str,
    index: int,
    horizon: int,
    capsys: pytest.CaptureFixture[str],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.api import matrix_observation

    arguments = [family, "--seed", "196", "--nth", str(index), "--format", "json"]
    assert (
        main(
            [
                *arguments,
                "--info",
                "temporal.matrix",
                "--temporal-matrix-steps",
                str(horizon),
            ]
        )
        == 0
    )
    requested = json.loads(capsys.readouterr().out)
    matrix = requested["info"]["temporal.matrix"]
    assert matrix["status"] == "available"
    assert matrix["physical_interval"] == [index, index + horizon]
    assert matrix["execution_authority"] is False
    assert "trace" not in matrix
    if family == "2rev10":
        assert matrix["chronological_future_roots_constructed"] is False
    else:
        assert matrix["exact_completed_children_joined"] is False
    assert "conditional_depth_matrix" not in matrix

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("ordinary demand built a matrix")

    monkeypatch.setattr(matrix_observation, "observe_matrix", forbidden)
    assert main([*arguments, "--info", "metrics"]) == 0
    ordinary = json.loads(capsys.readouterr().out)
    assert ordinary["value"] == requested["value"]
    assert "temporal.matrix" not in ordinary["info"]
