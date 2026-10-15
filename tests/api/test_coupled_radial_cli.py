"""Public observers expose radial coupling only on explicit information demand."""

from __future__ import annotations

import json

import pytest

from number_compiler.api import cli, cli_render
from number_compiler.arithmetic.fields.homogeneous_growth import (
    GrowthArithmeticEvaluator,
)
from number_compiler.sequences.collatz.border_identity import CollatzSegmentIdentity
from number_compiler.sequences.collatz.radial_boundary_coupling import (
    CollatzRadialBoundarySeam,
)


def _fail_if_observed(*_args: object, **_kwargs: object) -> dict[str, object]:
    raise AssertionError("undemanded radial boundary coupling was computed")


def test_boundary_macro_cli_exposes_coupling_without_rendering(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    observed: list[bool] = []
    original = CollatzRadialBoundarySeam.observation

    def record_observation(
        self: CollatzRadialBoundarySeam,
        evaluator: GrowthArithmeticEvaluator,
        *,
        width: int,
        previous_odds: int,
        previous_halvings: int,
        next_identity: CollatzSegmentIdentity | None,
    ) -> dict[str, object]:
        observed.append(True)
        return original(
            self,
            evaluator,
            width=width,
            previous_odds=previous_odds,
            previous_halvings=previous_halvings,
            next_identity=next_identity,
        )

    monkeypatch.setattr(CollatzRadialBoundarySeam, "observation", record_observation)
    monkeypatch.setattr(cli_render, "_render_value", _fail_if_observed)
    assert (
        cli.main(
            [
                "collatz",
                "--seed",
                "13",
                "--nth",
                "7",
                "--no-value",
                "--info",
                "temporal.macro",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    assert packet["value"] is None
    boundary = packet["info"]["temporal.macro"]
    coupled = boundary["coupled_radial_boundary"]
    assert coupled["repeated_skew_cylinder"]["scope"] == (
        "same source-admitted parity word only"
    )
    assert coupled["high_digit_transport"]
    assert observed


@pytest.mark.parametrize(
    ("info", "no_value"), (((), False), (("--info", "metrics"), True))
)
def test_metrics_and_no_info_do_not_demand_radial_boundary_coupling(
    info: tuple[str, ...],
    no_value: bool,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    monkeypatch.setattr(CollatzRadialBoundarySeam, "observation", _fail_if_observed)
    args = ["collatz", "--seed", "13", "--nth", "7"]
    if no_value:
        args.append("--no-value")
    args.extend(info)
    args.extend(("--format", "json"))
    assert cli.main(args) == 0
    packet = json.loads(capsys.readouterr().out)
    if no_value:
        assert packet["value"] is None
        assert "collatz" == packet["family"]
        assert packet["info"]["metrics"]
    else:
        assert packet["value"] == "4"


def test_mahler_information_exposes_radial_affine_transport(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    monkeypatch.setattr(cli_render, "_render_value", _fail_if_observed)
    assert (
        cli.main(
            [
                "antihydra",
                "--nth",
                "3",
                "--no-value",
                "--info",
                "arithmetic.mahler",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    mahler = packet["info"]["arithmetic.mahler"]
    associated = mahler["value"]["associated_action"]
    assert associated["radial_affine_arithmetic"]["high_digit_transport"]
    assert (
        "authenticated finite h image"
        in associated["radial_affine_arithmetic"]["scope"]
    )
