"""Demanded centered actions preserve CLI laziness and exact finite scope."""

from __future__ import annotations

import json
from typing import Never

import pytest

from number_compiler.api.cli import main
from number_compiler.api.json_output import is_string_object_mapping
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def _forbidden(*_args: object, **_kwargs: object) -> Never:
    raise AssertionError("unrequested mirrored action was constructed")


@pytest.mark.parametrize("information", ("metrics", "temporal"))
def test_summary_does_not_construct_center_action(
    information: str,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    monkeypatch.setattr(ReverseAddPoweredTerm, "temporal_mirrored_diagonal", _forbidden)
    assert (
        main(
            [
                "reverse-add",
                "--seed",
                "196",
                "--nth",
                "20",
                "--no-value",
                "--info",
                information,
                "--format",
                "json",
            ]
        )
        == 0
    )
    assert capsys.readouterr().err == ""


def test_center_action_packet_has_exact_cumulative_difference(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        main(
            [
                "reverse-add",
                "--seed",
                "196",
                "--nth",
                "256",
                "--no-value",
                "--info",
                "temporal.mirrored-diagonal",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet: object = json.loads(capsys.readouterr().out)
    assert is_string_object_mapping(packet)
    info = packet["info"]
    assert is_string_object_mapping(info)
    action = info["temporal.mirrored-diagonal"]
    assert is_string_object_mapping(action)
    assert action["status"] == "available"
    center = action["center11"]
    assert is_string_object_mapping(center)
    assert center["source_halves"] == [8, 3]
    assert center["target_halves"] == [10, 9]
    assert center["cumulative_difference_before"] == 5
    assert center["cumulative_difference_after"] == 9


def test_out_of_range_center_request_refuses_before_construction(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    monkeypatch.setattr(ReverseAddPoweredTerm, "temporal_mirrored_diagonal", _forbidden)
    assert (
        main(
            [
                "reverse-add",
                "--seed",
                "196",
                "--nth",
                "513",
                "--no-value",
                "--info",
                "temporal.mirrored-diagonal",
                "--format",
                "json",
            ]
        )
        == 3
    )
    packet: object = json.loads(capsys.readouterr().out)
    assert is_string_object_mapping(packet)
    info = packet["info"]
    assert is_string_object_mapping(info)
    action = info["temporal.mirrored-diagonal"]
    assert is_string_object_mapping(action)
    assert action["status"] == "unavailable"
    assert action["max_physical_ticks"] == 512


def test_center_request_rejects_nondecimal_source(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        main(
            [
                "reverse-add",
                "--seed",
                "196",
                "--base",
                "2",
                "--nth",
                "1",
                "--no-value",
                "--info",
                "temporal.mirrored-diagonal",
            ]
        )
        == 2
    )
    assert "decimal base" in capsys.readouterr().err
