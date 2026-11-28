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
    from number_compiler.sequences.reverse_add import temporal_mirrored_diagonal

    monkeypatch.setattr(
        temporal_mirrored_diagonal, "native_decimal_string_transport", _forbidden
    )
    assert (
        main(
            [
                "reverse-add",
                "--seed",
                "196",
                "--nth",
                "110422",
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
    assert action["max_work_units"] == 331264


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


def test_extended_center_cli_reports_literal_endpoint_and_refuses_before_tick(
    capsys: pytest.CaptureFixture[str], monkeypatch: pytest.MonkeyPatch
) -> None:
    from number_compiler.sequences.reverse_add import (
        temporal_mirrored_diagonal as diagonal,
    )

    started: list[int] = []
    original = diagonal.center11_tick_work

    def record(width: int) -> int:
        started.append(width)
        return original(width)

    monkeypatch.setattr(diagonal, "center11_tick_work", record)
    args = [
        "reverse-add",
        "--seed",
        "196",
        "--nth",
        "778",
        "--no-value",
        "--info",
        "temporal.mirrored-diagonal",
        "--format",
        "json",
    ]
    assert main(args) == 0
    packet = json.loads(capsys.readouterr().out)["info"]["temporal.mirrored-diagonal"]
    value = 196
    for _ in range(778):
        value += int(str(value)[::-1])
    text = str(value)
    halves = [
        int(text[: (len(text) + 1) // 2]) % 11,
        int(text[len(text) // 2 :][::-1]) % 11,
    ]
    assert packet["target_width"] == len(text)
    assert packet["center11"]["physical_target_halves"] == halves
    assert packet["repetition_authority"] == "none"
    assert len(started) == 778
    assert sum(map(original, started)) <= diagonal.CENTER11_WORK_UNITS
    started.clear()
    args[args.index("778")] = "779"
    assert main(args) == 3
    refused = json.loads(capsys.readouterr().out)["info"]["temporal.mirrored-diagonal"]
    assert refused["status"] == "unavailable"
    assert len(started) == 779  # last callback checks admission before tick 779
    assert sum(map(original, started[:-1])) <= diagonal.CENTER11_WORK_UNITS
    assert sum(map(original, started)) > diagonal.CENTER11_WORK_UNITS


def test_zero_center_request_keeps_existing_unavailable_packet(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        main(
            [
                "reverse-add",
                "--seed",
                "196",
                "--nth",
                "0",
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
    assert action["reason"] == "mirrored carry observation exceeds its finite horizon"
    assert action["max_physical_ticks"] == 512
