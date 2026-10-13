"""Regression coverage for the family-first CLI and selector contract."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from number_compiler.api.cli import main
from number_compiler.api.cli_requests import parse_request
from number_compiler.api.family_registry import CAPABILITIES


def test_family_nth_json_has_the_canonical_envelope(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert main(["fermat", "--nth", "0", "--format", "json"]) == 0
    row = json.loads(capsys.readouterr().out)
    assert set(row) == {"family", "index", "index_unit", "output_base", "value", "info"}
    assert row == {
        "family": "fermat",
        "index": 0,
        "index_unit": "fermat_index",
        "output_base": 10,
        "value": "3",
        "info": {},
    }


def test_registered_certificate_adapter_preserves_rejection_envelope(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    certificate = tmp_path / "invalid.json"
    certificate.write_text("{}", encoding="utf-8")
    assert (
        main(["antihydra", "--verify-nonhalting", str(certificate), "--format", "json"])
        == 1
    )
    packet = json.loads(capsys.readouterr().out)
    assert packet["nonhalting_certified"] is False
    assert packet["status"] == "rejected"
    assert packet["reason"]


def test_list_families_has_registry_units_and_no_term_execution(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert parse_request(["--list-families"]) is None
    assert main(["--list-families"]) == 0
    captured = capsys.readouterr()
    assert captured.err == ""
    lines = [line for line in captured.out.splitlines() if not line.startswith("  ")]
    assert len(lines) == len(CAPABILITIES)
    assert "--events E (accelerated_odd_events)" in captured.out
    assert "--verify-nonhalting PATH" in captured.out
    for line, (name, capability) in zip(lines, CAPABILITIES.items(), strict=True):
        assert line == (
            f"{name}: --nth N ({capability.unit}); "
            f"info: {', '.join(capability.nth_info)}"
        )


def test_no_value_and_repeatable_selectors_keep_payloads_under_info(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        main(
            [
                "fermat",
                "--nth",
                "0",
                "--no-value",
                "--info",
                "primality",
                "--info",
                "metrics",
                "--format",
                "json",
            ]
        )
        == 0
    )
    row = json.loads(capsys.readouterr().out)
    assert row["value"] is None
    assert set(row["info"]) == {"primality", "metrics"}
    assert row["info"]["primality"]["status"] == "prime"


def test_text_keeps_digits_on_stdout_and_info_dict_on_stderr(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert main(["fermat", "--nth", "0", "--info", "metrics"]) == 0
    captured = capsys.readouterr()
    assert captured.out == "3\n"
    info = json.loads(captured.err)
    assert set(info) == {"metrics"}
    assert info["metrics"]["family"] == "fermat"


def test_unsupported_family_selector_is_rejected_before_execution() -> None:
    with pytest.raises(SystemExit) as unsupported:
        main(["fermat", "--nth", "0", "--info", "clock"])
    assert unsupported.value.code == 2


@pytest.mark.parametrize(
    ("family", "selector", "index", "extra", "name"),
    [
        ("reverse-add", "--nth", "0", ["--seed", "196"], "metrics"),
        ("reverse-add", "--nth", "0", ["--seed", "1"], "metrics"),
        ("collatz", "--nth", "0", ["--seed", "27"], "clock"),
        ("collatz", "--events", "0", ["--seed", "27"], "clock"),
        ("antihydra", "--nth", "0", [], "ledger"),
        ("antihydra", "--nth", "0", [], "clock"),
        ("antihydra", "--nth", "0", [], "mahler"),
        ("prime", "--nth", "0", [], "metrics"),
        ("fermat", "--nth", "0", [], "primality"),
        ("mersenne", "--nth", "2", [], "primality"),
    ],
)
def test_info_packets_share_selector_metadata_without_unsolicited_metrics(
    capsys: pytest.CaptureFixture[str],
    family: str,
    selector: str,
    index: str,
    extra: list[str],
    name: str,
) -> None:
    assert (
        main(
            [
                family,
                selector,
                index,
                *extra,
                "--no-value",
                "--info",
                name,
                "--format",
                "json",
            ]
        )
        == 0
    )
    row = json.loads(capsys.readouterr().out)
    packet = row["info"][name]
    assert {key: packet[key] for key in ("family", "index", "index_unit")} == {
        key: row[key] for key in ("family", "index", "index_unit")
    }
    assert packet["kind"] == name
    assert isinstance(packet["status"], str)
    if name != "metrics":
        assert not {
            "work_counters",
            "source_work_counters",
            "peak_nodes",
            "retained_nodes",
            "execution_metrics",
        }.intersection(packet)


@pytest.mark.parametrize("name", ["primality", "factor"])
def test_unresolved_special_information_has_consistent_exit_status(
    capsys: pytest.CaptureFixture[str],
    name: str,
) -> None:
    assert (
        main(["fermat", "--nth", "4", "--no-value", "--info", name, "--format", "json"])
        == 3
    )
    packet = json.loads(capsys.readouterr().out)["info"][name]
    assert packet["status"] == "unknown"
    assert packet["decided"] is False
