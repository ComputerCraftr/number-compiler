"""Regression coverage for the family-first CLI and selector contract."""

from __future__ import annotations

import json

import pytest

from number_compiler.api.cli import main


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


def test_old_commands_and_metrics_flag_are_rejected_with_migration_hint() -> None:
    with pytest.raises(SystemExit) as old_command:
        main(["nth", "fermat", "0"])
    assert old_command.value.code == 2

    with pytest.raises(SystemExit) as old_metrics:
        main(["fermat", "--nth", "0", "--metrics"])
    assert old_metrics.value.code == 2


def test_unsupported_family_selector_is_rejected_before_execution() -> None:
    with pytest.raises(SystemExit) as unsupported:
        main(["fermat", "--nth", "0", "--info", "clock"])
    assert unsupported.value.code == 2
