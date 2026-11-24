"""The independent CF clock coexists with the selected Antihydra guard."""

from __future__ import annotations

import json

import pytest

from number_compiler.api.cli import main
from tests.support.mahler_harmonic_reference import mapping

_PREFIX = ["antihydra", "--nth", "254", "--no-value", "--format", "json"]
_CF = ["--info", "arithmetic.continued-fraction"]
_SAFE = ["--info", "safety.ledger", "--safety-ledger-detail", "finite-safety"]


@pytest.mark.parametrize("first", [False, True])
def test_cf_and_source_guard_share_horizon_without_changing_results(
    first: bool, capsys: pytest.CaptureFixture[str]
) -> None:
    assert main([*_PREFIX, *_CF, "--safety-horizon", "4"]) == 0
    original: object = json.loads(capsys.readouterr().out)
    expected = mapping(
        mapping(mapping(original)["info"])["arithmetic.continued-fraction"]
    )
    views = [*_CF, *_SAFE] if first else [*_SAFE, *_CF]
    assert (
        main(
            [
                *_PREFIX,
                *views,
                "--safety-horizon",
                "4",
                "--fractional-tail",
                "1/57",
            ]
        )
        == 0
    )
    combined: object = json.loads(capsys.readouterr().out)
    info = mapping(mapping(combined)["info"])
    assert info["arithmetic.continued-fraction"] == expected
    safety = mapping(mapping(mapping(info["safety.ledger"])["views"])["finite-safety"])
    assert mapping(safety["value"])["completed_ticks"] == 4
