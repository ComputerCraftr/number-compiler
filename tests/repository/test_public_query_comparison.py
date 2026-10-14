"""Public comparison evidence retains every route and never conceals disagreement."""

import json
import sys
from collections.abc import Callable, Sequence
from pathlib import Path

import pytest

from devtools.benchmarks.public_query_comparison import Sample, compare


def test_public_routes_agree_and_warm_priming_is_retained() -> None:
    rows = compare("collatz", [0, 2], 1, ["cold", "warm", "bypass"], seed=27)
    assert len(rows) == 24
    assert sum(row["phase"] == "priming" for row in rows) == 6
    assert {row["route"] for row in rows} == {"cli", "point"}
    for row in rows:
        expected = 27 if row["horizon"] == 0 else 41
        if row["route"] == "cli":
            assert int(row["value"], row["output_base"]) == expected
        else:
            assert int(row["value"]) == (expected >> 2) & 1


def test_mismatched_cli_sample_is_retained_before_rejection(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from devtools.benchmarks import public_query_comparison as module

    def wrong(arguments: list[str], *, fresh: bool) -> tuple[float, dict[str, object]]:
        return 0.01, {"value": "0", "info": {"metrics": None}}

    monkeypatch.setattr(module, "cli_sample", wrong)
    retained: list[Sample] = []
    with pytest.raises(AssertionError, match="CLI output differs"):
        compare("collatz", [0], 1, ["bypass"], seed=27, on_sample=retained.append)
    assert len(retained) == 1
    assert retained[0]["value"] == "0"


def test_sample_journal_survives_failure_without_rewriting_the_growing_report(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    from devtools.benchmarks import public_query_comparison as module

    output = tmp_path / "comparison.json"
    monkeypatch.setattr(module, "report_output", lambda *_args: output)
    monkeypatch.setattr(sys, "argv", ["comparison"])
    writes: list[Path] = []
    write_text = Path.write_text

    def record_write(path: Path, text: str) -> int:
        writes.append(path)
        return write_text(path, text)

    def interrupted(
        _family: str,
        _horizons: Sequence[int],
        _trials: int,
        _modes: Sequence[module.Mode],
        *,
        on_sample: Callable[[Sample], None],
        **_options: object,
    ) -> list[Sample]:
        for trial in range(3):
            on_sample(
                Sample(
                    family="collatz",
                    horizon=0,
                    trial=trial,
                    mode="warm",
                    phase="measured",
                    route="cli",
                    output_base=10,
                    seconds=0.0,
                    value="27",
                    info={},
                )
            )
        raise RuntimeError("interrupted comparison")

    monkeypatch.setattr(Path, "write_text", record_write)
    monkeypatch.setattr(module, "compare", interrupted)
    with pytest.raises(RuntimeError, match="interrupted comparison"):
        module.main()
    assert writes == [output, output]
    packet = json.loads(output.read_text())
    journal = [
        json.loads(line)
        for line in (tmp_path / "samples.jsonl").read_text().splitlines()
    ]
    assert journal == packet["rows"]
    assert len(journal) == 3
    assert packet["outcome"] == "failed_or_interrupted"
