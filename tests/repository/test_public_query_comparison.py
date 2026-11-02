"""Public comparison evidence retains every route and never conceals disagreement."""

import json
import sys
from collections.abc import Callable, Sequence
from pathlib import Path

import pytest

from devtools.benchmarks.public_query_comparison import Sample, compare
from number_compiler.api.number_api import NumberCompiler


def test_scalar_comparison_keeps_start_and_does_not_invent_point_support() -> None:
    rows = compare("prime", [0], 1, ["bypass"], start=100, bases=(10,), info=())
    assert len(rows) == 1
    assert rows[0]["route"] == "cli"
    assert rows[0]["value"] == "101"
    assert rows[0]["info"] == {}
    with pytest.raises(ValueError, match="source parameter"):
        compare("collatz", [0], 1, ["bypass"], start=100)


def test_registry_observation_options_reach_cli_without_selector_overrides() -> None:
    rows = compare(
        "reverse-add",
        [2],
        1,
        ["bypass"],
        seed=196,
        info=("temporal.matrix",),
        no_value=True,
        observation_options=(
            ("temporal_matrix_kind", "innovation"),
            ("temporal_matrix_modulus", "7"),
        ),
    )
    assert len(rows) == 1
    assert rows[0]["value"] is None
    clock_rows = compare(
        "collatz",
        [2],
        1,
        ["bypass"],
        seed=27,
        info=("temporal.clock",),
        no_value=True,
        observation_options=(("clock_max_digits", "64"),),
    )
    assert clock_rows[0]["value"] is None
    with pytest.raises(ValueError, match="not declared"):
        compare(
            "reverse-add", [2], 1, ["bypass"], observation_options=(("nth", "200"),)
        )
    with pytest.raises(ValueError, match="unique"):
        compare(
            "reverse-add",
            [2],
            1,
            ["bypass"],
            observation_options=(
                ("temporal_matrix_modulus", "7"),
                ("temporal_matrix_modulus", "198"),
            ),
        )


@pytest.mark.parametrize(
    "horizons",
    [
        pytest.param((2,), id="unit"),
        pytest.param((0, 2), marks=pytest.mark.validation, id="full"),
    ],
)
def test_public_routes_agree_and_warm_priming_is_retained(
    horizons: tuple[int, ...],
) -> None:
    rows = compare("collatz", list(horizons), 1, ["cold", "warm", "bypass"], seed=27)
    assert len(rows) == 12 * len(horizons)
    assert sum(row["phase"] == "priming" for row in rows) == 3 * len(horizons)
    assert {row["route"] for row in rows} == {"cli", "point"}
    for row in rows:
        expected = 27 if row["horizon"] == 0 else 41
        if row["route"] == "cli":
            value = row["value"]
            assert value is not None
            assert int(value, row["output_base"]) == expected
        else:
            value = row["value"]
            assert value is not None
            assert int(value) == (expected >> 2) & 1


def test_mismatched_cli_sample_is_retained_before_rejection(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from devtools.benchmarks import public_query_comparison as module

    def wrong(
        arguments: list[str], *, fresh: bool, shared_cache: bool = True
    ) -> tuple[float, dict[str, object]]:
        return 0.01, {"value": "0", "info": {"metrics": None}}

    monkeypatch.setattr(module, "cli_sample", wrong)
    retained: list[Sample] = []
    with pytest.raises(AssertionError, match="CLI output differs"):
        compare("collatz", [0], 1, ["bypass"], seed=27, on_sample=retained.append)
    assert len(retained) == 1
    assert retained[0]["value"] == "0"


def test_info_only_comparison_skips_value_reference_and_point_demand(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from devtools.benchmarks import public_query_comparison as module

    def forbidden_project(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("info-only comparison constructed a value reference")

    calls: list[list[str]] = []

    def observe(
        arguments: list[str], *, fresh: bool, shared_cache: bool = True
    ) -> tuple[float, dict[str, object]]:
        calls.append(arguments)
        assert "--no-value" in arguments
        return 0.01, {
            "value": None,
            "info": {"arithmetic.mahler": {"status": "available"}},
        }

    monkeypatch.setattr(NumberCompiler, "project", forbidden_project)
    monkeypatch.setattr(module, "cli_sample", observe)
    rows = compare(
        "antihydra",
        [16],
        1,
        ["bypass"],
        info=("arithmetic.mahler",),
        no_value=True,
    )
    assert len(rows) == 1
    assert rows[0]["route"] == "cli"
    assert rows[0]["value"] is None
    assert len(calls) == 1


def test_mismatched_observation_sample_is_retained_before_rejection(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from devtools.benchmarks import public_query_comparison as module

    calls = 0

    def changing(
        _arguments: list[str], *, fresh: bool, shared_cache: bool = True
    ) -> tuple[float, dict[str, object]]:
        nonlocal calls
        calls += 1
        return 0.01, {
            "value": None,
            "info": {
                "arithmetic.mahler": {"revision": calls},
                "metrics": None,
            },
        }

    monkeypatch.setattr(module, "cli_sample", changing)
    retained: list[Sample] = []
    with pytest.raises(AssertionError, match="observation changed"):
        compare(
            "antihydra",
            [0],
            1,
            ["bypass", "warm"],
            info=("arithmetic.mahler", "metrics"),
            no_value=True,
            on_sample=retained.append,
        )
    assert len(retained) == 2
    assert retained[-1]["info"] == {
        "arithmetic.mahler": {"revision": 2},
        "metrics": None,
    }


def test_sample_journal_survives_failure_without_rewriting_the_growing_report(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    from devtools.benchmarks import public_query_comparison as module

    output = tmp_path / "comparison.json"

    def report_output(_module: str, _filename: str) -> Path:
        return output

    monkeypatch.setattr(module, "report_output", report_output)
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
