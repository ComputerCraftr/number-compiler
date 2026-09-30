"""Regenerated evidence stays outside source directories and immutable history."""

from pathlib import Path

import pytest

from devtools import paths


def test_current_reports_use_canonical_module_ownership(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(paths, "repository_root", lambda: tmp_path)
    (tmp_path / "pyproject.toml").write_text('[project]\nversion="0.0.0"\n')
    history = tmp_path / "results" / "historical-root-checkpoints" / "report.md"
    history.parent.mkdir(parents=True)
    history.write_text("original checkpoint")
    output = paths.report_output(
        "devtools.benchmarks.reverse_temporal_power_probe", "report.md"
    )
    output.write_text("new measurement")
    assert output.relative_to(tmp_path).parts[:2] == ("results", "runs")
    assert output.parts[-3:] == (
        "benchmarks",
        "reverse_temporal_power_probe",
        "report.md",
    )
    with pytest.raises(FileExistsError):
        paths.report_output(
            "devtools.benchmarks.reverse_temporal_power_probe", "report.md"
        )
    assert history.read_text() == "original checkpoint"
    assert not (tmp_path / "report.md").exists()


@pytest.mark.parametrize(
    "module, filename",
    [
        ("number_compiler.api", "report.md"),
        ("devtools...", "report.md"),
        ("devtools.checks", "../report.md"),
    ],
)
def test_report_destinations_reject_ambiguous_paths(module: str, filename: str) -> None:
    with pytest.raises(ValueError):
        paths.report_output(module, filename)
