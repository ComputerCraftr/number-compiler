"""Public reverse queries either return an exact image or refuse explicitly."""

from __future__ import annotations

from typing import Never

import pytest

from number_compiler.api.cli import main
from number_compiler.arithmetic.functions import residual
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.observation.hashlife_projection import HashLifeBlockIndex
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from number_compiler.sequences.reverse_add.source_images import (
    ReverseCylinderConstructionUnavailable,
    _ReverseSourceImageAdapter,
)
from tests.support.reverse_cutover import forbid_uniform_context_compilation


def _forbidden(*_args: object, **_kwargs: object) -> Never:
    raise AssertionError("retired reverse execution path was invoked")


@pytest.fixture(autouse=True)
def forbid_universal_context_compilation(monkeypatch: pytest.MonkeyPatch) -> None:
    """Ensure missing-return refusals do not fall back to the retired executor."""
    forbid_uniform_context_compilation(monkeypatch, _forbidden)
    monkeypatch.setattr(residual, "minimize_bimachine", _forbidden)


@pytest.mark.parametrize("steps,expected", [(0, "196"), (1, "887"), (2, "1675")])
def test_available_cli_terms_use_source_only_scheduler(
    steps: int,
    expected: str,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    monkeypatch.setattr(CausalTileEngine, "__init__", _forbidden)
    monkeypatch.setattr(HashLifeBlockIndex, "__init__", _forbidden)
    assert main(["196", "--nth", str(steps)]) == 0
    captured = capsys.readouterr()
    assert captured.out == expected + "\n"
    assert captured.err == ""
    term = ReverseAddPoweredTerm(196, steps)
    assert term.digits() == tuple(map(int, reversed(expected)))
    assert term._workspace is not None
    assert term._workspace.scheduler._source_only


@pytest.mark.parametrize("steps", [3, 20, 1024, 10**9])
def test_missing_powered_constructor_refuses_without_legacy_work(
    steps: int,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    monkeypatch.setattr(CausalTileEngine, "__init__", _forbidden)
    monkeypatch.setattr(HashLifeBlockIndex, "__init__", _forbidden)
    assert main(["196", "--nth", str(steps)]) == 2
    captured = capsys.readouterr()
    assert captured.out == ""
    assert "cylinder" in captured.err.lower()
    term = ReverseAddPoweredTerm(196, steps)
    for demand in (lambda: term.digit(0), term.width, term.digits):
        with pytest.raises(ReverseCylinderConstructionUnavailable):
            demand()
    assert term._ledger.counters.get("tile_causal_point_parent_requests", 0) == 0
    assert term._ledger.counters.get("whole_word_symbol_visits", 0) == 0
    assert term._ledger.counters.get("sequential_generation_advances", 0) == 0


def test_metrics_leave_missing_constructor_lazy(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(ReverseAddPoweredTerm, "_source_workspace", _forbidden)
    term = ReverseAddPoweredTerm(196, 20)
    assert collect_ledger_metrics(term._ledger).resource_audit_complete == 1
    before = term._ledger.snapshot()
    assert term.metrics().generation == 20
    report = term.behavior_metrics()
    assert report.resource_audit_complete == 1
    assert report.resource_accounting_mismatch == 0
    assert term._ledger.snapshot() == before
    assert term._workspace is None


def test_source_binding_changes_are_rejected() -> None:
    term = ReverseAddPoweredTerm(196, 1)
    assert term.digit(0) == 7
    term.seed = 89
    with pytest.raises(ValueError, match="binding"):
        term.digit(0)


def test_foreign_workspace_cannot_replace_term_binding() -> None:
    term = ReverseAddPoweredTerm(196, 1)
    other = ReverseAddPoweredTerm(89, 1)
    assert term.digit(0) == 7
    assert other.digit(0) == 7
    term._workspace = other._workspace
    with pytest.raises(ValueError, match="binding"):
        term.digit(1)


@pytest.mark.parametrize(
    "seed,steps,expected",
    [(1, 3, "8"), (10, 4, "88"), (11, 3, "88"), (1001, 3, "8008"), (0, 10**26, "0")],
)
def test_admitted_no_growth_cli_powers_do_not_replay_steps(
    seed: int,
    steps: int,
    expected: str,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    monkeypatch.setattr(CausalTileEngine, "__init__", _forbidden)
    monkeypatch.setattr(HashLifeBlockIndex, "__init__", _forbidden)
    for method in (
        "apply_primitive",
        "iter_primitive_digits",
        "iter_second_digits",
        "_carry_and_digit",
    ):
        monkeypatch.setattr(
            _ReverseSourceImageAdapter, method, _forbidden, raising=False
        )
    assert main(["196", "--seed", str(seed), "--nth", str(steps)]) == 0
    captured = capsys.readouterr()
    assert captured.out == expected + "\n"
    assert captured.err == ""


def test_no_growth_power_refuses_at_the_first_unadmitted_growth(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert main(["196", "--seed", "1", "--nth", "4"]) == 2
    captured = capsys.readouterr()
    assert captured.out == ""
    assert "cylinder" in captured.err.lower()
