"""Public reverse queries either return an exact image or refuse explicitly."""

from __future__ import annotations

import json
from typing import Never

import pytest

from number_compiler.api import cli
from number_compiler.api.cli import main
from number_compiler.api.number_api import NumberCompiler
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.functions import residual
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.observation.hashlife_projection import HashLifeBlockIndex
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from number_compiler.sequences.reverse_add.source_images import (
    _ReverseSourceImageAdapter,
)
from tests.support.reverse_cutover import (
    assert_completed_child_work,
    assert_q19_output_authority,
    forbid_uniform_context_compilation,
)


def _forbidden(*_args: object, **_kwargs: object) -> Never:
    raise AssertionError("retired reverse execution path was invoked")


@pytest.fixture(autouse=True)
def forbid_universal_context_compilation(monkeypatch: pytest.MonkeyPatch) -> None:
    """Ensure missing-return refusals do not fall back to the retired executor."""
    forbid_uniform_context_compilation(monkeypatch, _forbidden)
    monkeypatch.setattr(residual, "minimize_bimachine", _forbidden)


def _checked_cli_term(
    steps: int,
    expected: str,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> ReverseAddPoweredTerm:
    monkeypatch.setattr(CausalTileEngine, "__init__", _forbidden)
    monkeypatch.setattr(HashLifeBlockIndex, "__init__", _forbidden)
    assert main(["reverse-add", "--seed", "196", "--nth", str(steps)]) == 0
    captured = capsys.readouterr()
    assert captured.out == expected + "\n"
    assert captured.err == ""
    term = ReverseAddPoweredTerm(196, steps)
    assert term.digits() == tuple(map(int, reversed(expected)))
    return term


@pytest.mark.parametrize("steps,expected", [(0, "196"), (1, "887"), (2, "1675")])
def test_available_cli_terms_use_source_only_scheduler(
    steps: int,
    expected: str,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    term = _checked_cli_term(steps, expected, monkeypatch, capsys)
    assert term._workspace is not None
    assert term._workspace.scheduler._source_only


@pytest.mark.parametrize(
    ("steps", "expected"),
    [(3, "7436"), (20, "70446464506")],
)
def test_completed_child_constructor_answers_rejected_same_carry_without_legacy_work(
    steps: int,
    expected: str,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    term = _checked_cli_term(steps, expected, monkeypatch, capsys)
    counters = term._ledger.counters
    assert_completed_child_work(counters)
    assert_q19_output_authority(term)
    assert counters.get("tile_causal_point_parent_requests", 0) == 0
    assert counters.get("whole_word_symbol_visits", 0) == 0
    assert counters.get("sequential_generation_advances", 0) == 0


def test_large_exact_output_replaces_the_retired_architectural_refusal(
    capsys: pytest.CaptureFixture[str],
) -> None:
    from tests.support.reference_arithmetic import literal_reverse_add_digits

    expected = literal_reverse_add_digits(196, 1024)
    assert main(["reverse-add", "--seed", "196", "--nth", "1024"]) == 0
    captured = capsys.readouterr()
    assert captured.out == "".join(map(str, reversed(expected))) + "\n"
    assert captured.err == ""


@pytest.mark.parametrize("steps", [1024, 10**9])
def test_large_power_respects_explicit_cache_budget_before_primitive_descent(
    steps: int,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    monkeypatch.setattr(CausalTileEngine, "__init__", _forbidden)
    monkeypatch.setattr(HashLifeBlockIndex, "__init__", _forbidden)
    compiler = NumberCompiler(max_context_nodes=512, max_cache_entries=512)
    monkeypatch.setattr(cli, "NumberCompiler", lambda: compiler)
    assert main(["reverse-add", "--seed", "196", "--nth", str(steps)]) == 2
    captured = capsys.readouterr()
    assert captured.out == ""
    assert "budget" in captured.err.lower()
    for point in (False, True):
        term = ReverseAddPoweredTerm(196, steps, max_cache_entries=512)
        with pytest.raises(BlockContextBudgetExceeded):
            if point:
                term.digit(0)
            else:
                term.digits()
        assert term._ledger.counters.get("source_image_primitive_applications", 0) == 0
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


def test_cli_mirror_and_value_share_completed_output_without_width_replay(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    from number_compiler.arithmetic.carry import carry_itinerary, event_memory

    monkeypatch.setattr(event_memory, "_pair_step_with_carry", _forbidden)
    monkeypatch.setattr(
        carry_itinerary, "reconstruct_pair_from_live_event_suffix", _forbidden
    )
    assert (
        main(
            [
                "reverse-add",
                "--seed",
                "196",
                "--nth",
                "20",
                "--info",
                "spatial.mirror",
                "--format",
                "json",
            ]
        )
        == 0
    )
    captured = capsys.readouterr()
    assert captured.err == ""
    packet = json.loads(captured.out)
    assert packet["value"] == "70446464506"
    assert packet["info"]["spatial.mirror"]["palindrome"] is False


def test_cli_metrics_only_does_not_construct_guarded_temporal_banks(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    monkeypatch.setattr(ReverseAddPoweredTerm, "_source_workspace", _forbidden)
    assert (
        main(
            [
                "reverse-add",
                "--seed",
                "196",
                "--nth-power10",
                "3",
                "--info",
                "metrics",
                "--no-value",
                "--format",
                "json",
            ]
        )
        == 0
    )
    captured = capsys.readouterr()
    assert captured.err == ""
    packet = json.loads(captured.out)
    assert packet["value"] is None
    assert packet["index"] == {"encoding": "power10", "exponent": 3}


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
    assert main(["reverse-add", "--seed", str(seed), "--nth", str(steps)]) == 0
    captured = capsys.readouterr()
    assert captured.out == expected + "\n"
    assert captured.err == ""


def test_first_unadmitted_growth_uses_completed_child_constructor(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert main(["reverse-add", "--seed", "1", "--nth", "4"]) == 0
    captured = capsys.readouterr()
    assert captured.out == "16\n"
    assert captured.err == ""
    term = ReverseAddPoweredTerm(1, 4)
    assert term.digits() == (6, 1)
    counters = term._ledger.counters
    assert_completed_child_work(counters)


def test_mutated_seed_rejects_before_recursive_authority_or_workspace_allocation() -> (
    None
):
    term = ReverseAddPoweredTerm(196, 20)
    term.seed = 295
    before = term._ledger.snapshot()
    with pytest.raises(ValueError, match="binding changed"):
        term.digit(0)
    assert term._source_construction is None
    assert term._workspace is None
    assert term._ledger.snapshot() == before
