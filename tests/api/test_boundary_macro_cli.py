"""Boundary certificates cannot authorize or demand a complete reverse word."""

import json

import pytest

from number_compiler.api import cli
from number_compiler.api.cli_requests import parse_request
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add import boundary_window
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from number_compiler.sequences.reverse_add.source_workspace import (
    ReverseSourceImageWorkspace,
)
from tests.support.assertions import forbid_explicit_lowering


def test_boundary_cli_uses_only_requested_edges(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    for name in ("width", "digit", "digits", "iter_digits"):
        monkeypatch.setattr(ReverseAddPoweredTerm, name, forbid_explicit_lowering)
    assert (
        cli.main(
            [
                "reverse-add",
                "--seed",
                "10001",
                "--nth",
                "1",
                "--no-value",
                "--info",
                "temporal.macro",
                "--info",
                "metrics",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    assert packet["value"] is None
    boundary = packet["info"]["temporal.macro"]
    assert boundary["status"] == "available"
    assert boundary["target_width"] == 5
    assert boundary["prefix"] == "20"
    assert boundary["suffix"] == "02"
    assert boundary["full_integer_powered"] is False


def test_boundary_cli_refuses_narrow_source_without_false_value(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(
            [
                "reverse-add",
                "--seed",
                "196",
                "--nth",
                "16",
                "--no-value",
                "--info",
                "temporal.macro",
                "--format",
                "json",
            ]
        )
        == 3
    )
    packet = json.loads(capsys.readouterr().out)
    assert packet["value"] is None
    assert packet["info"]["temporal.macro"]["status"] == "unavailable"
    assert packet["info"]["temporal.macro"]["target_width"] is None


def test_boundary_cli_rejects_nondecimal_base() -> None:
    with pytest.raises(ValueError, match="decimal"):
        parse_request(
            [
                "reverse-add",
                "--seed",
                "196",
                "--nth",
                "1",
                "--base",
                "2",
                "--no-value",
                "--info",
                "temporal.macro",
            ]
        )


def test_value_and_boundary_share_admitted_source_carries(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setattr(boundary_window, "digits_lsd", forbid_explicit_lowering)
    for name in ("source_inner_carry", "source_inner_carry_from_validated_digits"):
        monkeypatch.setattr(
            boundary_window.FiniteBoundaryWindow, name, forbid_explicit_lowering
        )
    assert (
        cli.main(
            [
                "reverse-add",
                "--seed",
                "12345",
                "--nth",
                "1",
                "--info",
                "temporal.macro",
                "--info",
                "metrics",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    assert packet["value"] == "66666"
    observation = packet["info"]["temporal.macro"]
    assert observation["status"] == "available"
    assert observation["prefix"] == observation["suffix"] == "66"
    assert observation["target_width"] == 5
    assert observation["full_integer_powered"] is False


@pytest.mark.parametrize("seed,steps", ((12346, 1), (12345, 2)))
def test_boundary_observer_rejects_foreign_request_in_same_ledger(
    seed: int, steps: int
) -> None:
    term = ReverseAddPoweredTerm(12345, 1)
    workspace = ReverseSourceImageWorkspace(term.resource_ledger, seed, steps)
    with pytest.raises(ValueError, match="another request"):
        boundary_window.ReverseBoundaryWindowObserver(
            12345, 1, term.resource_ledger, source_workspace=workspace
        )


def test_boundary_warm_result_rejects_disposed_source_workspace() -> None:
    ledger = ResourceLedger()
    workspace = ReverseSourceImageWorkspace(ledger, 12345, 1)
    observer = boundary_window.ReverseBoundaryWindowObserver(
        12345, 1, ledger, source_workspace=workspace
    )
    workspace.dispose()
    with pytest.raises(ValueError, match="disposed reverse source workspace"):
        observer.observe(seed=12345, generation=1, base=10)


def test_value_then_boundary_decodes_original_source_once() -> None:
    term = ReverseAddPoweredTerm(12345, 1)
    assert term.digits() == (6, 6, 6, 6, 6)
    assert term.observe_boundary_macro().prefix == "66"
    counters = term.resource_ledger.counters
    assert counters["reverse_source_original_digit_decodes"] == 5
    assert counters.get("reverse_boundary_window_source_digit_decodes", 0) == 0
    assert counters.get("reverse_boundary_window_source_inner_scan_reads", 0) == 0
