"""Query-scoped action ownership stays lazy, authenticated and retryable."""

from __future__ import annotations

import pytest

from number_compiler.api.cli import main
from number_compiler.api.cli_context import QueryContext
from number_compiler.api.cli_requests import parse_request
from number_compiler.api.number_api import NumberCompiler, PoweredCollatzTermPayload
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.parity_carry_tape_actions import (
    LedgeredParityTapeActions,
)


def _context() -> QueryContext:
    request = parse_request(["collatz", "--seed", "27", "--nth", "0"])
    assert request is not None
    return QueryContext(request, NumberCompiler())


def test_closing_unused_context_does_not_construct_a_source(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("closing an unused query constructed a source")

    monkeypatch.setattr(NumberCompiler, "project", forbidden)
    context = _context()
    context.close()
    context.close()
    with pytest.raises(RuntimeError, match="closed"):
        context.information()


def test_query_action_owner_authenticates_ledger_and_retries_cleanup(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    context = _context()
    payload = context.raw_projected_term().payload
    assert isinstance(payload, PoweredCollatzTermPayload)
    ledger = payload.term.resource_ledger
    with pytest.raises(ValueError, match="selected Collatz"):
        context.collatz_parity_actions(ResourceLedger())
    actions = context.collatz_parity_actions(ledger)
    assert context.collatz_parity_actions(ledger) is actions
    dispose = LedgeredParityTapeActions.dispose
    attempts = 0

    def fail_once(self: LedgeredParityTapeActions) -> None:
        nonlocal attempts
        attempts += 1
        if attempts == 1:
            raise RuntimeError("injected owner cleanup failure")
        dispose(self)

    monkeypatch.setattr(LedgeredParityTapeActions, "dispose", fail_once)
    with pytest.raises(RuntimeError, match="injected"):
        context.close()
    with pytest.raises(RuntimeError, match="closed"):
        context.collatz_parity_actions(ledger)
    context.close()
    context.close()
    assert attempts == 2


def test_cli_closes_query_when_demanded_observation_fails(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    closed: list[QueryContext] = []
    original = QueryContext.close

    def close(self: QueryContext) -> None:
        closed.append(self)
        original(self)

    def fail(self: QueryContext) -> dict[str, dict[str, object]]:
        raise ValueError("injected observation failure")

    monkeypatch.setattr(QueryContext, "close", close)
    monkeypatch.setattr(QueryContext, "information", fail)
    assert main(["collatz", "--seed", "27", "--nth", "0", "--info", "temporal"]) == 2
    assert "injected observation failure" in capsys.readouterr().err
    assert len(closed) == 1
