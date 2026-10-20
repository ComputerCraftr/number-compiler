"""Reusable fault injection for owner-memo disposal contracts."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import cast

import pytest

from number_compiler.resources.ledger import OwnedMemo
from tests.support.private_attributes import private_test_attribute


@dataclass(slots=True)
class OneShotDisposalFailure:
    """Record whether a test reached its targeted disposal failure branch."""

    triggered: bool = False


def fail_owned_memo_dispose_once(
    monkeypatch: pytest.MonkeyPatch,
    matches: Callable[[OwnedMemo[object, object]], bool],
    failure: BaseException,
) -> OneShotDisposalFailure:
    """Inject one targeted `OwnedMemo.dispose` failure, then allow retry."""
    original_dispose = cast(
        Callable[[OwnedMemo[object, object]], None],
        private_test_attribute(OwnedMemo, "dispose"),
    )
    state = OneShotDisposalFailure()

    def fail_once(memo: OwnedMemo[object, object]) -> None:
        if not state.triggered and matches(memo):
            state.triggered = True
            raise failure
        original_dispose(memo)

    monkeypatch.setattr(OwnedMemo, "dispose", fail_once)
    return state


__all__ = ["OneShotDisposalFailure", "fail_owned_memo_dispose_once"]
