"""Failure injection for retained-store publication regressions."""

from __future__ import annotations

from collections.abc import Callable
from typing import cast

import pytest

from number_compiler.resources.stores import LedgerDict


def inject_write_once_failure(
    monkeypatch: pytest.MonkeyPatch,
    target: object,
    *,
    after_insert: bool,
) -> None:
    """Fail one selected write-once map before or after its insertion."""
    original = cast(
        Callable[[LedgerDict[object, object], object, object], None],
        LedgerDict.__setitem__,
    )

    def fail_selected_store(
        store: LedgerDict[object, object], key: object, value: object
    ) -> None:
        if store is target:
            if after_insert:
                original(store, key, value)
            raise RuntimeError("injected issued-store publication failure")
        original(store, key, value)

    monkeypatch.setattr(LedgerDict, "__setitem__", fail_selected_store)
