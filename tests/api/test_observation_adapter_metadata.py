"""Common observer metadata must preserve family result status."""

from __future__ import annotations

from types import SimpleNamespace
from typing import cast

import pytest

from number_compiler.api.cli_context import QueryContext
from number_compiler.api.observation_adapters import _publish


@pytest.mark.parametrize("status", ("composite", "unknown", "unavailable"))
def test_common_metadata_preserves_observer_status(status: str) -> None:
    request = SimpleNamespace(
        family="fermat",
        presentation=SimpleNamespace(index=SimpleNamespace(encoding="integer")),
        presentation_index=4,
        index=4,
        index_unit="term",
    )
    context = cast(QueryContext, SimpleNamespace(request=request))

    packet = _publish(context, "primality", {"status": status, "decided": False})

    assert packet["status"] == status
    assert packet["kind"] == "primality"
    assert packet["index"] == 4


def test_common_metadata_supplies_available_when_observer_has_no_status() -> None:
    request = SimpleNamespace(
        family="collatz",
        presentation=SimpleNamespace(index=SimpleNamespace(encoding="integer")),
        presentation_index=3,
        index=3,
        index_unit="term",
    )
    context = cast(QueryContext, SimpleNamespace(request=request))

    packet = _publish(context, "accumulator", {"value": 7})

    assert packet["status"] == "available"
