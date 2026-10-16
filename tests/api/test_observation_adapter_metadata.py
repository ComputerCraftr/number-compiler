"""Common observer metadata must preserve family result status."""

from __future__ import annotations

from types import SimpleNamespace
from typing import cast

import pytest

from number_compiler.api.cli_context import QueryContext
from number_compiler.api.observation_adapters import _publish
from number_compiler.api.observation_types import (
    OBSERVATION_REGISTRY,
    FamilyId,
    IndexEncoding,
    IndexUnit,
    ObservationId,
)


def test_every_observation_has_a_category_and_matching_contract() -> None:
    assert set(OBSERVATION_REGISTRY) == set(ObservationId)
    assert all(key is spec.identifier for key, spec in OBSERVATION_REGISTRY.items())


@pytest.mark.parametrize("status", ("composite", "unknown", "unavailable"))
def test_common_metadata_preserves_observer_status(status: str) -> None:
    request = SimpleNamespace(
        family=FamilyId.FERMAT,
        presentation=SimpleNamespace(
            index=SimpleNamespace(encoding=IndexEncoding.INTEGER)
        ),
        presentation_index=4,
        index=4,
        index_unit=IndexUnit.FERMAT_INDEX,
    )
    context = cast(QueryContext, SimpleNamespace(request=request))

    packet = _publish(
        context,
        ObservationId.NUMBER_THEORY_PRIMALITY,
        {"status": status, "decided": False},
    )

    assert packet["status"] == status
    assert packet["kind"] == ObservationId.NUMBER_THEORY_PRIMALITY.value
    assert packet["index"] == 4


def test_common_metadata_supplies_available_when_observer_has_no_status() -> None:
    request = SimpleNamespace(
        family=FamilyId.COLLATZ,
        presentation=SimpleNamespace(
            index=SimpleNamespace(encoding=IndexEncoding.INTEGER)
        ),
        presentation_index=3,
        index=3,
        index_unit=IndexUnit.PHYSICAL_ITERATIONS,
    )
    context = cast(QueryContext, SimpleNamespace(request=request))

    packet = _publish(context, ObservationId.TEMPORAL_ACCUMULATOR, {"value": 7})

    assert packet["status"] == "available"
