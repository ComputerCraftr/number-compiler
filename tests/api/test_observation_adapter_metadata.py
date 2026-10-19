"""Common observer metadata must preserve family result status."""

from __future__ import annotations

from types import SimpleNamespace

import pytest

from number_compiler.api import registry_adapters
from number_compiler.api.cli_context import QueryContext
from number_compiler.api.cli_types import QueryRequest
from number_compiler.api.number_api import NumberCompiler
from number_compiler.api.observation_adapters import publish_observation
from number_compiler.api.observation_types import (
    OBSERVATION_REGISTRY,
    ObservationId,
)
from number_compiler.api.query_types import CollatzTermQuery, FermatTermQuery
from number_compiler.arithmetic.contracts.family_identity import FamilyId


def test_every_observation_has_a_category_and_matching_contract() -> None:
    assert set(OBSERVATION_REGISTRY) == set(ObservationId)
    assert all(key is spec.identifier for key, spec in OBSERVATION_REGISTRY.items())


@pytest.mark.parametrize("status", ("composite", "unknown", "unavailable"))
def test_common_metadata_preserves_observer_status(status: str) -> None:
    request = QueryRequest(FermatTermQuery(4))
    context = QueryContext(request, NumberCompiler())

    packet = publish_observation(
        context,
        ObservationId.NUMBER_THEORY_PRIMALITY,
        {"status": status, "decided": False},
    )

    assert packet["status"] == status
    assert packet["kind"] == ObservationId.NUMBER_THEORY_PRIMALITY.value
    assert packet["index"] == 4


def test_common_metadata_supplies_available_when_observer_has_no_status() -> None:
    request = QueryRequest(CollatzTermQuery(3, seed=27))
    context = QueryContext(request, NumberCompiler())

    packet = publish_observation(
        context, ObservationId.TEMPORAL_ACCUMULATOR, {"value": 7}
    )

    assert packet["status"] == "available"


def test_lazy_adapter_resolution_rejects_wrong_callable_shapes(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    malformed = SimpleNamespace(
        prepare_noop=lambda: None,
        admit_noop=lambda: None,
        observe_noop=lambda: None,
    )

    def malformed_module(_name: str) -> SimpleNamespace:
        return malformed

    monkeypatch.setattr(registry_adapters, "import_module", malformed_module)

    with pytest.raises(TypeError, match="prepare adapter"):
        registry_adapters.resolve_observation_adapter(FamilyId.PRIME)
