"""Public comma admission, selector and lazy-reporting contracts."""

from __future__ import annotations

import json
from collections.abc import Callable
from hashlib import sha256
from importlib.resources import as_file, files
from types import MappingProxyType
from typing import Never

import pytest

from number_compiler.api.cli import main
from number_compiler.api.cli_requests import parse_request
from number_compiler.api.cli_types import CommaObservationOptions
from number_compiler.api.comma_term import CommaTermPayload
from number_compiler.api.number_api import NumberCompiler, ProjectedNumberTerm
from number_compiler.api.observation_types import ObservationId
from number_compiler.api.query_types import CommaTermQuery
from number_compiler.arithmetic.contracts.unresolved_term import UnresolvedSequenceTerm
from number_compiler.sequences.comma.power import CommaTerm


def _force_empty_global_registry(monkeypatch: pytest.MonkeyPatch) -> None:
    from number_compiler.sequences.comma import future_provider

    monkeypatch.setattr(
        future_provider, "_ADMITTED_KERNEL_INSTANCES", MappingProxyType[str, object]({})
    )
    monkeypatch.setattr(
        future_provider, "registered_global_release_artifact_sha256", lambda: None
    )


@pytest.mark.parametrize(
    "extra",
    [
        ["--seed", "20"],
        ["--base", "10"],
        ["--radix", "2"],
        ["--start", "2"],
        ["--events", "1"],
        ["--max-comma-states", "0"],
        ["--max-comma-work", "0"],
        ["--info", "arithmetic.hensel"],
    ],
)
def test_comma_rejects_irrelevant_or_invalid_flags(extra: list[str]) -> None:
    if extra[0].startswith("--max-comma-"):
        assert main(["a367620", "--nth", "1", *extra]) == 2
    else:
        with pytest.raises(SystemExit) as error:
            main(["a367620", "--nth", "1", *extra])
        assert error.value.code == 2


def test_comma_preserves_oeis_index_and_deduplicates_information() -> None:
    request = parse_request(
        [
            "a367620",
            "--nth",
            "20000",
            "--info",
            "temporal.clock",
            "--info",
            "temporal.clock",
        ]
    )
    assert request is not None
    assert isinstance(request.execution, CommaTermQuery)
    assert request.index_unit == "oeis_index"
    assert request.observations == CommaObservationOptions(
        info=(ObservationId.TEMPORAL_CLOCK,)
    )
    assert request.execution.max_comma_states == 131072
    assert request.execution.max_comma_work == 1000000
    assert main(["a367620", "--nth", "0"]) == 2


@pytest.mark.parametrize("index", [1, 412987859, 412987861])
def test_empty_registry_refuses_every_public_value(
    index: int,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    _force_empty_global_registry(monkeypatch)
    assert main(["a367620", "--nth", str(index), "--format", "json"]) == 3
    payload = json.loads(capsys.readouterr().out)
    assert payload["value"] is None
    assert payload["index_unit"] == "oeis_index"
    assert payload["error"]["code"] == "unresolved_sequence_boundary"
    assert payload["error"]["requested_index"] == index
    assert payload["error"]["certified_max_index"] == 0


def test_empty_registry_status_and_metrics_are_lazy(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    from number_compiler.sequences.comma import certificates

    _force_empty_global_registry(monkeypatch)

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("status or metrics resolved a comma value")

    monkeypatch.setattr(CommaTerm, "resolve_index", forbidden)
    monkeypatch.setattr(certificates, "_registered_global_release_digest", lambda: None)
    assert (
        main(
            [
                "a367620",
                "--nth",
                "20000",
                "--no-value",
                "--info",
                "metrics",
                "--info",
                "safety.certificate",
                "--format",
                "json",
            ]
        )
        == 3
    )
    payload = json.loads(capsys.readouterr().out)
    assert payload["value"] is None
    assert payload["error"]["requested_index"] == 20000
    assert set(payload["info"]) == {"metrics", "safety.certificate"}
    assert payload["info"]["metrics"]["width"] is None
    assert payload["info"]["metrics"]["execution_metrics"]["schema_version"] == 8
    assert payload["info"]["safety.certificate"]["status"] == "unknown"
    assert payload["info"]["safety.certificate"]["coverage"] == "none"


def test_public_python_api_requires_global_authority_at_every_index(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _force_empty_global_registry(monkeypatch)
    compiler = NumberCompiler()
    projected_terms: list[ProjectedNumberTerm] = []
    try:
        for index in (1, 412987861):
            term = compiler.project(CommaTermQuery(index))
            projected_terms.append(term)
            with pytest.raises(UnresolvedSequenceTerm):
                term.materialize(max_bits=64)
            with pytest.raises(UnresolvedSequenceTerm):
                term.digit(0)
    finally:
        for term in projected_terms:
            if isinstance(term.payload, CommaTermPayload):
                term.payload.term.close()
        compiler.clear_powered_cache()


@pytest.mark.parametrize(
    ("index", "expected"),
    [
        (1, "20"),
        (20000, "1039404"),
        (412987859, "19999999918"),
        (412987860, "19999999999"),
    ],
)
def test_global_admission_emits_exact_public_value(
    index: int,
    expected: str,
    capsys: pytest.CaptureFixture[str],
) -> None:
    """Keep the established public positive output gate in default units."""
    assert main(["a367620", "--nth", str(index)]) == 0
    assert capsys.readouterr().out.strip() == expected


@pytest.mark.validation
def test_packaged_default_global_authority_is_exact_and_emits_fork_endpoints(
    capsys: pytest.CaptureFixture[str],
    request: pytest.FixtureRequest,
) -> None:
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.comma import future_provider

    digest = future_provider.registered_global_release_artifact_sha256()
    assert digest is not None
    asset = files("number_compiler").joinpath(
        "kernels", future_provider.FUTURE_PROVIDER_ASSET
    )
    assert sha256(asset.read_bytes()).hexdigest() == digest
    store = future_provider.SemanticFutureProviderStore(ResourceLedger())
    request.addfinalizer(store.close)
    with as_file(asset) as path:
        provider = store.load_file(path, charge_work=lambda _amount: None)
    provider.require_global_release_admission()
    assert provider.artifact_sha256 == digest

    expected = (
        (1, "20"),
        (20000, "1039404"),
        (412987859, "19999999918"),
        (412987860, "19999999999"),
    )
    from number_compiler.sequences.comma.arithmetic import comma_children

    assert comma_children(19999999918) == (19999999999, 20000000000)
    for index, value in expected:
        assert main(["a367620", "--nth", str(index)]) == 0
        assert capsys.readouterr().out.strip() == value


@pytest.mark.validation
def test_default_global_cli_selects_two_later_source_bound_forks(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    request: pytest.FixtureRequest,
) -> None:
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.comma import future_provider
    from number_compiler.sequences.comma.boundary_quotient import (
        BoundaryState,
        construct_macro,
    )
    from number_compiler.sequences.comma.future_authority import (
        SOURCE20_SELECTED_CHILD_INDEX,
    )
    from number_compiler.sequences.comma.occurrence import (
        BoundaryOccurrence,
        OccurrencePrefixReturn,
    )
    from number_compiler.sequences.comma.semantic_branch import (
        select_global_semantic_macro_child,
    )

    digest = future_provider.registered_global_release_artifact_sha256()
    assert digest is not None
    asset = files("number_compiler").joinpath(
        "kernels", future_provider.FUTURE_PROVIDER_ASSET
    )
    store = future_provider.SemanticFutureProviderStore(ResourceLedger())
    request.addfinalizer(store.close)
    with as_file(asset) as path:
        provider = store.load_file(path, charge_work=lambda _amount: None)
    assert provider.artifact_sha256 == digest
    source = BoundaryOccurrence(BoundaryState("N", 2, 10), 10)
    expected_states = (BoundaryState("N", 2, 10), BoundaryState("N", 7, 12))
    transition_counts: list[int] = []
    for expected_state in expected_states:
        assert source.state == expected_state
        prefix = OccurrencePrefixReturn(source, construct_macro(source.state))
        assert prefix.outcome == "fork"
        ordered = prefix.ordered_literal_children()
        _, literals = ordered.validated_parts()
        assert len(literals) == 2
        selected = select_global_semantic_macro_child(
            source,
            prefix,
            fork_value=prefix.terminal_value,
            ordered_literal_children=(literals[0], literals[1]),
            provider=provider,
            charge_work=lambda _amount: None,
        )
        assert selected.literal_value == literals[selected.selection.selected_slot]
        transition_counts.append(selected.total_transition_count)
        source = selected.target

    target_index = SOURCE20_SELECTED_CHILD_INDEX + sum(transition_counts)
    original_select = (
        future_provider.SemanticFutureProvider.select_unique_unranked_child
    )
    cli_sources: list[BoundaryState] = []

    def trace_select(
        self: future_provider.SemanticFutureProvider,
        state: BoundaryState,
        *,
        charge_work: Callable[[int], None],
    ) -> future_provider.UnrankedChildSelection:
        cli_sources.append(state)
        return original_select(self, state, charge_work=charge_work)

    monkeypatch.setattr(
        future_provider.SemanticFutureProvider,
        "select_unique_unranked_child",
        trace_select,
    )
    assert main(["a367620", "--nth", str(target_index), "--format", "json"]) == 0
    packet = json.loads(capsys.readouterr().out)
    assert packet["index"] == target_index
    assert packet["value"] == str(source.value())
    assert BoundaryState("N", 2, 10) in cli_sources
    assert BoundaryState("N", 7, 12) in cli_sources
