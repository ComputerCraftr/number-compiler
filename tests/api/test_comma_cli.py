"""Public comma admission, selector and lazy-reporting contracts."""

from __future__ import annotations

import json
from typing import Never

import pytest

from number_compiler.api.cli import main
from number_compiler.api.cli_requests import parse_request
from number_compiler.api.cli_types import CommaObservationOptions
from number_compiler.api.number_api import NumberCompiler
from number_compiler.api.observation_types import ObservationId
from number_compiler.api.query_types import CommaTermQuery
from number_compiler.arithmetic.contracts.unresolved_term import UnresolvedSequenceTerm
from number_compiler.sequences.comma import future_authority
from number_compiler.sequences.comma.power import CommaTerm


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


def test_unchecked_infinite_prefix_is_never_guessed(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert main(["a367620", "--nth", "412987861", "--format", "json"]) == 3
    captured = capsys.readouterr()
    payload = json.loads(captured.out)
    assert captured.err == ""
    assert payload["value"] is None
    assert payload["index_unit"] == "oeis_index"
    assert payload["error"]["code"] == "unresolved_sequence_boundary"
    assert payload["error"]["requested_index"] == 412987861


def test_certificate_and_metrics_do_not_compute_finite_orbit(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    from number_compiler.sequences.comma import certificates

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("certificate/reporting unexpectedly evaluated a term")

    monkeypatch.setattr(CommaTerm, "_resolve", forbidden)
    monkeypatch.setattr(certificates, "_verify", forbidden)
    monkeypatch.setattr(certificates, "files", forbidden)
    monkeypatch.setattr(certificates, "sha256", forbidden)
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
                "--info",
                "safety.certificate",
                "--format",
                "json",
            ]
        )
        == 0
    )
    payload = json.loads(capsys.readouterr().out)
    assert payload["value"] is None
    for name, packet in payload["info"].items():
        assert packet["kind"] == name
        assert packet["family"] == "a367620"
        assert packet["index"] == 20000
        assert packet["index_unit"] == "oeis_index"
    metrics = payload["info"]["metrics"]
    assert metrics["width"] is None
    assert metrics["execution_metrics"]["schema_version"] == 8
    assert metrics["execution_metrics"]["reporting"]["inspected_inventory_rows"] == 0
    assert payload["info"]["safety.certificate"]["runtime_verified"] is False
    assert payload["info"]["safety.certificate"]["isabelle_instance_checked"] is False


def test_registered_global_certificate_admits_snapshot_without_loading_provider(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    from number_compiler.sequences.comma import certificates

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("snapshot loaded a provider or computed a term")

    digest = "b" * 64
    monkeypatch.setattr(
        certificates, "_registered_global_release_digest", lambda: digest
    )
    monkeypatch.setattr(certificates, "_verify", forbidden)
    monkeypatch.setattr(certificates, "files", forbidden)
    monkeypatch.setattr(certificates, "sha256", forbidden)
    monkeypatch.setattr(CommaTerm, "_resolve", forbidden)

    assert (
        main(
            [
                "a367620",
                "--nth",
                str(certificates.CERTIFIED_MAX_INDEX + 1),
                "--no-value",
                "--info",
                "safety.certificate",
                "--format",
                "json",
            ]
        )
        == 0
    )
    payload = json.loads(capsys.readouterr().out)
    packet = payload["info"]["safety.certificate"]
    assert payload["value"] is None
    assert packet["status"] == "available"
    assert packet["certificate_sha256"] == digest
    assert packet["certified_max_index"] is None
    assert packet["runtime_verified"] is False
    assert packet["isabelle_instance_checked"] is True
    assert packet["coverage"] == "all_positive_indices"


def test_public_api_requires_prefix_evidence_on_every_value_demand() -> None:
    compiler = NumberCompiler()
    assert compiler.project(CommaTermQuery(1)).materialize(max_bits=64) == 20
    assert compiler.nth(CommaTermQuery(1)) == 20
    term = compiler.project(CommaTermQuery(412987861))
    with pytest.raises(UnresolvedSequenceTerm):
        term.materialize(max_bits=64)
    with pytest.raises(UnresolvedSequenceTerm):
        term.digit(0)


@pytest.mark.validation
@pytest.mark.parametrize(
    ("index", "expected"),
    [
        (1, "20"),
        (20000, "1039404"),
        (412987859, "19999999918"),
        (412987860, "19999999999"),
    ],
)
def test_release_checked_prefix_emits_exact_value(
    index: int, expected: str, capsys: pytest.CaptureFixture[str]
) -> None:
    """Positive release gate: refusal is not completion of certified-prefix rollout."""
    assert main(["a367620", "--nth", str(index)]) == 0
    assert capsys.readouterr().out.strip() == expected


def test_metrics_only_remains_visible_at_unresolved_boundary(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("metrics evaluated the comma trajectory")

    monkeypatch.setattr(CommaTerm, "_resolve", forbidden)
    assert (
        main(
            [
                "a367620",
                "--nth",
                "412987861",
                "--no-value",
                "--info",
                "metrics",
                "--format",
                "json",
            ]
        )
        == 3
    )
    payload = json.loads(capsys.readouterr().out)
    assert set(payload["info"]) == {"metrics"}
    assert payload["error"]["code"] == "unresolved_sequence_boundary"
    assert payload["value"] is None


def test_metrics_only_does_not_verify_or_construct(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    from number_compiler.sequences.comma import certificates

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("metrics initiated certificate or arithmetic work")

    monkeypatch.setattr(certificates, "_verify", forbidden)
    monkeypatch.setattr(CommaTerm, "_resolve", forbidden)
    assert (
        main(
            [
                "a367620",
                "--nth",
                "20000",
                "--no-value",
                "--info",
                "metrics",
                "--format",
                "json",
            ]
        )
        == 0
    )
    payload = json.loads(capsys.readouterr().out)
    assert payload["value"] is None
    assert "error" not in payload


def test_certificate_versions_cannot_reuse_an_api_term(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.comma import certificates

    compiler = NumberCompiler()
    before = compiler.project(CommaTermQuery(20))
    monkeypatch.setattr(certificates, "CERTIFICATE_ID", "adversarial-new-version")
    after = compiler.project(CommaTermQuery(20))
    assert before.payload is not after.payload
    with pytest.raises(UnresolvedSequenceTerm, match="stale"):
        before.materialize(max_bits=100)


def test_forged_shared_certificate_marker_cannot_authorize_digits() -> None:
    from number_compiler.resources.process_cache import get_process_cache
    from number_compiler.sequences.comma import certificates as c

    cache = get_process_cache()
    cache.reset()
    with cache.acquire(
        "comma-prefix-certificate", c.CERTIFICATE_ID, (20, 10, c.CERTIFICATE_SHA256)
    ) as lease:
        lease.put(
            (
                c.CERTIFIED_MAX_INDEX,
                future_authority.SOURCE20_FIRST_FORK_INDEX,
                future_authority.SOURCE20_FIRST_FORK_VALUE,
            ),
            (c.CERTIFICATE_SHA256, "forged"),
        )
    try:
        with pytest.raises(ValueError, match="foreign comma certificate cache"):
            NumberCompiler().project(CommaTermQuery(1)).materialize(max_bits=64)
    finally:
        cache.reset()


def test_bypassed_public_query_verifies_once_and_reuses_its_own_admission() -> None:
    term = NumberCompiler(shared_cache=False).project(CommaTermQuery(1))
    assert term.materialize(max_bits=64) == 20
    assert term.materialize(max_bits=64) == 20
    from number_compiler.api.comma_term import CommaTermPayload

    assert isinstance(term.payload, CommaTermPayload)
    counters = term.payload.term.ledger.counters
    assert counters["comma_certificate_cache_bypasses"] == 1
    assert counters["comma_certificate_local_hits"] == 1
    assert counters["comma_certificate_work"] < 1_000_000
