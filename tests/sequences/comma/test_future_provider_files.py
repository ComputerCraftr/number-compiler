"""File admission and byte-accounting contracts for FutureCID artifacts."""

from __future__ import annotations

import base64
import json
import os
from collections.abc import Callable, Mapping
from pathlib import Path
from types import SimpleNamespace
from typing import Protocol, cast

import pytest

from devtools.paths import isabelle_root
from devtools.verification.comma_semantic_future_artifact import (
    runtime_candidate_record_from_isabelle_data,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.comma import future_provider
from number_compiler.sequences.comma.boundary_quotient import BoundaryState
from tests.support.comma_future_provider_fixture import (
    candidate_record,
    canonical_bytes,
    install_synthetic_registry,
    work_log,
)


class _PreflightParser(Protocol):
    def __call__(
        self,
        candidate: Mapping[str, object],
        *,
        charge_work: Callable[[int], None],
        artifact_sha256: str | None = None,
    ) -> future_provider.ParsedFutureCandidate: ...


def test_file_loader_preflights_nested_metadata_before_canonical_dump(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = candidate_record()
    nested: object = None
    for _ in range(future_provider.MAX_CANDIDATE_JSON_DEPTH + 1):
        nested = [nested]
    record["unexpected_metadata"] = {"nested": nested}
    payload = canonical_bytes(record)
    candidate_path = tmp_path / "deep-future-candidate.json"
    candidate_path.write_bytes(payload)
    charges, charge_work = work_log()

    def reject_canonical_dump(_record: Mapping[str, object]) -> bytes:
        raise AssertionError("deep metadata reached canonical serialization")

    monkeypatch.setattr(future_provider, "_canonical_json_bytes", reject_canonical_dump)
    with pytest.raises(ValueError, match="nesting exceeds its bound"):
        future_provider.SemanticFutureProvider.load_file(
            candidate_path, charge_work=charge_work
        )
    assert sum(charges) >= (len(payload) + 65_535) // 65_536


def test_file_loader_requires_canonical_bytes_and_registry_admission(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = candidate_record()
    _charges, charge_work = work_log()
    install_synthetic_registry(monkeypatch, record, charge_work)
    candidate_path = tmp_path / "future.json"
    candidate_path.write_bytes(canonical_bytes(record))
    provider = future_provider.SemanticFutureProvider.load_file(
        candidate_path, charge_work=charge_work
    )
    assert provider.class_count == 3

    candidate_path.write_text(json.dumps(record), encoding="utf-8")
    with pytest.raises(ValueError, match="canonical form"):
        future_provider.SemanticFutureProvider.load_file(
            candidate_path, charge_work=charge_work
        )


def test_file_loader_charges_bytes_read_when_stat_underreports(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class_count = 2_048
    encoded_classes = bytearray()
    for source_index in range(future_provider.SOURCE_COUNT):
        value = min(source_index, class_count - 1)
        while value >= 0x80:
            encoded_classes.append((value & 0x7F) | 0x80)
            value >>= 7
        encoded_classes.append(value)
    record = {
        "format": future_provider.FUTURE_CANDIDATE_FORMAT,
        "authority": future_provider.FUTURE_CANDIDATE_AUTHORITY,
        "state_universe": future_provider.FUTURE_SOURCE_UNIVERSE,
        "class_of_state_varint_base64": base64.b64encode(encoded_classes).decode(
            "ascii"
        ),
        "controls": [["landmine", None] for _ in range(class_count)],
        "ordered_children": [[None, None] for _ in range(class_count)],
        "class_rank_candidate": [0] * class_count,
    }
    _charges, setup_charge = work_log()
    # The submitted large payload is well-formed but has no matching admission.
    install_synthetic_registry(monkeypatch, candidate_record(), setup_charge)
    _charges, charge_work = work_log()

    payload = canonical_bytes(record)
    assert len(payload) > 65_536
    candidate_path = tmp_path / "stale-stat-future.json"
    candidate_path.write_bytes(payload)
    too_large_path = tmp_path / "stale-stat-oversized-future.json"
    too_large_path.write_bytes(b"x" * (future_provider.MAX_CANDIDATE_BYTES + 16))
    underreported_paths = {candidate_path, too_large_path}

    ledger = ResourceLedger(max_nodes=131_072, max_cache_entries=131_072)
    with future_provider.SemanticFutureProviderStore(ledger) as store:
        parse_charge_totals: list[int] = []
        actual_parser = cast(
            _PreflightParser,
            object.__getattribute__(
                future_provider, "_parse_preflighted_future_candidate"
            ),
        )

        def observe_parser(
            candidate: Mapping[str, object],
            *,
            charge_work: Callable[[int], None],
            artifact_sha256: str | None = None,
        ) -> future_provider.ParsedFutureCandidate:
            parse_charge_totals.append(sum(_charges))
            return actual_parser(
                candidate,
                charge_work=charge_work,
                artifact_sha256=artifact_sha256,
            )

        monkeypatch.setattr(
            future_provider,
            "_parse_preflighted_future_candidate",
            observe_parser,
        )
        path_type = type(candidate_path)
        actual_stat = path_type.stat

        def stale_stat(path: Path) -> os.stat_result:
            if path in underreported_paths:
                return cast(os.stat_result, SimpleNamespace(st_size=1))
            return actual_stat(path)

        monkeypatch.setattr(path_type, "stat", stale_stat)
        with pytest.raises(PermissionError, match="no kernel-admitted"):
            store.load_file(candidate_path, charge_work=charge_work)

        payload_work = (len(payload) + 65_535) // 65_536
        assert len(parse_charge_totals) == 1
        assert parse_charge_totals[0] >= payload_work
        assert sum(_charges) >= payload_work
        first_load_work = sum(_charges)

        _charges.clear()
        parse_charge_totals.clear()
        with pytest.raises(ValueError, match="bounded input size"):
            store.load_file(too_large_path, charge_work=charge_work)
        bounded_read_work = (future_provider.MAX_CANDIDATE_BYTES + 1 + 65_535) // 65_536
        assert sum(_charges) == bounded_read_work
        assert parse_charge_totals == []
        assert ledger.counters["comma_future_provider_load_work"] == (
            first_load_work + sum(_charges)
        )


def test_authored_candidate_fits_default_comma_state_budget(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = (
        isabelle_root()
        / "families/comma/comma_semantic_future_instance"
        / "Comma_Semantic_Future_Candidate_Data.thy"
    )
    # This is test-only admission evidence, not a claim that the kernel release
    # theorem has admitted the artifact.
    record = runtime_candidate_record_from_isabelle_data(
        source.read_text(encoding="utf-8"), source
    )
    _charges, charge_work = work_log()
    digest = install_synthetic_registry(monkeypatch, record, charge_work)
    candidate_path = tmp_path / "authored-candidate-v2.json"
    candidate_path.write_bytes(canonical_bytes(record))

    ledger = ResourceLedger(max_nodes=131_072, max_cache_entries=131_072)
    with future_provider.SemanticFutureProviderStore(ledger) as store:
        lease = store.load_file(candidate_path, charge_work=charge_work)
        snapshot = ledger.snapshot()
        controls = record["controls"]
        assert isinstance(controls, list)
        control_rows = cast(list[object], controls)
        assert lease.artifact_sha256 == digest
        assert lease.class_count == len(control_rows)
        assert snapshot.nodes > 0
        assert snapshot.peak_nodes <= 131_072
        assert snapshot.counters["comma_future_provider_publications"] == 1


def test_ledger_store_loads_then_reuses_only_by_verified_digest(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = candidate_record()
    charges, charge_work = work_log()
    digest = install_synthetic_registry(monkeypatch, record, charge_work)
    charges.clear()
    path = tmp_path / "admitted-future.json"
    path.write_bytes(canonical_bytes(record))
    ledger = ResourceLedger(max_nodes=49_152, max_cache_entries=4)
    store = future_provider.SemanticFutureProviderStore(ledger)

    first = store.load_file(path, charge_work=charge_work)
    published = ledger.snapshot()
    assert sum(charges) > 0
    assert first.artifact_sha256 == digest
    assert published.entries == 1
    assert published.nodes > 0
    owners_by_role = {item.role: item for item in published.inventory}
    assert owners_by_role["semantic_future_provider"].entries == 1
    assert owners_by_role["semantic_future_provider_workspace"].nodes == 0
    assert not owners_by_role["semantic_future_provider"].evictable
    assert published.peak_nodes > published.nodes
    assert published.counters["comma_future_provider_publications"] == 1
    assert published.counters["comma_future_provider_load_work"] == sum(charges)

    def reject_reparse(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("warm digest retrieval reparsed provider input")

    monkeypatch.setattr(future_provider, "parse_future_candidate", reject_reparse)
    warm = store.get(digest)
    assert warm.artifact_sha256 == digest
    assert warm.class_count == first.class_count == 3
    assert warm.source_class(BoundaryState("N", 2, 2), charge_work=charge_work) == 2
    assert ledger.counters["comma_future_provider_lookup_hits"] == 1
    assert ledger.counters["comma_future_provider_lease_resolutions"] > 0
    assert ledger.snapshot().entries == published.entries
    assert ledger.snapshot().nodes == published.nodes
    store.close()
