"""Bounded contract tests for the preparatory semantic FutureCID provider."""

from __future__ import annotations

import base64
import copy
import json
import os
from collections.abc import Callable, Mapping
from dataclasses import FrozenInstanceError, replace
from pathlib import Path
from types import MappingProxyType, SimpleNamespace
from typing import cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.comma import future_authority, future_provider
from number_compiler.sequences.comma.boundary_chart import PERIOD
from number_compiler.sequences.comma.boundary_quotient import BoundaryState
from number_compiler.sequences.comma.power import CommaTerm
from tests.support.comma_future_provider_fixture import (
    candidate_record as _candidate_record,
)
from tests.support.comma_future_provider_fixture import (
    fixture_admission,
)


def _record_list(record: dict[str, object], field: str) -> list[object]:
    value = record[field]
    assert isinstance(value, list)
    return value


def _work_log() -> tuple[list[int], Callable[[int], None]]:
    charges: list[int] = []

    def charge(amount: int) -> None:
        if type(amount) is not int or amount <= 0:
            raise ValueError("test charger received an invalid amount")
        charges.append(amount)

    return charges, charge


def _install_synthetic_registry(
    monkeypatch: pytest.MonkeyPatch,
    record: dict[str, object],
    charge_work: Callable[[int], None],
) -> str:
    """Install explicit test-only evidence through the private registry seam."""
    digest, admission = fixture_admission(record, charge_work)
    registry = MappingProxyType({digest: admission})
    monkeypatch.setattr(future_provider, "_ADMITTED_KERNEL_INSTANCES", registry)
    return digest


def _canonical_bytes(record: dict[str, object]) -> bytes:
    return (
        json.dumps(record, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
        + "\n"
    ).encode("ascii")


def test_structural_parser_decodes_nested_boundary_binding_without_authority() -> None:
    charges, charge_work = _work_log()
    parsed = future_provider.parse_future_candidate(
        _candidate_record(), charge_work=charge_work
    )

    assert len(parsed.source_classes) == future_provider.SOURCE_COUNT
    assert parsed.classes[2].control == future_provider.FutureControl("fork", 2)
    assert parsed.classes[2].ordered_children == (1, 2)
    assert parsed.classes[2].rank is None
    assert parsed.source_classes[BoundaryState("N", 2, 0).exponent_residue] == 0
    assert parsed.source_classes[BoundaryState("N", 2, 1).exponent_residue] == 1
    z_index = 8 * PERIOD
    assert parsed.source_classes[z_index] == 2
    assert sum(charges) >= future_provider.SOURCE_COUNT


def test_read_only_root_mapping_uses_the_same_bounded_canonical_digest() -> None:
    record = _candidate_record()
    read_only_record = MappingProxyType(record)
    charges, charge_work = _work_log()
    parsed_dict = future_provider.parse_future_candidate(
        record, charge_work=charge_work
    )
    parsed_read_only = future_provider.parse_future_candidate(
        read_only_record, charge_work=charge_work
    )
    assert parsed_read_only.artifact_sha256 == parsed_dict.artifact_sha256
    assert parsed_read_only.source_classes == parsed_dict.source_classes
    assert parsed_read_only.classes == parsed_dict.classes

    charges, charge_work = _work_log()
    expected_charges, expected_charge = _work_log()
    future_provider._preflight_future_candidate(
        read_only_record, charge_work=expected_charge
    )
    expected_preflight_work = sum(expected_charges)
    charges.clear()
    callback_charge_totals: list[int] = []
    with pytest.raises(PermissionError, match="no kernel-admitted"):
        future_provider.SemanticFutureProvider.from_record(
            read_only_record,
            charge_work=charge_work,
            _before_parse=lambda _record: callback_charge_totals.append(sum(charges)),
        )
    assert callback_charge_totals == [expected_preflight_work]


def test_empty_production_registry_rejects_structurally_valid_candidate() -> None:
    _charges, charge_work = _work_log()
    assert not future_provider._ADMITTED_KERNEL_INSTANCES
    with pytest.raises(PermissionError, match="no kernel-admitted"):
        future_provider.SemanticFutureProvider.from_record(
            _candidate_record(), charge_work=charge_work
        )


def test_private_term_staging_rejects_unadmitted_artifact_and_closes_store(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(
        future_provider, "_ADMITTED_KERNEL_INSTANCES", MappingProxyType({})
    )
    candidate_path = tmp_path / "unadmitted-future.json"
    candidate_path.write_bytes(_canonical_bytes(_candidate_record()))
    term = CommaTerm(1)

    with pytest.raises(PermissionError, match="no kernel-admitted"):
        term._stage_global_future_provider_artifact(candidate_path)

    assert term._future_provider_store is None
    assert term._future_provider_lease is None
    assert term.ledger.counters.get("comma_future_provider_load_failures", 0) == 1
    assert term.ledger.counters.get("comma_future_provider_closes", 0) == 1
    term.close()
    assert term.ledger.counters.get("comma_future_provider_closes", 0) == 1


def test_private_term_staging_rejects_query_progress_before_reading_artifact(
    tmp_path: Path,
) -> None:
    term = CommaTerm(1)
    assert term.materialize() == 20
    missing_path = tmp_path / "must-not-be-read.json"

    with pytest.raises(ValueError, match="only allowed before use"):
        term._stage_global_future_provider_artifact(missing_path)

    assert term._future_provider_store is None
    assert term.ledger.counters.get("comma_future_provider_load_requests", 0) == 0


def test_in_memory_record_bounds_ignored_metadata_before_serializing(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = _candidate_record()
    record["seam_projection_collision"] = {
        "untrusted": "x" * future_provider.MAX_CANDIDATE_BYTES
    }
    charges, charge_work = _work_log()

    def reject_serialize(_record: Mapping[str, object]) -> str:
        raise AssertionError("oversized input reached canonical serialization")

    monkeypatch.setattr(future_provider, "_future_candidate_sha256", reject_serialize)
    callback_calls: list[bool] = []
    with pytest.raises(ValueError, match="bounded JSON size"):
        future_provider.SemanticFutureProvider.from_record(
            record,
            charge_work=charge_work,
            _before_parse=lambda _record: callback_calls.append(True),
        )
    assert sum(charges) > 0
    assert callback_calls == []


def test_record_callback_cannot_mutate_the_bounded_parse_snapshot(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = _candidate_record()
    expected_controls = copy.deepcopy(record["controls"])
    expected_metadata = copy.deepcopy(record["seam_projection_collision"])
    original_digest = future_provider._future_candidate_sha256
    observed_snapshots: list[Mapping[str, object]] = []
    charges, charge_work = _work_log()

    def mutate_original(original: Mapping[str, object]) -> None:
        assert original is record
        _record_list(record, "controls")[2] = ["landmine", None]
        metadata = record["seam_projection_collision"]
        assert isinstance(metadata, dict)
        metadata["after_snapshot"] = "x" * future_provider.MAX_CANDIDATE_BYTES

    def observe_digest(snapshot: Mapping[str, object]) -> str:
        observed_snapshots.append(snapshot)
        assert snapshot is not record
        assert snapshot["controls"] == expected_controls
        assert snapshot["seam_projection_collision"] == expected_metadata
        return original_digest(snapshot)

    monkeypatch.setattr(future_provider, "_future_candidate_sha256", observe_digest)
    with pytest.raises(PermissionError, match="no kernel-admitted"):
        future_provider.SemanticFutureProvider.from_record(
            record,
            charge_work=charge_work,
            _before_parse=mutate_original,
        )

    assert len(observed_snapshots) == 1
    assert sum(charges) > 0


def test_in_memory_record_bounds_json_depth_and_integer_width() -> None:
    charges, charge_work = _work_log()
    too_deep = _candidate_record()
    nested: object = None
    for _ in range(future_provider.MAX_CANDIDATE_JSON_DEPTH + 1):
        nested = [nested]
    too_deep["seam_projection_collision"] = {"nested": nested}
    with pytest.raises(ValueError, match="nesting exceeds its bound"):
        future_provider.parse_future_candidate(too_deep, charge_work=charge_work)
    assert sum(charges) > 0

    charges.clear()
    too_wide = _candidate_record()
    too_wide["refinement_rounds"] = 1 << (future_provider.MAX_CANDIDATE_BYTES * 4)
    with pytest.raises(ValueError, match="integer exceeds"):
        future_provider.parse_future_candidate(too_wide, charge_work=charge_work)
    assert sum(charges) > 0


@pytest.mark.parametrize(
    ("mutation", "query"),
    (
        ("source_tuple", "source"),
        ("class_tuple", "source"),
        ("control", "row"),
        ("rank", "row"),
    ),
)
def test_provider_leases_reject_altered_tables_and_rows(
    mutation: str,
    query: str,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = _candidate_record()
    _charges, charge_work = _work_log()
    digest = _install_synthetic_registry(monkeypatch, record, charge_work)
    ledger = ResourceLedger(max_nodes=65_536, max_cache_entries=2)
    store = future_provider.SemanticFutureProviderStore(ledger)
    lease = store.load_record(record, charge_work=charge_work)
    provider = store._providers[digest]

    if mutation == "source_tuple":
        altered = tuple(1 if cid == 0 else cid for cid in provider._source_classes)
        object.__setattr__(provider, "_source_classes", altered)
    elif mutation == "class_tuple":
        object.__setattr__(
            provider,
            "_classes",
            tuple(row for row in provider._classes),
        )
    elif mutation == "control":
        object.__setattr__(provider._classes[2].control, "kind", "landmine")
    else:
        object.__setattr__(provider._classes[2], "rank", 0)

    with pytest.raises(PermissionError, match="provider|row"):
        if query == "source":
            lease.source_class(BoundaryState("N", 2, 0), charge_work=charge_work)
        else:
            lease.class_row(2, charge_work=charge_work)
    store.close()


def test_warm_class_row_guard_checks_only_its_signature(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = _candidate_record()
    _charges, charge_work = _work_log()
    digest = _install_synthetic_registry(monkeypatch, record, charge_work)
    ledger = ResourceLedger(max_nodes=65_536, max_cache_entries=2)
    store = future_provider.SemanticFutureProviderStore(ledger)
    lease = store.load_record(record, charge_work=charge_work)
    provider = store._providers[digest]
    object.__setattr__(provider._classes[1], "rank", 7)

    def reject_full_validation(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("warm lookup must not reparse or hash the full table")

    monkeypatch.setattr(future_provider, "_validate_record", reject_full_validation)
    monkeypatch.setattr(
        future_provider,
        "_future_candidate_sha256",
        reject_full_validation,
    )
    row = lease.class_row(2, charge_work=charge_work)
    assert row.control == future_provider.FutureControl("fork", 2)
    store.close()


def test_future_control_rejects_kind_equality_aliases() -> None:
    class ForkKindAlias:
        def __eq__(self, other: object) -> bool:
            return other == "fork"

    with pytest.raises(ValueError, match="unknown future class control"):
        future_authority.FutureControl(
            cast(future_authority.FutureControlKind, ForkKindAlias()),
            2,
        )


def test_preflight_charges_before_validation_and_in_bounded_string_chunks() -> None:
    malformed = _candidate_record()
    malformed["seam_projection_collision"] = {1: "bad object key"}
    refused_charges: list[int] = []

    def no_budget(amount: int) -> None:
        refused_charges.append(amount)
        raise RuntimeError("work budget exhausted")

    with pytest.raises(RuntimeError, match="work budget exhausted"):
        future_provider._preflight_future_candidate(malformed, charge_work=no_budget)
    assert refused_charges == [1]

    large_string_record = _candidate_record()
    large_string_record["seam_projection_collision"] = {"ignored": "\x01" * 100_000}
    charges, charge_work = _work_log()
    future_provider._preflight_future_candidate(
        large_string_record, charge_work=charge_work
    )
    expected_size_units = (
        len(_canonical_bytes(large_string_record)) + 65_535
    ) // 65_536
    assert sum(charges) == expected_size_units
    assert len(charges) > 1


def test_file_loader_preflights_nested_metadata_before_canonical_dump(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = _candidate_record()
    nested: object = None
    for _ in range(future_provider.MAX_CANDIDATE_JSON_DEPTH + 1):
        nested = [nested]
    record["seam_projection_collision"] = {"nested": nested}
    payload = _canonical_bytes(record)
    candidate_path = tmp_path / "deep-future-candidate.json"
    candidate_path.write_bytes(payload)
    charges, charge_work = _work_log()

    def reject_canonical_dump(_record: Mapping[str, object]) -> bytes:
        raise AssertionError("deep metadata reached canonical serialization")

    monkeypatch.setattr(future_provider, "_canonical_json_bytes", reject_canonical_dump)
    with pytest.raises(ValueError, match="nesting exceeds its bound"):
        future_provider.SemanticFutureProvider.load_file(
            candidate_path, charge_work=charge_work
        )
    assert sum(charges) >= (len(payload) + 65_535) // 65_536


def test_lease_rejects_a_total_fake_store_and_direct_unretained_binding() -> None:
    class FakeStore:
        def _resolve(self, _digest: str, _token: ArenaToken) -> object:
            raise AssertionError("fake store should never resolve")

    with pytest.raises(TypeError, match="exact provider store"):
        future_provider.SemanticFutureProviderLease(
            cast(future_provider.SemanticFutureProviderStore, FakeStore()),
            "0" * 64,
            ArenaToken("fake-provider-store"),
        )

    ledger = ResourceLedger(max_nodes=64, max_cache_entries=1)
    store = future_provider.SemanticFutureProviderStore(ledger)
    store.__dict__["_resolve"] = lambda *_args: cast(
        future_provider.SemanticFutureProvider, object()
    )
    forged = future_provider.SemanticFutureProviderLease(
        store,
        "0" * 64,
        store._token,
    )
    with pytest.raises(RuntimeError, match="no longer retained"):
        _ = forged.class_count
    store.close()


def test_admitted_provider_selects_one_slot_and_preserves_literal_children(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = _candidate_record()
    charges, charge_work = _work_log()
    digest = _install_synthetic_registry(monkeypatch, record, charge_work)
    provider = future_provider.SemanticFutureProvider.from_record(
        record, charge_work=charge_work
    )
    # Source index 3 is deliberately distinct from the synthetic table's CID 2.
    # This ensures the selection follows the source-to-CID map before reading
    # the class row, rather than treating the source offset as a class ID.
    source = BoundaryState("N", 2, 3)
    source_index = future_provider._source_index(source)
    assert source_index == 3

    selection = provider.select_unique_unranked_child(source, charge_work=charge_work)
    n_child = object()
    z_child = object()
    assert provider.artifact_sha256 == digest
    assert provider.runtime_admitted
    assert not provider.global_release_admitted
    with pytest.raises(PermissionError, match="global release authority"):
        provider.require_global_release_admission()
    assert selection.source == source
    assert selection.source_class == 2
    assert selection.source_class != source_index
    assert selection.fork_coefficient == 2
    assert selection.ordered_child_classes == (1, 2)
    assert selection.selected_slot == 1
    assert selection.selected_class == 2
    assert selection.select_literal((n_child, z_child)) is z_child
    assert sum(charges) >= 2 * future_provider.SOURCE_COUNT


def test_provider_binding_fields_cannot_be_reassigned(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = _candidate_record()
    _charges, charge_work = _work_log()
    _install_synthetic_registry(monkeypatch, record, charge_work)
    provider = future_provider.SemanticFutureProvider.from_record(
        record, charge_work=charge_work
    )

    forged_bindings: tuple[tuple[str, object], ...] = (
        ("_source_classes", ()),
        ("_classes", ()),
        ("_digest", "forged-digest"),
        ("_admission", object()),
    )
    for field, value in forged_bindings:
        with pytest.raises(FrozenInstanceError):
            setattr(provider, field, value)

    assert provider.runtime_admitted
    assert provider.artifact_sha256


def test_release_authority_requires_exact_global_theorem_and_all_claims() -> None:
    digest = "a" * 64
    fixture = future_authority._KernelInstanceAdmission(
        artifact_sha256=digest,
        instance_id=future_authority.FINITE_TEST_FIXTURE_SESSION_ID,
        theorem_id=future_authority.FINITE_TEST_FIXTURE_THEOREM_ID,
        contract_id=future_authority.FINITE_TEST_FIXTURE_CONTRACT_ID,
        claims=future_authority.FINITE_TEST_FIXTURE_CLAIMS,
        scope=future_authority.FINITE_TEST_FIXTURE_SCOPE,
    )
    assert future_authority._registered_admission_matches(fixture, digest)
    assert not future_authority._global_release_admission_matches(fixture, digest)

    # These release-shaped records are deliberately incomplete contract probes;
    # they are never installed in the empty production registry.
    release_shape = future_authority._KernelInstanceAdmission(
        artifact_sha256=digest,
        instance_id=future_authority.GLOBAL_RELEASE_SESSION_ID,
        theorem_id=future_authority.GLOBAL_RELEASE_THEOREM_ID,
        contract_id=future_authority.GLOBAL_RELEASE_CONTRACT_ID,
        claims=future_authority.GLOBAL_RELEASE_CLAIMS,
        scope=future_authority.KERNEL_RELEASE_SCOPE,
    )
    missing_claim_probes = tuple(
        replace(release_shape, claims=release_shape.claims - {claim})
        for claim in future_authority.GLOBAL_RELEASE_CLAIMS
    )
    malformed = (
        replace(release_shape, theorem_id="comma_semantic_global_release_safety"),
        replace(release_shape, theorem_id="unrelated.nonempty_theorem"),
        *missing_claim_probes,
        replace(release_shape, instance_id="another Isabelle session"),
        replace(
            release_shape,
            contract_id=future_provider.FUTURE_PROVIDER_CONTRACT,
        ),
    )
    for probe in malformed:
        assert not future_authority._registered_admission_matches(probe, digest)
        assert not future_authority._global_release_admission_matches(probe, digest)

    assert future_provider._ADMITTED_KERNEL_INSTANCES == {}


def test_provider_rejects_digest_changes_to_control_children_or_rank(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = _candidate_record()
    _charges, charge_work = _work_log()
    digest = _install_synthetic_registry(monkeypatch, record, charge_work)
    assert digest

    mutations: tuple[tuple[str, Callable[[dict[str, object]], None]], ...] = (
        (
            "control",
            lambda candidate: _record_list(candidate, "controls").__setitem__(
                2, ["fork", 3]
            ),
        ),
        (
            "ordered children",
            lambda candidate: _record_list(candidate, "ordered_children").__setitem__(
                2, [2, 1]
            ),
        ),
        (
            "rank",
            lambda candidate: _record_list(
                candidate, "class_rank_candidate"
            ).__setitem__(0, 7),
        ),
    )
    for _name, mutate in mutations:
        forged = copy.deepcopy(record)
        mutate(forged)
        # Local parsing checks representation only; the registered theorem
        # digest is what binds exact controls, ordered edges, and checked ranks.
        future_provider.parse_future_candidate(forged, charge_work=charge_work)
        with pytest.raises(PermissionError, match="no kernel-admitted"):
            future_provider.SemanticFutureProvider.from_record(
                forged, charge_work=charge_work
            )


def _assert_rejected_candidate_field(
    field: str, replacement: object, message: str
) -> None:
    record = _candidate_record()
    record[field] = replacement
    _charges, charge_work = _work_log()
    with pytest.raises(ValueError, match=message):
        future_provider.parse_future_candidate(record, charge_work=charge_work)


@pytest.mark.parametrize(
    ("field", "replacement", "message"),
    [
        ("format", "comma-semantic-future-candidate-v1", "version"),
        ("state_universe", "N/Z only", "source universe"),
        ("class_rank_candidate", [0, True, None], "rank"),
    ],
)
def test_parser_rejects_version_universe_and_rank_type_mismatch(
    field: str, replacement: object, message: str
) -> None:
    _assert_rejected_candidate_field(field, replacement, message)


@pytest.mark.parametrize(
    ("field", "replacement"),
    [("controls", None), ("ordered_children", {}), ("class_rank_candidate", None)],
)
def test_parser_reports_wrong_array_types_as_type_errors(
    field: str, replacement: object
) -> None:
    record = _candidate_record()
    record[field] = replacement
    _charges, charge_work = _work_log()
    with pytest.raises(TypeError):
        future_provider.parse_future_candidate(record, charge_work=charge_work)


@pytest.mark.parametrize(
    ("field", "replacement", "message"),
    [
        (
            "controls",
            [["landmine", None], ["fork", 2], ["unknown", 2]],
            "neither Fork nor Landmine",
        ),
        (
            "ordered_children",
            [[None, None], [0, 0], [3, 1]],
            "leaves the class table",
        ),
        (
            "ordered_children",
            [[2, None], [0, 0], [1, 2]],
            "Landmine row carries",
        ),
        (
            "ordered_children",
            [[None, None], [0, None], [1, 2]],
            "Fork row lost",
        ),
    ],
)
def test_parser_rejects_malformed_control_and_ordered_child_rows(
    field: str,
    replacement: object,
    message: str,
) -> None:
    _assert_rejected_candidate_field(field, replacement, message)


def test_parser_rejects_truncated_noncanonical_and_out_of_range_source_maps() -> None:
    record = _candidate_record()
    original = base64.b64decode(
        cast(str, record["class_of_state_varint_base64"]), validate=True
    )
    _charges, charge_work = _work_log()

    truncated = copy.deepcopy(record)
    truncated["class_of_state_varint_base64"] = base64.b64encode(original[:-1]).decode(
        "ascii"
    )
    with pytest.raises(ValueError, match="truncated or has extra"):
        future_provider.parse_future_candidate(truncated, charge_work=charge_work)

    noncanonical = copy.deepcopy(record)
    payload = bytearray(original)
    payload[0:1] = b"\x80\x00"
    noncanonical["class_of_state_varint_base64"] = base64.b64encode(payload).decode(
        "ascii"
    )
    with pytest.raises(ValueError, match="noncanonical CID varint"):
        future_provider.parse_future_candidate(noncanonical, charge_work=charge_work)

    out_of_range = copy.deepcopy(record)
    payload = bytearray(original)
    payload[0] = 3
    out_of_range["class_of_state_varint_base64"] = base64.b64encode(payload).decode(
        "ascii"
    )
    with pytest.raises(ValueError, match="out-of-range CID"):
        future_provider.parse_future_candidate(out_of_range, charge_work=charge_work)


@pytest.mark.parametrize(
    ("kind", "coefficient", "phase"),
    [("X", 2, 0), ("N", 1, 0), ("Z", 2, PERIOD), ("N", True, 0)],
)
def test_boundary_state_rejects_invalid_future_source_coordinates(
    kind: str, coefficient: int, phase: int
) -> None:
    with pytest.raises(ValueError):
        BoundaryState(kind, coefficient, phase)  # type: ignore[arg-type]


def test_file_loader_requires_canonical_bytes_and_registry_admission(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = _candidate_record()
    _charges, charge_work = _work_log()
    _install_synthetic_registry(monkeypatch, record, charge_work)
    candidate_path = tmp_path / "future.json"
    candidate_path.write_bytes(_canonical_bytes(record))
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
    record = _candidate_record()
    _charges, setup_charge = _work_log()
    _install_synthetic_registry(monkeypatch, record, setup_charge)
    _charges, charge_work = _work_log()

    oversized_record = copy.deepcopy(record)
    oversized_record["refinement_collision_witnesses"] = ["w" * 100] * 700
    payload = _canonical_bytes(oversized_record)
    assert len(payload) > 65_536
    candidate_path = tmp_path / "stale-stat-future.json"
    candidate_path.write_bytes(payload)
    too_large_path = tmp_path / "stale-stat-oversized-future.json"
    too_large_path.write_bytes(b"x" * (future_provider.MAX_CANDIDATE_BYTES + 16))
    underreported_paths = {candidate_path, too_large_path}

    ledger = ResourceLedger(max_nodes=65_536, max_cache_entries=2)
    store = future_provider.SemanticFutureProviderStore(ledger)
    parse_charge_totals: list[int] = []
    actual_parser = future_provider._parse_preflighted_future_candidate

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
    assert len(parse_charge_totals) == 1 and parse_charge_totals[0] >= payload_work
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
    store.close()


def test_ledger_store_loads_then_reuses_only_by_verified_digest(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = _candidate_record()
    charges, charge_work = _work_log()
    digest = _install_synthetic_registry(monkeypatch, record, charge_work)
    charges.clear()
    path = tmp_path / "admitted-future.json"
    path.write_bytes(_canonical_bytes(record))
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

    # Retrieval by the admitted digest consumes the retained provider. It does
    # not call the parser or reconstruct the immutable source/class tuples.
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


def test_store_rejects_changed_inputs_and_failed_publication_is_atomic(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = _candidate_record()
    _charges, charge_work = _work_log()
    _install_synthetic_registry(monkeypatch, record, charge_work)
    ledger = ResourceLedger(max_nodes=65_536, max_cache_entries=4)
    store = future_provider.SemanticFutureProviderStore(ledger)
    original_path = tmp_path / "original-future.json"
    original_path.write_bytes(_canonical_bytes(record))
    retained = store.load_file(original_path, charge_work=charge_work)
    assert retained.artifact_sha256

    changed = copy.deepcopy(record)
    _record_list(changed, "controls")[2] = ["fork", 3]
    before = ledger.snapshot()
    with pytest.raises(PermissionError, match="no kernel-admitted"):
        store.load_record(changed, charge_work=charge_work)
    assert (ledger.entries, ledger.nodes) == (before.entries, before.nodes)

    changed_path = tmp_path / "changed-future.json"
    changed_path.write_bytes(_canonical_bytes(changed))
    with pytest.raises(PermissionError, match="no kernel-admitted"):
        store.load_file(changed_path, charge_work=charge_work)
    assert (ledger.entries, ledger.nodes) == (before.entries, before.nodes)
    assert (
        store.get(retained.artifact_sha256).artifact_sha256 == retained.artifact_sha256
    )
    assert ledger.counters["comma_future_provider_load_failures"] == 2
    store.close()


def test_store_budget_refusal_and_reset_reclaim_all_provider_nodes(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = _candidate_record()
    _charges, charge_work = _work_log()
    _install_synthetic_registry(monkeypatch, record, charge_work)

    limited = ResourceLedger(max_nodes=32, max_cache_entries=1)
    refused = future_provider.SemanticFutureProviderStore(limited)

    def reject_parse(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("budget should be reserved before tuple decoding")

    with monkeypatch.context() as patcher:
        patcher.setattr(
            future_provider,
            "_parse_preflighted_future_candidate",
            reject_parse,
        )
        with pytest.raises(BlockContextBudgetExceeded):
            refused.load_record(record, charge_work=charge_work)
    assert limited.entries == limited.nodes == 0
    refused.close()

    publish_limited = ResourceLedger(max_nodes=40_000, max_cache_entries=1)
    publish_refused = future_provider.SemanticFutureProviderStore(publish_limited)
    with pytest.raises(BlockContextBudgetExceeded):
        publish_refused.load_record(record, charge_work=charge_work)
    assert publish_limited.entries == publish_limited.nodes == 0
    workspace = publish_limited.inventory()[publish_refused._workspace_owner]
    assert workspace.nodes == 0
    assert publish_limited.counters["comma_future_provider_load_failures"] == 1
    publish_refused.close()

    ledger = ResourceLedger(max_nodes=49_152, max_cache_entries=4)
    store = future_provider.SemanticFutureProviderStore(ledger)
    old = store.load_record(record, charge_work=charge_work)
    assert ledger.entries == 1 and ledger.nodes > 0
    store.reset()
    assert ledger.entries == ledger.nodes == 0
    assert not old.runtime_admitted
    with pytest.raises(RuntimeError, match="stale"):
        _ = old.class_count

    current = store.load_record(record, charge_work=charge_work)
    assert current.runtime_admitted
    removed_digest = current.artifact_sha256
    del store._providers[removed_digest]
    assert not current.runtime_admitted
    with pytest.raises(RuntimeError, match="no longer retained"):
        _ = current.class_count
    with pytest.raises(KeyError, match="not been loaded"):
        store.get(removed_digest)
    assert ledger.entries == ledger.nodes == 0
    store.close()
    assert ledger.entries == ledger.nodes == 0
    assert not current.runtime_admitted
    with pytest.raises(RuntimeError, match="stale"):
        _ = current.class_count
    store.close()


def test_store_cancellation_releases_workspace_without_validation_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = _candidate_record()
    _install_synthetic_registry(monkeypatch, record, lambda _amount: None)
    ledger = ResourceLedger(max_nodes=65_536, max_cache_entries=2)
    store = future_provider.SemanticFutureProviderStore(ledger)

    class LoadCancelled(BaseException):
        pass

    def cancel_load(_amount: int) -> None:
        raise LoadCancelled

    with pytest.raises(LoadCancelled):
        store.load_record(record, charge_work=cancel_load)

    assert ledger.entries == ledger.nodes == 0
    workspace = ledger.inventory()[store._workspace_owner]
    assert workspace.nodes == 0
    assert ledger.counters["comma_future_provider_load_cancellations"] == 1
    assert ledger.counters.get("comma_future_provider_load_failures", 0) == 0
    store.close()


def test_provider_selection_refuses_class_with_two_unranked_children(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = _candidate_record()
    _record_list(record, "ordered_children")[2] = [2, 2]
    _charges, charge_work = _work_log()
    _install_synthetic_registry(monkeypatch, record, charge_work)
    provider = future_provider.SemanticFutureProvider.from_record(
        record, charge_work=charge_work
    )
    with pytest.raises(ValueError, match="no unique unranked child"):
        provider.select_unique_unranked_child(
            BoundaryState("N", 2, 2), charge_work=charge_work
        )


def test_boundary_source_rejects_equality_aliases() -> None:
    class NKindAlias:
        def __eq__(self, other: object) -> bool:
            return other == "N"

    with pytest.raises(ValueError, match="invalid comma boundary constructor"):
        BoundaryState(NKindAlias(), 2, 0)  # type: ignore[arg-type]


def test_unranked_selection_rejects_boolean_cid_aliases() -> None:
    with pytest.raises(ValueError, match="exact ordered child CIDs"):
        future_provider.UnrankedChildSelection(
            BoundaryState("N", 2, 0),
            2,
            2,
            (True, False),
            0,
        )


def test_store_owner_name_collision_is_preflighted_before_registration() -> None:
    ledger = ResourceLedger()
    ledger.register(
        "comma-semantic-future-provider-workspace-2",
        "unrelated_owner",
    )
    before = ledger.owner_count

    with pytest.raises(ValueError, match="already registered"):
        future_provider.SemanticFutureProviderStore(ledger)

    assert ledger.owner_count == before
