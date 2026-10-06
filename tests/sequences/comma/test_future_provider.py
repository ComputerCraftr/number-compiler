"""Bounded contract tests for the preparatory semantic FutureCID provider."""

from __future__ import annotations

import base64
import copy
import json
import os
from collections.abc import Callable, Mapping
from dataclasses import FrozenInstanceError
from pathlib import Path
from types import MappingProxyType, SimpleNamespace
from typing import cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.comma import future_provider
from number_compiler.sequences.comma.boundary_chart import PERIOD
from number_compiler.sequences.comma.boundary_quotient import BoundaryState


def _candidate_record() -> dict[str, object]:
    class_ids = bytearray([2]) * future_provider.SOURCE_COUNT
    class_ids[0] = 0
    class_ids[1] = 1
    return {
        "format": future_provider.FUTURE_CANDIDATE_FORMAT,
        "authority": "untrusted-source-derived-candidate",
        "state_universe": future_provider.FUTURE_SOURCE_UNIVERSE,
        "class_of_state_varint_base64": base64.b64encode(class_ids).decode("ascii"),
        "controls": [["landmine", None], ["fork", 2], ["fork", 2]],
        "ordered_children": [[None, None], [0, 0], [1, 2]],
        "class_rank_candidate": [0, 1, None],
        "refinement_rounds": 1,
        "refinement_collision_witnesses": [],
        "seam_is_projected_from_cid": False,
        "seam_projection_collision": {"fixture": "test-only"},
    }


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
    parsed = future_provider.parse_future_candidate(record, charge_work=charge_work)
    admission = future_provider._KernelInstanceAdmission(
        artifact_sha256=parsed.artifact_sha256,
        instance_id="TEST_ONLY: bounded synthetic FutureCID fixture",
        theorem_id="TEST_ONLY: not a kernel theorem",
        contract_id=future_provider.FUTURE_PROVIDER_CONTRACT,
        claims=future_provider._REGISTRY_CONTRACT,
    )
    registry = MappingProxyType({parsed.artifact_sha256: admission})
    monkeypatch.setattr(future_provider, "_ADMITTED_KERNEL_INSTANCES", registry)
    return parsed.artifact_sha256


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


def test_empty_production_registry_rejects_structurally_valid_candidate() -> None:
    _charges, charge_work = _work_log()
    assert not future_provider._ADMITTED_KERNEL_INSTANCES
    with pytest.raises(PermissionError, match="no kernel-admitted"):
        future_provider.SemanticFutureProvider.from_record(
            _candidate_record(), charge_work=charge_work
        )


def test_admitted_provider_selects_one_slot_and_preserves_literal_children(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    record = _candidate_record()
    charges, charge_work = _work_log()
    digest = _install_synthetic_registry(monkeypatch, record, charge_work)
    provider = future_provider.SemanticFutureProvider.from_record(
        record, charge_work=charge_work
    )
    source = BoundaryState("N", 2, 2)

    selection = provider.select_unique_unranked_child(source, charge_work=charge_work)
    n_child = object()
    z_child = object()
    assert provider.artifact_sha256 == digest
    assert provider.runtime_admitted
    assert selection.source == source
    assert selection.source_class == 2
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
    actual_parser = future_provider.parse_future_candidate

    def observe_parser(
        candidate: Mapping[str, object],
        *,
        charge_work: Callable[[int], None],
    ) -> future_provider.ParsedFutureCandidate:
        parse_charge_totals.append(sum(_charges))
        return actual_parser(candidate, charge_work=charge_work)

    monkeypatch.setattr(future_provider, "parse_future_candidate", observe_parser)
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
    assert parse_charge_totals == [payload_work]
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
        patcher.setattr(future_provider, "parse_future_candidate", reject_parse)
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
