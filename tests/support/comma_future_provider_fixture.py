"""Canonical finite FutureCID candidate used by provider contract tests."""

from __future__ import annotations

import base64
import json
from collections.abc import Callable, Mapping
from types import MappingProxyType
from typing import cast

import pytest

from devtools.paths import isabelle_root
from devtools.verification.comma_semantic_future_artifact import (
    runtime_candidate_record_from_isabelle_data,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.comma import (
    future_authority,
    future_provider,
    future_provider_codec,
)


def candidate_record() -> dict[str, object]:
    class_ids = bytearray([2]) * future_provider_codec.SOURCE_COUNT
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
    }


def fixture_admission(
    record: Mapping[str, object], charge_work: Callable[[int], None]
) -> tuple[str, future_authority.KernelInstanceAdmission]:
    parsed = future_provider.parse_future_candidate(record, charge_work=charge_work)
    admission = future_authority.KernelInstanceAdmission(
        artifact_sha256=parsed.artifact_sha256,
        instance_id=future_authority.FINITE_TEST_FIXTURE_SESSION_ID,
        theorem_id=future_authority.FINITE_TEST_FIXTURE_THEOREM_ID,
        contract_id=future_authority.FINITE_TEST_FIXTURE_CONTRACT_ID,
        claims=future_authority.FINITE_TEST_FIXTURE_CLAIMS,
        scope=future_authority.FINITE_TEST_FIXTURE_SCOPE,
    )
    return parsed.artifact_sha256, admission


def work_log() -> tuple[list[int], Callable[[int], None]]:
    charges: list[int] = []

    def charge(amount: int) -> None:
        if type(amount) is not int or amount <= 0:
            raise ValueError("test charger received an invalid amount")
        charges.append(amount)

    return charges, charge


def install_synthetic_registry(
    monkeypatch: pytest.MonkeyPatch,
    record: dict[str, object],
    charge_work: Callable[[int], None],
) -> str:
    """Install explicit test-only evidence through the private registry seam."""
    digest, admission = fixture_admission(record, charge_work)
    registry = MappingProxyType({digest: admission})
    monkeypatch.setattr(future_provider, "_ADMITTED_KERNEL_INSTANCES", registry)
    return digest


def canonical_bytes(record: Mapping[str, object]) -> bytes:
    return (
        json.dumps(record, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
        + "\n"
    ).encode("ascii")


def provider_classes(
    provider: future_provider.SemanticFutureProvider,
) -> tuple[future_provider.FutureClass, ...]:
    return cast(
        tuple[future_provider.FutureClass, ...],
        object.__getattribute__(provider, "_classes"),
    )


def provider_source_classes(
    provider: future_provider.SemanticFutureProvider,
) -> tuple[int, ...]:
    return cast(tuple[int, ...], object.__getattribute__(provider, "_source_classes"))


def workspace_owner(ledger: ResourceLedger) -> int:
    return next(
        row.owner
        for row in ledger.inventory()
        if row.role == "semantic_future_provider_workspace"
    )


def authored_candidate_record() -> dict[str, object]:
    source = (
        isabelle_root()
        / "families/comma/comma_semantic_future_instance"
        / "Comma_Semantic_Future_Candidate_Data.thy"
    )
    return runtime_candidate_record_from_isabelle_data(
        source.read_text(encoding="utf-8"), source
    )


def install_test_only_global_registry(
    monkeypatch: pytest.MonkeyPatch, record: Mapping[str, object]
) -> str:
    """Exercise the global consumer under explicitly synthetic test admission."""

    def charge_no_work(_amount: int) -> None:
        return None

    parsed = future_provider.parse_future_candidate(record, charge_work=charge_no_work)
    admission = future_authority.KernelInstanceAdmission(
        artifact_sha256=parsed.artifact_sha256,
        instance_id=future_authority.GLOBAL_RELEASE_SESSION_ID,
        theorem_id=future_authority.GLOBAL_RELEASE_THEOREM_ID,
        contract_id=future_authority.GLOBAL_RELEASE_CONTRACT_ID,
        claims=future_authority.GLOBAL_RELEASE_CLAIMS,
        scope=future_authority.KERNEL_RELEASE_SCOPE,
    )
    monkeypatch.setattr(
        future_provider,
        "_ADMITTED_KERNEL_INSTANCES",
        MappingProxyType({parsed.artifact_sha256: admission}),
    )
    monkeypatch.setattr(
        future_provider,
        "registered_global_release_artifact_sha256",
        lambda: parsed.artifact_sha256,
    )
    return parsed.artifact_sha256
