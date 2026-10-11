"""Canonical finite FutureCID candidate used by provider contract tests."""

from __future__ import annotations

import base64
from collections.abc import Callable, Mapping

from number_compiler.sequences.comma import future_authority, future_provider


def candidate_record() -> dict[str, object]:
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


def fixture_admission(
    record: Mapping[str, object], charge_work: Callable[[int], None]
) -> tuple[str, future_authority._KernelInstanceAdmission]:
    parsed = future_provider.parse_future_candidate(record, charge_work=charge_work)
    admission = future_authority._KernelInstanceAdmission(
        artifact_sha256=parsed.artifact_sha256,
        instance_id=future_authority.FINITE_TEST_FIXTURE_SESSION_ID,
        theorem_id=future_authority.FINITE_TEST_FIXTURE_THEOREM_ID,
        contract_id=future_authority.FINITE_TEST_FIXTURE_CONTRACT_ID,
        claims=future_authority.FINITE_TEST_FIXTURE_CLAIMS,
        scope=future_authority.FINITE_TEST_FIXTURE_SCOPE,
    )
    return parsed.artifact_sha256, admission
