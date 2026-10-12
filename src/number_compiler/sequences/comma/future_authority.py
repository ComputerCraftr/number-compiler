"""Canonical FutureCID row values used by the admitted provider."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from types import MappingProxyType
from typing import Literal

from number_compiler.resources.immutable_signature import (
    ScalarSignature,
    make_scalar_signature,
)

FutureControlKind = Literal["fork", "landmine"]
FutureClassRow = tuple[int | None, int | None]

GLOBAL_RELEASE_SESSION_ID = "Comma_Semantic_Future_Instance"
GLOBAL_RELEASE_THEOREM_ID = (
    "Comma_Semantic_Global_Safety.comma_semantic_global_release_safety"
)
GLOBAL_RELEASE_CONTRACT_ID = "comma-semantic-global-release-safety-v1"
GLOBAL_RELEASE_CLAIMS = frozenset(
    {
        "complete-source-map",
        "semantic-control-equality",
        "ordered-child-equality",
        "rank-rows-checked",
        "global-decimal-roots-have-infinite-path-iff-20",
        "source20-first-child-19999999999-at-path-index-412987859",
        "all-source20-infinite-paths-agree-at-every-index",
        "positive-infinite-start-is-at-least-20",
    }
)
FINITE_TEST_FIXTURE_SCOPE = "test-fixture"
KERNEL_RELEASE_SCOPE = "kernel-release"
FINITE_TEST_FIXTURE_SESSION_ID = "TEST_ONLY: semantic future fixture"
FINITE_TEST_FIXTURE_THEOREM_ID = "TEST_ONLY: not a kernel theorem"
FINITE_TEST_FIXTURE_CONTRACT_ID = "comma-semantic-future-provider-fixture-v1"
FINITE_TEST_FIXTURE_CLAIMS = frozenset(
    {
        "complete-source-map",
        "semantic-control-equality",
        "ordered-child-equality",
        "rank-rows-checked",
    }
)

SOURCE20_FIRST_FORK_INDEX = 412_987_859
SOURCE20_FIRST_FORK_VALUE = 19_999_999_918
SOURCE20_FIRST_FORK_CHILDREN = (19_999_999_999, 20_000_000_000)
SOURCE20_SELECTED_CHILD_INDEX = 412_987_860
SOURCE20_SELECTED_CHILD = 19_999_999_999


@dataclass(frozen=True, slots=True)
class _KernelInstanceAdmission:
    artifact_sha256: str
    instance_id: str
    theorem_id: str
    contract_id: str
    claims: frozenset[str]
    scope: str


def _valid_artifact_digest(digest: str) -> bool:
    return (
        type(digest) is str
        and len(digest) == 64
        and all(character in "0123456789abcdef" for character in digest)
    )


def _registered_admission_matches(
    admission: _KernelInstanceAdmission, digest: str
) -> bool:
    if (
        type(admission) is not _KernelInstanceAdmission
        or not _valid_artifact_digest(digest)
        or type(admission.artifact_sha256) is not str
        or admission.artifact_sha256 != digest
        or type(admission.instance_id) is not str
        or type(admission.theorem_id) is not str
        or type(admission.contract_id) is not str
        or type(admission.scope) is not str
        or type(admission.claims) is not frozenset
        or any(type(claim) is not str for claim in admission.claims)
    ):
        return False
    if admission.scope == KERNEL_RELEASE_SCOPE:
        return _global_release_admission_matches(admission, digest)
    return (
        admission.scope == FINITE_TEST_FIXTURE_SCOPE
        and admission.instance_id == FINITE_TEST_FIXTURE_SESSION_ID
        and admission.theorem_id == FINITE_TEST_FIXTURE_THEOREM_ID
        and admission.contract_id == FINITE_TEST_FIXTURE_CONTRACT_ID
        and admission.claims == FINITE_TEST_FIXTURE_CLAIMS
    )


def _global_release_admission_matches(
    admission: _KernelInstanceAdmission, digest: str
) -> bool:
    return (
        type(admission) is _KernelInstanceAdmission
        and _valid_artifact_digest(digest)
        and type(admission.artifact_sha256) is str
        and admission.artifact_sha256 == digest
        and type(admission.instance_id) is str
        and admission.instance_id == GLOBAL_RELEASE_SESSION_ID
        and type(admission.theorem_id) is str
        and admission.theorem_id == GLOBAL_RELEASE_THEOREM_ID
        and type(admission.contract_id) is str
        and admission.contract_id == GLOBAL_RELEASE_CONTRACT_ID
        and type(admission.scope) is str
        and admission.scope == KERNEL_RELEASE_SCOPE
        and type(admission.claims) is frozenset
        and all(type(claim) is str for claim in admission.claims)
        and admission.claims == GLOBAL_RELEASE_CLAIMS
    )


def registered_global_release_artifact_sha256(
    registry: Mapping[str, _KernelInstanceAdmission],
) -> str | None:
    """Read the unique exact global digest from an immutable admission map."""
    if type(registry) is not MappingProxyType:
        raise PermissionError("semantic future admission registry is not immutable")
    global_digests: list[str] = []
    for digest, admission in registry.items():
        if type(admission) is not _KernelInstanceAdmission:
            raise PermissionError("semantic future registry contains a foreign entry")
        if admission.scope != KERNEL_RELEASE_SCOPE:
            continue
        if not _global_release_admission_matches(admission, digest):
            raise PermissionError("semantic future global registry entry is invalid")
        global_digests.append(digest)
    if len(global_digests) > 1:
        raise PermissionError(
            "multiple global semantic future artifacts are registered"
        )
    return None if not global_digests else global_digests[0]


@dataclass(frozen=True, slots=True)
class FutureControl:
    """Exact terminal class control carried by one checked quotient row."""

    kind: FutureControlKind
    fork_coefficient: int | None

    def __post_init__(self) -> None:
        if type(self.kind) is not str:
            raise ValueError("unknown future class control")
        if self.kind == "fork":
            if (
                type(self.fork_coefficient) is not int
                or not 2 <= self.fork_coefficient <= 9
            ):
                raise ValueError("future Fork control needs its exact coefficient")
        elif self.kind == "landmine":
            if self.fork_coefficient is not None:
                raise ValueError("future Landmine control cannot carry a coefficient")
        else:
            raise ValueError("unknown future class control")


@dataclass(frozen=True, slots=True)
class FutureClass:
    """One admitted classifier row; edge slots retain their N/Z order."""

    control: FutureControl
    ordered_children: FutureClassRow
    rank: int | None


def _class_row_signature(row: FutureClass) -> ScalarSignature:
    if type(row) is not FutureClass or type(row.control) is not FutureControl:
        raise TypeError("future class row has a foreign control descriptor")
    control = row.control
    children = row.ordered_children
    if (
        type(control.kind) is not str
        or control.kind not in ("fork", "landmine")
        or (
            control.fork_coefficient is not None
            and type(control.fork_coefficient) is not int
        )
        or type(children) is not tuple
        or len(children) != 2
        or any(child is not None and type(child) is not int for child in children)
        or (row.rank is not None and type(row.rank) is not int)
    ):
        raise TypeError("future class row has noncanonical scalar fields")
    return make_scalar_signature(
        (
            control.kind,
            control.fork_coefficient,
            children[0],
            children[1],
            row.rank,
        )
    )
