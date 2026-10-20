"""Read-only storage identities for canonical diamond arena audits."""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from typing import TYPE_CHECKING, Generic, TypeVar

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.diamond_certificate import (
        DiamondCompositionCertificate,
    )
    from number_compiler.hashlife.interfaces.diamond_kernel import (
        FiniteExpression,
        PrimitiveKernel,
    )

_Node = TypeVar("_Node")
_Index = TypeVar("_Index")


@dataclass(frozen=True, slots=True)
class DiamondNodeStorageSnapshot(Generic[_Node, _Index]):
    node_owner: int
    index_owner: int
    node_store_identity: int
    index_store_identity: int
    nodes: Sequence[_Node]
    index: Mapping[_Index, int]


@dataclass(frozen=True, slots=True)
class DiamondKernelStorageSnapshot:
    kernel_owner: int
    expression_owner: int
    kernel_store_identity: int
    expression_store_identity: int
    kernels: Sequence[PrimitiveKernel]
    expressions: Sequence[FiniteExpression]


@dataclass(frozen=True, slots=True)
class DiamondApplicationStorageSnapshot:
    certificate_store_identity: int
    cycle_store_identity: int
    certificates: Sequence[DiamondCompositionCertificate]
    cycles: Sequence[object]
