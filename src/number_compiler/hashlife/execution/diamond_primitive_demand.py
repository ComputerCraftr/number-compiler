"""Finite primitive cofactors that certify which arguments need observation.

Unknown ports range only over an already admitted original primitive kernel.
The query retains a universal cofactor certificate, not a field observation:
there are no source cells, positions, emitted words, or composed port universes.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
    BoundarySide,
)
from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.hashlife.interfaces.diamond_kernel import (
    DiamondKernelArena,
    PrimitiveKernel,
)
from number_compiler.resources.ledger import OwnedMemo
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)


@dataclass(frozen=True, slots=True)
class PrimitiveDemandKey:
    kernel: ActionProgramID
    operation: Literal["advance", "emit"]
    side: int
    values: tuple[int | None, ...]

    def __post_init__(self) -> None:
        if (
            type(self.kernel) is not ActionProgramID
            or self.kernel.kind != "diamond-kernel"
            or type(self.operation) is not str
            or self.operation not in ("advance", "emit")
            or type(self.side) is not int
            or self.side not in (0, 1)
            or (self.operation == "emit" and self.side != 0)
            or type(self.values) is not tuple
            or len(self.values) != (2 if self.operation == "advance" else 3)
            or any(
                value is not None
                and (type(value) is not int or not 0 <= value < 1 << 64)
                for value in self.values
            )
        ):
            raise ValueError("invalid finite primitive demand pattern")


@dataclass(frozen=True, slots=True)
class PrimitiveDemandCertificate:
    """A constant value, or a proof that two admitted completions differ."""

    value: int | None

    def __post_init__(self) -> None:
        if self.value is not None and (
            type(self.value) is not int or not 0 <= self.value < 1 << 64
        ):
            raise ValueError("primitive demand result must be a bounded finite value")


class PrimitiveDemandOracle:
    def __init__(self, kernels: DiamondKernelArena) -> None:
        self.kernels, self.ledger = kernels, kernels.ledger
        self.ledger.register_execution_root(self)
        prefix = f"diamond-primitive-demand-{len(self.ledger.inventory())}"
        self.owner = self.ledger.register(prefix, "query_memo")
        self.memo: OwnedMemo[PrimitiveDemandKey, PrimitiveDemandCertificate] = (
            OwnedMemo(self.ledger, self.owner, evictable=True)
        )

    def _validate(
        self, key: PrimitiveDemandKey
    ) -> tuple[PrimitiveKernel, tuple[int, ...]]:
        primitive = self.kernels.kernel(key.kernel)
        sizes: tuple[int, ...]
        if key.operation == "advance":
            count = primitive.left_count if key.side == 0 else primitive.right_count
            sizes = (count, primitive.blank + 1)
        else:
            sizes = (primitive.left_count, primitive.blank + 1, primitive.right_count)
        for value, size in zip(key.values, sizes, strict=True):
            if value is not None and value >= size:
                raise ValueError(
                    "known demand argument is outside its admitted primitive domain"
                )
        return primitive, sizes

    def constant(
        self,
        kernel: ActionProgramID,
        operation: Literal["advance", "emit"],
        side: int,
        values: tuple[int | None, ...],
    ) -> int | None:
        key = PrimitiveDemandKey(kernel, operation, side, values)
        primitive, sizes = self._validate(key)
        # Every supplied field has been checked before even a warm query counts.
        self.ledger.bump(_execution_keys.PRIMITIVE_DEMAND_REQUESTS)
        if all(value is not None for value in values):
            # A fully observed fixed primitive operation needs no certificate
            # allocation or response memo, even when the cache is full.
            self.ledger.bump(_execution_keys.PRIMITIVE_DEMAND_KNOWN_EVALUATIONS)
            self.ledger.bump(_execution_keys.PRIMITIVE_DEMAND_COMPLETION_TESTS)
            assert values[0] is not None and values[1] is not None
            if operation == "advance":
                return primitive.advance(BoundarySide(side), values[0], values[1])
            assert values[2] is not None
            return primitive.emit(values[0], values[1], values[2])
        found = self.memo.get(key)
        if found is not None:
            self.ledger.bump(_execution_keys.PRIMITIVE_DEMAND_CACHE_HITS)
            return found.value
        limit = self.ledger.max_cache_entries
        if limit is not None and self.ledger.entries >= limit:
            raise BlockContextBudgetExceeded(
                "primitive demand certificate needs one free cache entry"
            )
        node_limit = self.ledger.max_nodes
        if node_limit is not None and self.ledger.nodes > node_limit:
            raise BlockContextBudgetExceeded(
                "primitive demand starts above the configured node budget"
            )
        cursors = [0 if value is None else value for value in values]
        self.ledger.bump(
            _execution_keys.PRIMITIVE_DEMAND_CURSOR_PEAK,
            max(
                0,
                len(cursors)
                - self.ledger.counters.get(
                    _execution_keys.PRIMITIVE_DEMAND_CURSOR_PEAK, 0
                ),
            ),
        )
        baseline: int | None = None
        while True:
            self.ledger.bump(_execution_keys.PRIMITIVE_DEMAND_COMPLETION_TESTS)
            result = (
                primitive.advance(BoundarySide(side), cursors[0], cursors[1])
                if operation == "advance"
                else primitive.emit(cursors[0], cursors[1], cursors[2])
            )
            if baseline is None:
                baseline = result
            elif baseline != result:
                self.ledger.bump(_execution_keys.PRIMITIVE_DEMAND_EARLY_VARIATION_EXITS)
                baseline = None
                break
            # Mixed-radix enumeration has at most three original finite ports.
            # Known ports never advance, and no collection of outputs is built.
            index = len(cursors) - 1
            while index >= 0:
                if values[index] is None:
                    if cursors[index] < sizes[index] - 1:
                        cursors[index] += 1
                        break
                    cursors[index] = 0
                index -= 1
            if index < 0:
                break
        certificate = PrimitiveDemandCertificate(baseline)
        self.memo[key] = certificate
        self.ledger.bump(_execution_keys.PRIMITIVE_DEMAND_EVALUATIONS)
        return certificate.value
