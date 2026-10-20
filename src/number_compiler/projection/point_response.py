"""One bounded response register, never a coordinate-indexed future field."""

from __future__ import annotations

from collections.abc import Callable, MutableSequence
from dataclasses import dataclass

from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.resources.ledger import ResourceLedger, ResourceScope
from number_compiler.resources.metric_keys import projection as _projection_keys


@dataclass(frozen=True, slots=True)
class PointResponse:
    program: ActionProgramID
    position: int
    value: int


@dataclass(frozen=True, slots=True)
class PointResponseAuditSnapshot:
    """Detached response rows and exact registered-store identity."""

    ledger: ResourceLedger
    owner: int
    store_identity: int
    responses: tuple[PointResponse, ...]


class PointResponseRegister:
    """Keep at most the last requested scalar, charged before evaluation."""

    def __init__(self, compiler: LazyCompiler) -> None:
        self.compiler = compiler
        self.ledger: ResourceLedger = compiler.ledger
        self.ledger.register_execution_root(self)
        owner = self.ledger.register(
            "point-response", "observation_memo", ResourceScope.INDEX_OWNED
        )
        self.owner = owner
        self._value: MutableSequence[PointResponse] = self.ledger.make_list(
            owner, append_only=False
        )
        self.ledger.register_container(
            owner,
            self._value,
            node_count=self._value.__len__,
            payloads=lambda: self._value,
            evict=self.clear,
        )

    def audit_snapshot(self) -> PointResponseAuditSnapshot:
        """Expose bounded response records without exposing the mutable store."""
        return PointResponseAuditSnapshot(
            self.ledger,
            self.owner,
            id(self._value),
            tuple(self._value),
        )

    def clear(self) -> None:
        size = len(self._value)
        self._value.clear()
        self.ledger.release(self.owner, entries=size, nodes=size)

    def query(
        self, program: ActionProgramID, position: int, evaluate: Callable[[int], int]
    ) -> int:
        # Handle ownership/range checks precede even an identical warm hit.
        effect = self.compiler.resolve(program)
        self.ledger.bump(_projection_keys.POINT_RESPONSE_REQUESTS)
        if self._value:
            last = self._value[0]
            if last.program == program and last.position == position:
                self.ledger.bump(_projection_keys.POINT_RESPONSE_CACHE_HITS)
                return last.value
        reserved = not self._value
        if reserved:
            self.ledger.reserve(self.owner, entries=1, nodes=1)
        try:
            value = evaluate(position)
            if type(value) is not int or not 0 <= value <= effect.blank:
                raise ValueError(
                    "point evaluator returned a value outside its alphabet"
                )
            result = PointResponse(program, position, value)
        except BaseException:
            if reserved:
                self.ledger.release(self.owner, entries=1, nodes=1)
            raise
        if reserved:
            self._value.append(result)
        else:
            self._value[0] = result
        self.ledger.bump(_projection_keys.POINT_RESPONSE_EVALUATIONS)
        return value
