"""Typed records for the source-free higher semantic DAG."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal, Protocol, TypeAlias

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.resources.ledger import ResourceLedger


@dataclass(frozen=True, slots=True)
class HigherExpressionID(ArenaHandle):
    """Scoped canonical higher expression."""


@dataclass(frozen=True, slots=True)
class HigherFunctionID(ArenaHandle):
    """Scoped alpha-normalized higher function."""


@dataclass(frozen=True, slots=True)
class FieldStateSort:
    action: FieldCellActionID
    side: int


@dataclass(frozen=True, slots=True)
class FieldFunctionSort:
    domain: FieldStateSort
    codomain: FieldStateSort


@dataclass(frozen=True, slots=True)
class FieldSymbolSort:
    base: int
    blank: int


@dataclass(frozen=True, slots=True)
class FieldAtomSort:
    role: str
    cardinality: int


HigherSort: TypeAlias = (
    FieldStateSort | FieldFunctionSort | FieldSymbolSort | FieldAtomSort
)
ExpressionKind: TypeAlias = Literal[
    "variable",
    "bound",
    "literal",
    "symbol",
    "constant",
    "pair",
    "anchor",
    "continuation",
    "function",
    "apply",
    "bind-free",
    "select",
    "equal-constant",
    "add-constant",
    "retag",
    "primitive-step",
    "primitive-emit",
    "action-initial",
    "action-step",
    "action-emit",
]


class HigherActionSchema(Protocol):
    @property
    def ledger(self) -> ResourceLedger: ...
    def validate_action(self, action: FieldCellActionID) -> None: ...
    def children(
        self, action: FieldCellActionID
    ) -> tuple[FieldCellActionID, FieldCellActionID] | None: ...
    def kind(
        self, action: FieldCellActionID
    ) -> Literal["identity", "primitive", "compose"]: ...
    def alphabet(self, action: FieldCellActionID) -> tuple[int, int]: ...
    def state_count(self, action: FieldCellActionID, side: int) -> int: ...
    def initial(self, action: FieldCellActionID, side: int) -> int: ...
    def step(
        self, action: FieldCellActionID, side: int, state: int, symbol: int
    ) -> int: ...
    def emit(
        self, action: FieldCellActionID, left: int, symbol: int, right: int
    ) -> int: ...


@dataclass(frozen=True, slots=True)
class HigherExpression:
    kind: ExpressionKind
    sort: HigherSort
    children: tuple[int, ...] = ()
    action: FieldCellActionID | None = None
    side: int = -1
    value: int = -1
    role: str = ""
    function: HigherFunctionID | None = None


@dataclass(frozen=True, slots=True)
class HigherFunction:
    signature: FieldFunctionSort
    parameter: HigherExpressionID
    body: HigherExpressionID
    free_variables: tuple[HigherExpressionID, ...]
    parameter_used: bool


@dataclass(frozen=True, slots=True)
class HigherSemanticMetrics:
    expressions: int
    functions: int
    expression_hits: int
    function_hits: int
    substitutions: int
    evaluations: int
    evaluation_workspace_peak: int


@dataclass(frozen=True, slots=True)
class _Rewrite:
    root: int
    variable: int
    replacement: int
