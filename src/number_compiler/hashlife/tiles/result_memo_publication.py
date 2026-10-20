"""Typed read and reserved-publication boundary for completed result stores."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import replace
from types import MappingProxyType
from typing import Protocol, TypeVar

from number_compiler.hashlife.tiles.tile_result_records import (
    BoundaryConcatResult,
    CompletedBehaviorClassification,
    CompletedInterfaceResult,
    FusedVariantKey,
    NormalizedRegionResult,
    ResultVariantKey,
    RootMatchResult,
)
from number_compiler.hashlife.tiles.tile_result_types import (
    ExecutionValue,
    MemoKey,
    ReverseKey,
    ReverseValue,
)
from number_compiler.resources.stores import LedgerDict

_IssuedResult = TypeVar(
    "_IssuedResult",
    RootMatchResult,
    NormalizedRegionResult,
    BoundaryConcatResult,
    CompletedInterfaceResult,
    CompletedBehaviorClassification,
)


class ResultMemoPublication(Protocol):
    """The result owner retains stores; callers retain reservation journals."""

    _interface_publication_seal: object
    _memo: LedgerDict[MemoKey, ExecutionValue]
    _reverse: LedgerDict[ReverseKey, ReverseValue]
    _variants: LedgerDict[ResultVariantKey | FusedVariantKey, int]
    _memo_owner: int
    _reverse_owner: int
    _variant_owner: int

    def issued_result(
        self,
        value: RootMatchResult
        | NormalizedRegionResult
        | BoundaryConcatResult
        | CompletedInterfaceResult
        | CompletedBehaviorClassification,
    ) -> bool:
        return value.issued_by(self._interface_publication_seal)

    def seal_result(
        self, value: _IssuedResult, snapshot: tuple[object, ...]
    ) -> _IssuedResult:
        return replace(
            value,
            _publication_owner=self._interface_publication_seal,
            _publication_snapshot=snapshot,
        )

    @property
    def memo_view(self) -> Mapping[MemoKey, ExecutionValue]:
        return MappingProxyType(self._memo)

    @property
    def reverse_view(self) -> Mapping[ReverseKey, ReverseValue]:
        return MappingProxyType(self._reverse)

    @property
    def variant_counts(self) -> Mapping[ResultVariantKey | FusedVariantKey, int]:
        return MappingProxyType(self._variants)

    @property
    def memo_owner(self) -> int:
        return self._memo_owner

    @property
    def reverse_owner(self) -> int:
        return self._reverse_owner

    @property
    def variant_owner(self) -> int:
        return self._variant_owner

    def write_memo_reserved(self, key: MemoKey, value: ExecutionValue) -> None:
        """Publish after the caller reserves and journals the complete change."""
        self._memo[key] = value

    def discard_memo(self, key: MemoKey) -> ExecutionValue | None:
        return self._memo.pop(key, None)

    def write_reverse(self, key: ReverseKey, value: ReverseValue) -> None:
        """Single fault-injection boundary for reverse-index publication."""
        self._reverse[key] = value

    def discard_reverse(self, key: ReverseKey) -> ReverseValue | None:
        return self._reverse.pop(key, None)

    def write_variant(
        self, key: ResultVariantKey | FusedVariantKey, count: int
    ) -> None:
        self._variants[key] = count

    def discard_variant(self, key: ResultVariantKey | FusedVariantKey) -> int | None:
        return self._variants.pop(key, None)
