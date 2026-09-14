"""Fixed execution-family interface consumed by the shared tile scheduler."""

from __future__ import annotations

from typing import Protocol

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.interfaces.diamond_quotient import LocalInterfaceID
from number_compiler.hashlife.tiles.tile_context import (
    ChildContext,
    PrimitiveTileResult,
    ResultSemantics,
    TemporalCocycle,
)
from number_compiler.hashlife.tiles.tile_ports import ResultWiring
from number_compiler.hashlife.tiles.tile_result_records import CompletedResult
from number_compiler.hashlife.tiles.tiles import TileID


class TileExecutionAdapter(Protocol):
    """Fixed-interface family law consumed by the shared scheduler."""

    complete_via_midpoint_tiles: bool

    def validate_action(self, action: FieldCellActionID) -> None: ...

    def validate_wiring(
        self,
        action: FieldCellActionID,
        wiring: ResultWiring,
    ) -> None: ...

    def action_children(
        self,
        action: FieldCellActionID,
    ) -> tuple[FieldCellActionID, FieldCellActionID] | None: ...

    def action_cocycle(self, action: FieldCellActionID) -> TemporalCocycle: ...

    def leaf_observation(
        self,
        action: FieldCellActionID,
        source: TileID,
        interface: LocalInterfaceID,
        ports: tuple[int, ...],
    ) -> TemporalCocycle: ...

    def leaf_interface(
        self,
        action: FieldCellActionID,
        source: TileID,
        wiring: ResultWiring,
    ) -> LocalInterfaceID: ...

    def apply_leaf(
        self,
        interface: LocalInterfaceID,
        ports: tuple[int, ...],
    ) -> PrimitiveTileResult: ...

    def child_context(
        self,
        action: FieldCellActionID,
        parent: TileID,
        left: TileID,
        right: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
        side: int,
    ) -> ChildContext: ...

    def join_semantics(
        self,
        action: FieldCellActionID,
        parent: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
        left: CompletedResult,
        right: CompletedResult,
    ) -> ResultSemantics: ...

    def temporal_before_context(
        self,
        action: FieldCellActionID,
        before: FieldCellActionID,
        original_ports: tuple[int, ...],
        wiring: ResultWiring,
    ) -> ChildContext: ...

    def temporal_after_context(
        self,
        action: FieldCellActionID,
        after: FieldCellActionID,
        before_result: CompletedResult,
        original_ports: tuple[int, ...],
        wiring: ResultWiring,
    ) -> ChildContext: ...

    def temporal_semantics(
        self,
        action: FieldCellActionID,
        before: CompletedResult,
        after: CompletedResult,
        original_ports: tuple[int, ...],
        wiring: ResultWiring,
    ) -> ResultSemantics: ...

    def output_active(
        self,
        action: FieldCellActionID,
        source: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
    ) -> bool: ...


__all__ = ["TileExecutionAdapter"]
