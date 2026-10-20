"""Bounded reverse-interface observation shared by cold and completed evidence."""

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.behavior.reverse_bound_output import ReverseBoundOutput
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.execution.tile_causal_interfaces import (
    CausalInterfacePayload,
)
from number_compiler.hashlife.tiles.tiles import TileID


def reverse_interface_payload(
    engine: CausalTileEngine,
    action: FieldCellActionID,
    tile: TileID,
) -> CausalInterfacePayload:
    payload = engine.reverse_interface(
        action,
        tile,
        engine.initial_state(action, 0),
        engine.initial_state(action, 1),
    )
    assert type(payload) is CausalInterfacePayload
    assert type(payload.bound_reverse_output) is ReverseBoundOutput
    return payload
