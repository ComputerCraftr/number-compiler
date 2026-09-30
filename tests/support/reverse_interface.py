"""Bounded reverse-interface observation shared by cold and completed evidence."""

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.behavior.reverse_bound_output import ReverseBoundOutput
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.execution.tile_causal_interfaces import (
    CausalInterfacePayload,
)
from number_compiler.hashlife.execution.tile_causal_tasks import CausalFrame
from number_compiler.hashlife.tiles.tiles import TileID


def reverse_interface_payload(
    engine: CausalTileEngine,
    action: FieldCellActionID,
    tile: TileID,
) -> CausalInterfacePayload:
    payload = engine._run(
        CausalFrame(
            "reverse_interface",
            (action, tile, engine._initial(action, 0), engine._initial(action, 1)),
        ),
        tile_result=False,
    )
    assert type(payload) is CausalInterfacePayload
    assert type(payload.bound_reverse_output) is ReverseBoundOutput
    return payload
