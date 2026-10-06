"""Semantic contract marker for canonical primitive tile kernels."""

from number_compiler.arithmetic.functions.finite_port_action import PortVariable

TILE_KERNEL_CONTRACT = (
    "primitive-canonical-tile-v1",
    "two-sided-boundary-transfer",
    "leaf-output-or-left-edge-output",
    "bounded-child-activity-and-edge-halos",
    "exact-interval-output-owned-by-completed-tile",
)
TILE_LEFT = PortVariable(0, 0, "tile-left", 0)
TILE_RIGHT = PortVariable(0, 1, "tile-right", 0)

__all__ = ["TILE_KERNEL_CONTRACT", "TILE_LEFT", "TILE_RIGHT"]
