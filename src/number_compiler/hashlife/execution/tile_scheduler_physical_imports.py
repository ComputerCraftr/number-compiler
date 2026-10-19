"""Physical dependencies loaded only by physical tile scheduler operations."""

from number_compiler.hashlife.execution.tile_application_authority import (
    TileApplicationRegistry,
    application_by_id,
    application_source,
)
from number_compiler.hashlife.execution.tile_causal_interfaces import (
    interface_payload_from_completed,
)
from number_compiler.hashlife.execution.tile_clock_dispatch import complete_clock
from number_compiler.hashlife.execution.tile_execution_adapter import (
    TileExecutionAdapter,
)
from number_compiler.hashlife.interfaces.semantic_structures import LocalInterfaceID
from number_compiler.hashlife.tiles.ordered_boolean_support import (
    OrderedBooleanSupportArena,
)
from number_compiler.hashlife.tiles.tile_context import (
    ChildContext,
    PrimitiveTileResult,
    ResultSemantics,
    TemporalCocycle,
    after_context,
    before_context,
    bind_context,
    temporal_result,
    validate_midpoint_exits,
)
from number_compiler.hashlife.tiles.tile_ports import BoundPorts
from number_compiler.hashlife.tiles.tile_result_records import (
    CompletedResult,
    PoweredResultKey,
)
from number_compiler.hashlife.tiles.tile_result_validation import (
    normalize_output_region,
)
from number_compiler.hashlife.tiles.tile_results import (
    CompletedResultArena,
    ResultLease,
)
from number_compiler.hashlife.tiles.tiles import TileArena
from number_compiler.resources.causal_workspace import (
    CausalSpatialWorkspace,
    CausalTaskWorkspace,
)
from number_compiler.resources.tile_dependency_leases import TileDependencyLeases

__all__ = [
    "BoundPorts",
    "CausalSpatialWorkspace",
    "CausalTaskWorkspace",
    "ChildContext",
    "CompletedResult",
    "CompletedResultArena",
    "LocalInterfaceID",
    "OrderedBooleanSupportArena",
    "PoweredResultKey",
    "PrimitiveTileResult",
    "ResultLease",
    "ResultSemantics",
    "TemporalCocycle",
    "TileApplicationRegistry",
    "TileArena",
    "TileDependencyLeases",
    "TileExecutionAdapter",
    "after_context",
    "application_by_id",
    "application_source",
    "before_context",
    "bind_context",
    "complete_clock",
    "interface_payload_from_completed",
    "normalize_output_region",
    "temporal_result",
    "validate_midpoint_exits",
]
