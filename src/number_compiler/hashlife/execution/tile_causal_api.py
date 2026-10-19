"""Public lease-scoped operations for the causal tile task engine."""

from __future__ import annotations

from typing import TYPE_CHECKING, Protocol

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.causal_frames import (
    CausalTaskFrame,
    ChildStatesFrame,
    InterfaceFrame,
    OutputFrame,
    PointFrame,
)
from number_compiler.hashlife.execution.tile_causal_behavior import quiescent_boundary
from number_compiler.hashlife.execution.tile_causal_interfaces import (
    CausalInterfacePayload,
)
from number_compiler.hashlife.execution.tile_causal_observation import causal_width
from number_compiler.hashlife.execution.tile_causal_results import (
    PrimitiveCausalPorts,
    lookup_causal_result,
    probe_causal_result,
)
from number_compiler.hashlife.execution.tile_causal_tasks import (
    bound_states,
)
from number_compiler.hashlife.tiles.tile_boundaries import BoundaryTileView
from number_compiler.hashlife.tiles.tile_ports import (
    FusedBoundaryContract,
    ResultWiring,
)
from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
from number_compiler.hashlife.tiles.tile_results import ResultLease
from number_compiler.hashlife.tiles.tiles import TileArena, TileID, TileLease
from number_compiler.resources.causal_types import (
    CausalChildStates,
    CausalPrefix,
    CausalState,
    CausalTaskValue,
    require_child_states,
)
from number_compiler.resources.causal_workspace import CausalActionAdmission
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)

CausalRunResult = CausalTaskValue | ResultLease | TileLease

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler


class CausalTileAPI(Protocol):
    """Mixin; the concrete engine supplies the single iterative ``_run``."""

    scheduler: TileScheduler
    tiles: TileArena
    adapter: PrimitiveTileKernelAdapter
    ledger: ResourceLedger
    _application: int | None
    _hold_workspace: bool

    @property
    def action_admission(self) -> CausalActionAdmission | None: ...

    def _run(
        self,
        root: CausalTaskFrame,
        *,
        tile_result: bool,
        return_result: bool = False,
    ) -> CausalRunResult: ...

    def _initial(
        self,
        action: FieldCellActionID,
        side: int,
        seed: int | None = None,
    ) -> int | CausalPrefix: ...

    def initial_state(
        self,
        action: FieldCellActionID,
        side: int,
        seed: int | None = None,
    ) -> int | CausalPrefix:
        """Return the admitted initial boundary state for one action side."""
        return self._initial(action, side, seed)

    def _children(
        self,
        action: FieldCellActionID,
    ) -> tuple[FieldCellActionID, FieldCellActionID] | None: ...

    def _composite_key(
        self,
        action: FieldCellActionID,
        tile: TileID,
        left: CausalState,
        right: CausalState,
    ) -> PoweredResultKey | None: ...

    def _wiring(self, action: FieldCellActionID) -> ResultWiring: ...

    def _release_workspace(self) -> None: ...

    def output(self, action: FieldCellActionID, tile: TileID) -> TileLease:
        result = self._run(
            OutputFrame(
                (action, tile, self._initial(action, 0), self._initial(action, 1)),
            ),
            tile_result=True,
        )
        if type(result) is not TileLease:
            raise AssertionError("causal output returned another lease sort")
        return result

    def point(
        self,
        action: FieldCellActionID,
        tile: TileID,
        coordinate: int,
        *,
        application: int | None = None,
    ) -> int:
        self._application = application
        value = self._run(
            PointFrame(
                (
                    action,
                    tile,
                    coordinate,
                    self._initial(action, 0),
                    self._initial(action, 1),
                ),
            ),
            tile_result=False,
        )
        if type(value) is not int:
            raise AssertionError("causal point returned another scalar sort")
        return value

    def point_bound(
        self,
        action: FieldCellActionID,
        tile: TileID,
        coordinate: int,
        contract: FusedBoundaryContract,
        *,
        application: int | None = None,
    ) -> int:
        left, right = bound_states(
            self.adapter,
            self.scheduler.results,
            action,
            tile,
            contract,
        )
        self._application = application
        value = self._run(
            PointFrame(
                (
                    action,
                    tile,
                    coordinate,
                    left,
                    right,
                ),
            ),
            tile_result=False,
        )
        if type(value) is not int:
            raise AssertionError("bound causal point returned another scalar sort")
        return value

    def output_bound(
        self,
        action: FieldCellActionID,
        tile: TileID,
        contract: FusedBoundaryContract,
    ) -> ResultLease:
        left, right = bound_states(
            self.adapter,
            self.scheduler.results,
            action,
            tile,
            contract,
        )
        result = self._run(
            OutputFrame(
                (action, tile, left, right),
            ),
            tile_result=True,
            return_result=True,
        )
        if type(result) is not ResultLease:
            raise AssertionError("bound causal output returned another result sort")
        return result

    def interface(
        self,
        action: FieldCellActionID,
        tile: TileID,
        left: CausalState,
        right: CausalState,
        *,
        application: int | None = None,
    ) -> CausalInterfacePayload:
        if application is not None:
            self._application = application
        result = self._run(
            InterfaceFrame(
                (action, tile, left, right),
            ),
            tile_result=False,
        )
        if type(result) is not CausalInterfacePayload:
            raise AssertionError("causal interface returned another payload sort")
        return result

    def child_states(
        self,
        action: FieldCellActionID,
        parent: TileID,
        left: CausalState,
        right: CausalState,
    ) -> CausalChildStates:
        result = self._run(
            ChildStatesFrame(
                (action, parent, left, right),
            ),
            tile_result=False,
        )
        try:
            return require_child_states(result)
        except TypeError as error:
            raise AssertionError(
                "causal child states returned another shape"
            ) from error

    def width(
        self,
        action: FieldCellActionID,
        tile: TileID,
        *,
        limit: int,
        application: int | None = None,
        contract: FusedBoundaryContract | None = None,
    ) -> int:
        if contract is None:
            left, right = self._initial(action, 0), self._initial(action, 1)
        else:
            left, right = bound_states(
                self.adapter,
                self.scheduler.results,
                action,
                tile,
                contract,
            )
        self._application = application
        try:
            key: PoweredResultKey | None
            if self._children(action) is None:
                if type(left) is not int or type(right) is not int:
                    raise TypeError(
                        "primitive causal states require exact integer ports"
                    )
                key, completed = probe_causal_result(
                    self.scheduler.results,
                    action,
                    tile,
                    PrimitiveCausalPorts(left, right),
                    self._wiring(action),
                )
            else:
                key = self._composite_key(action, tile, left, right)
                completed = (
                    None
                    if key is None
                    else lookup_causal_result(self.scheduler.results, key)
                )
            if completed is not None:
                if key is None:
                    raise AssertionError("completed causal result has no request key")
                try:
                    with completed:
                        self.ledger.bump(
                            _execution_keys.TILE_CAUSAL_INTERFACE_PARENT_HITS
                        )
                        width = self.tiles.active_width(completed.output, limit)
                        if type(width) is not int:
                            raise TypeError(
                                "canonical tile width returned another sort"
                            )
                        return width
                finally:
                    self._application = None
            node = self.tiles.resolve(tile)
            if type(limit) is not int or not 0 <= limit <= node.width:
                self._application = None
                raise ValueError(
                    "causal width limit requires an exact in-range integer"
                )
            if not limit:
                self._application = None
                return 0
            if (
                node.first_active is None
                and quiescent_boundary(
                    self,
                    action,
                    0,
                    BoundaryTileView(tile, 0, node.width),
                    left,
                    right,
                    discharged_extent=limit,
                )
                is not None
            ):
                self._application = None
                self.ledger.bump(_execution_keys.BEHAVIOR_WIDTH_OBSERVATIONS)
                return 0
            self._hold_workspace = True
            try:
                from number_compiler.hashlife.interfaces.tile_reverse_sector_functions import (
                    reverse_sector_width_from_interface,
                    supports_reverse_sector_width,
                )

                if contract is None and supports_reverse_sector_width(
                    self.adapter, action
                ):
                    payload = self.interface(action, tile, left, right)
                    sector_width = reverse_sector_width_from_interface(
                        self.adapter, action, tile, payload, limit
                    )
                    if sector_width is not None:
                        return sector_width
                return causal_width(
                    self,
                    action,
                    tile,
                    left,
                    right,
                    limit=limit,
                )
            finally:
                self._hold_workspace = False
                self._release_workspace()
        finally:
            self._application = None


__all__ = ["CausalTileAPI"]
