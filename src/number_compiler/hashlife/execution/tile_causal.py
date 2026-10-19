"""Store-free iterative causal recurrence over exact boundary tile operands."""

from __future__ import annotations

from collections.abc import Callable
from functools import partial
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.causal_frames import (
    AdvanceFrame,
    AdvanceSymbolFrame,
    AnchorFrame,
    CausalTaskFrame,
    ChildStatesFrame,
    EmitFrame,
    ExactReverseOutputFrame,
    InterfaceEmitFrame,
    InterfaceFrame,
    MemoDoneFrame,
    OutputBoundaryFrame,
    OutputChunkListFrame,
    OutputFrame,
    PointFrame,
    PromoteMidpointFrame,
    ResidualFrame,
    ReverseBoundaryFrame,
    ReverseInterfaceFrame,
    ScanChunksFrame,
    SourceRootMatchFrame,
)
from number_compiler.hashlife.execution.reverse_active_transfer import (
    consume_reverse_bound_output,
)
from number_compiler.hashlife.execution.tile_causal_admission import (
    admit_run_actions,
    admitted_children,
    admitted_cocycle,
    admitted_kernel,
    admitted_wiring,
)
from number_compiler.hashlife.execution.tile_causal_api import (
    CausalRunResult,
    CausalTileAPI,
)
from number_compiler.hashlife.execution.tile_causal_behavior import quiescent_boundary
from number_compiler.hashlife.execution.tile_causal_boundary_step import (
    boundary_step,
    probe_boundary_result,
)
from number_compiler.hashlife.execution.tile_causal_emit import emit_step
from number_compiler.hashlife.execution.tile_causal_interface_step import interface_step
from number_compiler.hashlife.execution.tile_causal_midpoint import cached_midpoint_step
from number_compiler.hashlife.execution.tile_causal_pair_transfer import (
    finite_pair_transfer,
)
from number_compiler.hashlife.execution.tile_causal_point import point_step
from number_compiler.hashlife.execution.tile_causal_promotion import promotion_step
from number_compiler.hashlife.execution.tile_causal_results import (
    CausalCompletedOutput,
    PrimitiveCausalPorts,
    lookup_causal_result,
    probe_causal_result,
)
from number_compiler.hashlife.execution.tile_causal_tasks import (
    append_prefix,
    combine_spatial_outputs,
    composite_result_key,
    covered_chunks,
    primitive_advance,
    publish_composite_output,
    retain_completed,
)
from number_compiler.hashlife.execution.tile_reverse_boundary import (
    reverse_boundary_step,
    supports_reverse_boundary,
)
from number_compiler.hashlife.tiles.tile_boundaries import (
    BoundaryTileView,
)
from number_compiler.hashlife.tiles.tile_region_memo import normalize_cached_region
from number_compiler.hashlife.tiles.tile_result_leases import tile_lease_was_released
from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
from number_compiler.hashlife.tiles.tile_results import ResultLease
from number_compiler.hashlife.tiles.tiles import TileID, TileLease
from number_compiler.resources.causal_types import (
    CausalPrefix as _Prefix,
)
from number_compiler.resources.causal_types import (
    CausalState,
    CausalTaskValue,
)
from number_compiler.resources.causal_types import (
    pop_boundary_view as _pop_boundary_view,
)
from number_compiler.resources.causal_types import (
    pop_causal_state as _pop_causal_state,
)
from number_compiler.resources.causal_types import (
    pop_completed_output as _pop_completed_output,
)
from number_compiler.resources.causal_types import (
    pop_reverse_bound_output as _pop_reverse_bound_output,
)
from number_compiler.resources.causal_workspace import CausalActionAdmission
from number_compiler.resources.lifecycle import cleanup_all
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
    from number_compiler.hashlife.interfaces.diamond_kernel import PrimitiveKernel
    from number_compiler.hashlife.tiles.tile_context import TemporalCocycle
    from number_compiler.hashlife.tiles.tile_ports import ResultWiring


class CausalTileEngine(CausalTileAPI):
    def __init__(self, scheduler: TileScheduler) -> None:
        from number_compiler.hashlife.execution.tile_kernel import (
            PrimitiveTileKernelAdapter,
        )

        if type(scheduler.adapter) is not PrimitiveTileKernelAdapter:
            raise TypeError(
                "causal tile execution requires the verified primitive adapter"
            )
        self.scheduler = scheduler
        self.tiles = scheduler.tiles
        self.adapter: PrimitiveTileKernelAdapter = scheduler.adapter
        self.ledger = scheduler.ledger
        self._leases: list[TileLease] = []
        self._result_leases: list[ResultLease] = []
        self._application: int | None = None
        self._hold_workspace = False
        self._action_admission_token: CausalActionAdmission | None = None
        self._running = False
        self._workspace_memo = scheduler._causal_tasks.memo
        self._workspace_active = scheduler._causal_tasks.active

    @property
    def action_admission(self) -> CausalActionAdmission | None:
        """Expose the current run lease to checked causal helper operations."""
        return self._action_admission_token

    def _children(
        self,
        action: FieldCellActionID,
    ) -> tuple[FieldCellActionID, FieldCellActionID] | None:
        return admitted_children(
            self.adapter,
            self.scheduler._causal_tasks,
            self._action_admission_token,
            action,
        )

    def _law(self, action: FieldCellActionID) -> PrimitiveKernel:
        return admitted_kernel(
            self.adapter,
            self.scheduler._causal_tasks,
            self._action_admission_token,
            action,
        )

    def _cocycle(self, action: FieldCellActionID) -> TemporalCocycle:
        return admitted_cocycle(
            self.adapter,
            self.scheduler._causal_tasks,
            self._action_admission_token,
            action,
        )

    def _wiring(self, action: FieldCellActionID) -> ResultWiring:
        return admitted_wiring(
            self.adapter,
            self.scheduler._causal_tasks,
            self._action_admission_token,
            action,
        )

    def _admit_run_actions(self, action: FieldCellActionID) -> CausalActionAdmission:
        return admit_run_actions(
            self.adapter, self.scheduler._causal_tasks, self.ledger, action
        )

    def _release_run_action_admission(self) -> None:
        token = self._action_admission_token
        self._action_admission_token = None
        if token is not None:
            self.scheduler._causal_tasks.clear_action_admission(token)

    def _initial(
        self,
        action: FieldCellActionID,
        side: int,
        seed: int | None = None,
    ) -> int | _Prefix:
        children = self._children(action)
        if children is None:
            return self._initial_port(action, side) if seed is None else seed
        before, after = children
        producer = self._initial_port(before, side)
        consumer = self._initial_port(after, side) if seed is None else seed
        return _Prefix(action, side, producer, consumer)

    def _initial_port(self, action: FieldCellActionID, side: int) -> int:
        if self._action_admission_token is not None:
            return self._law(action).initial(BoundarySide(side))
        return self.adapter.initial_ports(action)[side]

    def _keep(self, lease: TileLease) -> TileID:
        self._leases.append(lease)
        return lease.tile

    def _composite_key(
        self,
        action: FieldCellActionID,
        tile: TileID,
        left: CausalState,
        right: CausalState,
    ) -> PoweredResultKey | None:
        return composite_result_key(
            self.adapter,
            self.scheduler.results,
            action,
            tile,
            left,
            right,
            action_admission=self._action_admission_token,
        )

    def _covered_chunks(self, view: BoundaryTileView) -> tuple[TileID, ...]:
        return covered_chunks(self.tiles, self._leases, view)

    def _append_prefix(self, state: _Prefix, view: BoundaryTileView) -> _Prefix:
        return append_prefix(
            self.adapter,
            self.tiles,
            self._leases,
            state,
            view,
            results=self.scheduler.results,
            dependencies=(
                self.scheduler._causal_dependencies
                if self._application is not None
                else None
            ),
            application=self._application,
        )

    def _release_workspace(self) -> None:
        pair_transfer = self.adapter.pair_transfer
        failed_results: list[ResultLease] = []
        failed_tiles: list[TileLease] = []
        cleanups: list[Callable[[], object]] = []

        if pair_transfer is not None:
            cleanups.append(pair_transfer.clear_bindings)

        def close_result(result: ResultLease) -> None:
            try:
                result.close()
            except BaseException:
                failed_results.append(result)
                raise

        def close_tile(lease: TileLease) -> None:
            try:
                lease.close()
            except BaseException:
                if not tile_lease_was_released(lease):
                    failed_tiles.append(lease)
                else:
                    lease._closed = True
                raise

        cleanups.extend(
            partial(close_result, result) for result in reversed(self._result_leases)
        )
        cleanups.extend(partial(close_tile, lease) for lease in reversed(self._leases))
        cleanups.extend(
            (self.scheduler._causal_workspace.clear, self.scheduler._causal_tasks.clear)
        )
        cleanups.append(self.scheduler.results._retry_pending_acquisition_leases)
        try:
            cleanup_all(cleanups)
        finally:
            self._result_leases = failed_results
            self._leases = failed_tiles
            self._application = None
            if (
                self.scheduler._causal_tasks._action_admission_token is None
                and self.scheduler._causal_tasks._issued_action_admission_token is None
            ):
                self._action_admission_token = None

    def _run(
        self,
        root: CausalTaskFrame,
        *,
        tile_result: bool,
        return_result: bool = False,
    ) -> CausalRunResult:
        if self._running:
            raise RuntimeError("causal tile engine cannot reenter an active run")
        frames = self.scheduler._causal_tasks.frames
        values = self.scheduler._causal_tasks.values
        memo = self._workspace_memo
        active = self._workspace_active
        run_token = self.scheduler._causal_tasks.begin_run()
        self._running = True
        try:
            match root:
                case ExactReverseOutputFrame():
                    pass
                case MemoDoneFrame() | SourceRootMatchFrame():
                    raise TypeError("causal recurrence root is an internal task")
                case _:
                    self._action_admission_token = self._admit_run_actions(root.args[0])
            frames.append(root)
            while frames:
                peak = len(frames) + len(values) + len(memo) + len(active)
                old = self.ledger.counters.get(
                    _execution_keys.TILE_CAUSAL_WORKSPACE_PEAK, 0
                )
                if peak > old:
                    self.ledger.bump(
                        _execution_keys.TILE_CAUSAL_WORKSPACE_PEAK,
                        peak - old,
                    )
                frame = frames.pop()
                op = frame.op
                self.ledger.bump(_execution_keys.TILE_CAUSAL_FRAMES)
                if isinstance(frame, MemoDoneFrame):
                    (key,) = frame.args
                    if key not in active or not values:
                        raise AssertionError(
                            "causal memo completion lost its dependency"
                        )
                    value = values.pop()
                    self.scheduler._causal_tasks.finish(key, value)
                    values.append(value)
                    self.ledger.bump(_execution_keys.TILE_CAUSAL_TASK_MEMO_PUBLICATIONS)
                    continue
                if (
                    isinstance(
                        frame,
                        (
                            AdvanceFrame,
                            AnchorFrame,
                            EmitFrame,
                            ResidualFrame,
                            OutputFrame,
                            OutputBoundaryFrame,
                            InterfaceFrame,
                            ReverseInterfaceFrame,
                            InterfaceEmitFrame,
                            ChildStatesFrame,
                        ),
                    )
                    and frame.stage == 0
                    and not frame.memoized
                ):
                    if isinstance(frame, OutputBoundaryFrame):
                        (
                            boundary_action,
                            boundary_side,
                            boundary_view,
                            boundary_anchor,
                            boundary_argument,
                        ) = frame.args
                        dependencies = (
                            self.scheduler._causal_dependencies
                            if self._application is not None
                            else None
                        )
                        normalized, lease = normalize_cached_region(
                            self.scheduler.results,
                            boundary_view,
                            dependencies=dependencies,
                            application=self._application,
                        )
                        self._leases.append(lease)
                        frame.args = (
                            boundary_action,
                            boundary_side,
                            normalized,
                            boundary_anchor,
                            boundary_argument,
                        )
                    elif isinstance(frame, AdvanceFrame):
                        advance_action, advance_side, advance_state, advance_view = (
                            frame.args
                        )
                        if type(advance_view) is not BoundaryTileView:
                            raise TypeError("advance frame requires a boundary view")
                        advance_view.__post_init__()
                        if advance_view.relative_origin:
                            advance_view = BoundaryTileView(
                                advance_view.tile,
                                0,
                                advance_view.relative_extent,
                                advance_view.orientation,
                                advance_view.source_offset,
                            )
                            frame.args = (
                                advance_action,
                                advance_side,
                                advance_state,
                                advance_view,
                            )
                    memo_key = (frame.op, frame.args)
                    counter = "tile_causal_" + (
                        "boundary_output"
                        if isinstance(frame, OutputBoundaryFrame)
                        else op
                    )
                    self.ledger.bump(counter + "_requests")
                    if isinstance(frame, OutputBoundaryFrame):
                        self.ledger.bump(
                            counter + "_requested_extent",
                            frame.args[2].relative_extent,
                        )
                    found = memo.get(memo_key)
                    if found is not None:
                        values.append(found)
                        self.ledger.bump(_execution_keys.TILE_CAUSAL_TASK_MEMO_HITS)
                        self.ledger.bump(counter + "_hits")
                        if isinstance(frame, OutputBoundaryFrame):
                            self.ledger.bump(
                                counter + "_cached_extent",
                                frame.args[2].relative_extent,
                            )
                        continue
                    if isinstance(frame, OutputBoundaryFrame):
                        boundary = probe_boundary_result(self, frame)
                        if boundary is not None:
                            values.append(boundary)
                            self.ledger.bump(counter + "_hits")
                            self.ledger.bump(
                                counter + "_cached_extent",
                                frame.args[2].relative_extent,
                            )
                            continue
                    if memo_key in active:
                        raise ValueError("causal task dependency contains a cycle")
                    self.ledger.bump(counter + "_evaluations")
                    try:
                        self.scheduler._causal_tasks.begin(memo_key)
                    except BaseException:
                        self.ledger.bump(counter + "_failures")
                        raise
                    frame.memoized = True
                    frames.extend((MemoDoneFrame((memo_key,)), frame))
                    self.ledger.bump(_execution_keys.TILE_CAUSAL_TASK_MEMO_EVALUATIONS)
                    continue
                if isinstance(
                    frame,
                    (
                        InterfaceFrame,
                        ReverseInterfaceFrame,
                        InterfaceEmitFrame,
                        ChildStatesFrame,
                        ExactReverseOutputFrame,
                    ),
                ) and interface_step(self, frame, frames, values):
                    continue
                if isinstance(frame, ReverseBoundaryFrame) and reverse_boundary_step(
                    self, frame, frames, values
                ):
                    continue
                if isinstance(frame, PromoteMidpointFrame) and promotion_step(
                    self, frame, frames, values
                ):
                    continue
                if isinstance(frame, PointFrame) and point_step(
                    self, frame, frames, values
                ):
                    continue
                if isinstance(frame, AdvanceFrame):
                    advance_action, advance_side, advance_state, advance_view = (
                        frame.args
                    )
                    if self._children(advance_action) is None:
                        if type(advance_state) is not int:
                            raise TypeError("primitive advance requires a finite state")
                        values.append(
                            primitive_advance(
                                self.adapter,
                                advance_action,
                                advance_side,
                                advance_state,
                                advance_view,
                                action_admission=self._action_admission_token,
                            )
                        )
                    else:
                        if (
                            not isinstance(advance_state, _Prefix)
                            or advance_state.action != advance_action
                            or advance_state.side != advance_side
                        ):
                            raise ValueError(
                                "composite transfer requires its exact causal prefix"
                            )
                        values.append(self._append_prefix(advance_state, advance_view))
                    continue
                if isinstance(frame, EmitFrame):
                    emit_step(self, frame, frames, values)
                    continue
                if isinstance(frame, AdvanceSymbolFrame):
                    symbol_action, symbol_side, symbol_state, symbol = frame.args
                    if type(symbol_side) is not int or symbol_side not in (0, 1):
                        raise ValueError("symbol advance requires an exact direction")
                    if self._children(symbol_action) is None:
                        if type(symbol_state) is not int:
                            raise TypeError(
                                "primitive symbol advance requires a finite state"
                            )
                        # A primitive transition observes only the finite literal.
                        # Publishing a tile and a directed-transfer cache entry
                        # for it duplicates the admitted kernel's transition law.
                        values.append(
                            self._law(symbol_action).advance(
                                BoundarySide(symbol_side), symbol_state, symbol
                            )
                        )
                        self.ledger.bump(
                            _execution_keys.TILE_CAUSAL_DIRECT_SYMBOL_TRANSFERS
                        )
                    else:
                        if (
                            not isinstance(symbol_state, _Prefix)
                            or symbol_state.action != symbol_action
                            or symbol_state.side != symbol_side
                        ):
                            raise ValueError(
                                "composite symbol advance requires its exact causal prefix"
                            )
                        with self.tiles.leaf(
                            self.adapter.alphabet(symbol_action), symbol
                        ) as leaf:
                            values.append(
                                self._append_prefix(
                                    symbol_state,
                                    BoundaryTileView(leaf.tile, 0, 1),
                                )
                            )
                    continue
                if isinstance(frame, AnchorFrame):
                    anchor_action, anchor_side, anchor_state = frame.args
                    if not isinstance(anchor_state, _Prefix):
                        raise TypeError("anchor task requires a causal prefix")
                    if self._children(anchor_state.action) is None:
                        raise ValueError("causal prefix belongs to a primitive action")
                    if anchor_state.view is None:
                        values.append(
                            self._initial(
                                anchor_action, anchor_side, anchor_state.producer_seed
                            )
                        )
                    else:
                        frames.append(
                            AdvanceFrame(
                                (
                                    anchor_action,
                                    anchor_side,
                                    self._initial(
                                        anchor_action,
                                        anchor_side,
                                        anchor_state.producer_seed,
                                    ),
                                    anchor_state.view,
                                )
                            )
                        )
                    continue
                if isinstance(frame, ResidualFrame):
                    composite, side, prefix, argument = frame.args
                    if not isinstance(prefix, _Prefix):
                        raise TypeError("residual task requires a causal prefix")
                    children = self._children(composite)
                    if children is None:
                        raise TypeError("residual requires a composite action")
                    before, after = children
                    consumer_state = self._initial(
                        after,
                        side,
                        prefix.consumer_seed,
                    )
                    if prefix.consumer_view is not None and frame.stage == 0:
                        frame.stage = -1
                        frames.extend(
                            (
                                frame,
                                AdvanceFrame(
                                    (
                                        after,
                                        side,
                                        consumer_state,
                                        prefix.consumer_view,
                                    ),
                                ),
                            )
                        )
                        continue
                    if frame.stage == -1:
                        consumer_state = _pop_causal_state(values)
                        frame.stage = 0
                        frame.saved = (consumer_state,)
                    elif frame.saved:
                        match frame.saved:
                            case (saved_state,):
                                consumer_state = saved_state
                            case _:
                                raise AssertionError(
                                    "causal residual lost its consumer state"
                                )
                    if prefix.view is None:
                        values.append(consumer_state)
                        continue
                    if frame.stage == 0:
                        blank = quiescent_boundary(
                            self,
                            before,
                            side,
                            prefix.view,
                            self._initial(before, side, prefix.producer_seed),
                            argument,
                        )
                        if blank is not None:
                            frames.append(
                                AdvanceFrame(
                                    (
                                        after,
                                        side,
                                        consumer_state,
                                        blank,
                                    ),
                                )
                            )
                            continue
                        finite = finite_pair_transfer(
                            self, composite, side, prefix, argument, consumer_state
                        )
                        if finite is not None:
                            values.append(finite)
                            continue
                        if supports_reverse_boundary(
                            self,
                            before,
                            after,
                            consumer_state,
                            side,
                            prefix.view,
                            self._initial(before, side, prefix.producer_seed),
                            argument,
                        ):
                            frame.stage, frame.saved = 2, (consumer_state,)
                            frames.extend(
                                (
                                    frame,
                                    ReverseBoundaryFrame(
                                        (
                                            before,
                                            side,
                                            prefix.view,
                                            self._initial(
                                                before, side, prefix.producer_seed
                                            ),
                                            argument,
                                        ),
                                    ),
                                )
                            )
                            continue
                        frame.stage = 1
                        frame.saved = (consumer_state,)
                        frames.extend(
                            (
                                frame,
                                OutputBoundaryFrame(
                                    (
                                        before,
                                        side,
                                        prefix.view,
                                        self._initial(
                                            before,
                                            side,
                                            prefix.producer_seed,
                                        ),
                                        argument,
                                    ),
                                ),
                            )
                        )
                        continue
                    if frame.stage == 2:
                        produced = _pop_reverse_bound_output(values)
                        if type(consumer_state) is not int:
                            raise TypeError(
                                "reverse output transfer requires a finite consumer"
                            )
                        consumed = consume_reverse_bound_output(
                            self.adapter, after, side, consumer_state, produced
                        )
                        if consumed is None:
                            raise ValueError(
                                "admitted reverse boundary lost its consumer"
                            )
                        self.ledger.bump(
                            _execution_keys.REVERSE_BOUNDARY_EXTENT_DISCHARGED,
                            prefix.view.relative_extent,
                        )
                        values.append(consumed)
                        continue
                    produced_view = _pop_boundary_view(values)
                    frames.append(
                        AdvanceFrame(
                            (
                                after,
                                side,
                                consumer_state,
                                produced_view,
                            ),
                        )
                    )
                    continue
                if isinstance(
                    frame, (ScanChunksFrame, OutputChunkListFrame, OutputBoundaryFrame)
                ) and boundary_step(self, frame, frames, values):
                    continue
                if isinstance(frame, OutputFrame):
                    output_action, output_tile, output_left, output_right = frame.args
                    children = self._children(output_action)
                    if (
                        frame.stage == 0
                        and children is None
                        and type(output_left) is int
                        and type(output_right) is int
                    ):
                        wiring = self._wiring(output_action)
                        result_key, completed = probe_causal_result(
                            self.scheduler.results,
                            output_action,
                            output_tile,
                            PrimitiveCausalPorts(output_left, output_right),
                            wiring,
                            action_admission=self._action_admission_token,
                        )
                        if completed is None:
                            completed = self.scheduler._complete_direct(result_key)
                            self.ledger.bump(
                                _execution_keys.TILE_CAUSAL_RESULT_EVALUATIONS
                            )
                        else:
                            self.ledger.bump(_execution_keys.TILE_CAUSAL_RESULT_HITS)
                        payload = retain_completed(self, result_key, completed)
                        values.append(payload)
                        continue
                    if frame.stage == 0 and children is not None:
                        composite_result_key = self._composite_key(
                            output_action,
                            output_tile,
                            output_left,
                            output_right,
                        )
                        if composite_result_key is not None:
                            completed = lookup_causal_result(
                                self.scheduler.results,
                                composite_result_key,
                                action_admission=self._action_admission_token,
                            )
                            if completed is not None:
                                payload = retain_completed(
                                    self, composite_result_key, completed
                                )
                                self.ledger.bump(
                                    _execution_keys.TILE_CAUSAL_RESULT_HITS
                                )
                                values.append(payload)
                                continue
                    if children is not None and cached_midpoint_step(
                        self,
                        frame,
                        frames,
                        values,
                        output_action,
                        output_tile,
                        output_left,
                        output_right,
                        children,
                    ):
                        continue
                    node = self.tiles.resolve(output_tile)
                    if not node.level:
                        if node.symbol is None:
                            raise ValueError("malformed tile leaf")
                        if frame.stage == 0:
                            frame.stage = 1
                            frames.extend(
                                (
                                    frame,
                                    EmitFrame(
                                        (
                                            output_action,
                                            output_left,
                                            node.symbol,
                                            output_right,
                                        )
                                    ),
                                )
                            )
                            continue
                        payload = _pop_completed_output(values)
                        payload = publish_composite_output(
                            self,
                            output_action,
                            output_tile,
                            output_left,
                            output_right,
                            payload,
                        )
                        values.append(payload)
                        continue
                    assert node.left is not None and node.right is not None
                    if frame.stage == 0:
                        frame.stage = 1
                        frames.extend(
                            (
                                frame,
                                AdvanceFrame(
                                    (
                                        output_action,
                                        1,
                                        output_right,
                                        BoundaryTileView(
                                            node.right,
                                            0,
                                            self.tiles.resolve(node.right).width,
                                            1,
                                        ),
                                    ),
                                ),
                                AdvanceFrame(
                                    (
                                        output_action,
                                        0,
                                        output_left,
                                        BoundaryTileView(
                                            node.left,
                                            0,
                                            self.tiles.resolve(node.left).width,
                                        ),
                                    ),
                                ),
                            )
                        )
                        continue
                    if frame.stage == 1:
                        right_mid = _pop_causal_state(values)
                        left_mid = _pop_causal_state(values)
                        frame.stage, frame.saved = 2, (left_mid, right_mid)
                        frames.extend(
                            (
                                frame,
                                OutputFrame(
                                    (output_action, node.left, output_left, right_mid)
                                ),
                            )
                        )
                        continue
                    if frame.stage == 2:
                        left_out = _pop_completed_output(values)
                        match frame.saved:
                            case (left_mid, right_mid):
                                pass
                            case _:
                                raise AssertionError(
                                    "causal parent lost its midpoint states"
                                )
                        frame.stage, frame.saved = 3, (left_out, left_mid, right_mid)
                        frames.extend(
                            (
                                frame,
                                OutputFrame(
                                    (output_action, node.right, left_mid, output_right)
                                ),
                            )
                        )
                        continue
                    right_out = _pop_completed_output(values)
                    match frame.saved:
                        case (left_out, _left_mid, _right_mid):
                            pass
                        case _:
                            raise AssertionError(
                                "causal parent lost its completed left child"
                            )
                    payload = combine_spatial_outputs(
                        self, output_action, left_out, right_out
                    )
                    payload = publish_composite_output(
                        self,
                        output_action,
                        output_tile,
                        output_left,
                        output_right,
                        payload,
                    )
                    values.append(payload)
                    continue
                raise AssertionError(op)
            if len(values) != 1:
                raise AssertionError("causal recurrence returned another arity")
            token = self._action_admission_token
            if token is not None:
                self.scheduler._causal_tasks.validate_admitted_actions(
                    token, self.adapter
                )
            result: CausalTaskValue = values.pop()
            if not tile_result:
                return result
            match result:
                case CausalCompletedOutput():
                    pass
                case _:
                    raise AssertionError(
                        "causal output did not return a completed tile"
                    )
            if return_result:
                if not isinstance(root, OutputFrame):
                    raise TypeError("leased result return requires an output request")
                root_action, root_tile, root_left, root_right = root.args
                root_result_key = self._composite_key(
                    root_action, root_tile, root_left, root_right
                )
                completed = (
                    None
                    if root_result_key is None
                    else self.scheduler.results.lookup(root_result_key)
                )
                if completed is None:
                    raise AssertionError("bound causal output was not published")
                return completed
            return self.tiles.retain(result.output)
        except BaseException:
            for failed_op, _failed_args in active:
                failed_prefix = (
                    "boundary_output" if failed_op == "output_boundary" else failed_op
                )
                self.ledger.bump("tile_causal_" + failed_prefix + "_failures")
            raise
        finally:
            try:
                self._release_run_action_admission()
            finally:
                try:
                    if not self._hold_workspace:
                        self._release_workspace()
                finally:
                    self._running = False
                    self.scheduler._causal_tasks.end_run(run_token)


__all__ = ["CausalTileEngine"]
