"""Store-free iterative causal recurrence over exact boundary tile operands."""

from __future__ import annotations

from dataclasses import replace
from typing import TYPE_CHECKING, Any

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
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
from number_compiler.hashlife.execution.tile_causal_api import CausalTileAPI
from number_compiler.hashlife.execution.tile_causal_behavior import quiescent_boundary
from number_compiler.hashlife.execution.tile_causal_boundary_step import (
    boundary_step,
    probe_boundary_result,
)
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
    primitive_causal_semantics,
    probe_causal_result,
    publish_causal_completed,
)
from number_compiler.hashlife.execution.tile_causal_tasks import (
    CausalFrame as _Frame,
)
from number_compiler.hashlife.execution.tile_causal_tasks import (
    CausalPrefix as _Prefix,
)
from number_compiler.hashlife.execution.tile_causal_tasks import (
    append_prefix,
    combine_spatial_outputs,
    composite_result_key,
    covered_chunks,
    primitive_advance,
    publish_composite_output,
    retain_completed,
    temporal_payload,
)
from number_compiler.hashlife.execution.tile_reverse_boundary import (
    reverse_boundary_step,
    supports_reverse_boundary,
)
from number_compiler.hashlife.tiles.tile_boundaries import (
    BoundaryTileOperands,
    BoundaryTileView,
)
from number_compiler.hashlife.tiles.tile_region_memo import normalize_cached_region
from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey
from number_compiler.hashlife.tiles.tile_results import ResultLease
from number_compiler.hashlife.tiles.tiles import TileID, TileLease

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
        self._action_admission_token: object | None = None
        self._running = False
        self._workspace_memo = scheduler._causal_tasks.memo
        self._workspace_active = scheduler._causal_tasks.active

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

    def _admit_run_actions(self, action: FieldCellActionID) -> object:
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
        self, action: FieldCellActionID, tile: TileID, left: object, right: object
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
        if pair_transfer is not None:
            pair_transfer.clear_bindings()
        for result in reversed(self._result_leases):
            result.close()
        self._result_leases.clear()
        for lease in reversed(self._leases):
            lease.close()
        self._leases.clear()
        self.scheduler._causal_workspace.clear()
        self.scheduler._causal_tasks.clear()
        self._application = None

    def _run(
        self,
        root: _Frame,
        *,
        tile_result: bool,
        return_result: bool = False,
    ) -> Any:
        if self._running:
            raise RuntimeError("causal tile engine cannot reenter an active run")
        frames = self.scheduler._causal_tasks.frames
        values = self.scheduler._causal_tasks.values
        memo = self._workspace_memo
        active = self._workspace_active
        primary = {
            "advance",
            "anchor",
            "emit",
            "residual",
            "output",
            "output_boundary",
            "interface",
            "reverse_interface",
            "reverse_boundary",
            "interface_emit",
            "child_states",
        }
        run_token = self.scheduler._causal_tasks.begin_run()
        self._running = True
        try:
            if root.op != "exact_reverse_output":
                self._action_admission_token = self._admit_run_actions(root.args[0])
            frames.append(root)
            while frames:
                peak = len(frames) + len(values) + len(memo) + len(active)
                old = self.ledger.counters.get("tile_causal_workspace_peak", 0)
                if peak > old:
                    self.ledger.bump("tile_causal_workspace_peak", peak - old)
                frame = frames.pop()
                op, a = frame.op, frame.args
                self.ledger.bump("tile_causal_frames")
                if op == "memo_done":
                    key = a[0]
                    if key not in active or not values:
                        raise AssertionError(
                            "causal memo completion lost its dependency"
                        )
                    value = values.pop()
                    self.scheduler._causal_tasks.finish(key, value)
                    values.append(value)
                    self.ledger.bump("tile_causal_task_memo_publications")
                    continue
                if op in primary and frame.stage == 0 and not frame.memoized:
                    if op == "output_boundary":
                        action, side, view, anchor, argument = a
                        dependencies = (
                            self.scheduler._causal_dependencies
                            if self._application is not None
                            else None
                        )
                        normalized, lease = normalize_cached_region(
                            self.scheduler.results,
                            view,
                            dependencies=dependencies,
                            application=self._application,
                        )
                        self._leases.append(lease)
                        a = (action, side, normalized, anchor, argument)
                        frame.args = a
                    elif op == "advance":
                        action, side, state, view = a
                        if type(view) is BoundaryTileView:
                            view.__post_init__()
                        if type(view) is BoundaryTileView and view.relative_origin:
                            view = BoundaryTileView(
                                view.tile,
                                0,
                                view.relative_extent,
                                view.orientation,
                                view.source_offset,
                            )
                            a = (action, side, state, view)
                            frame.args = a
                    key = (op, a)
                    counter = "tile_causal_" + (
                        "boundary_output" if op == "output_boundary" else op
                    )
                    self.ledger.bump(counter + "_requests")
                    if op == "output_boundary":
                        self.ledger.bump(
                            counter + "_requested_extent", a[2].relative_extent
                        )
                    found = memo.get(key)
                    if found is not None:
                        values.append(found)
                        self.ledger.bump("tile_causal_task_memo_hits")
                        self.ledger.bump(counter + "_hits")
                        if op == "output_boundary":
                            self.ledger.bump(
                                counter + "_cached_extent", a[2].relative_extent
                            )
                        continue
                    if op == "output_boundary":
                        boundary = probe_boundary_result(self, frame)
                        if boundary is not None:
                            values.append(boundary)
                            self.ledger.bump(counter + "_hits")
                            self.ledger.bump(
                                counter + "_cached_extent", a[2].relative_extent
                            )
                            continue
                    if key in active:
                        raise ValueError("causal task dependency contains a cycle")
                    self.ledger.bump(counter + "_evaluations")
                    try:
                        self.scheduler._causal_tasks.begin(key)
                    except BaseException:
                        self.ledger.bump(counter + "_failures")
                        raise
                    frame.memoized = True
                    frames.extend((_Frame("memo_done", (key,)), frame))
                    self.ledger.bump("tile_causal_task_memo_evaluations")
                    continue
                if interface_step(self, frame, frames, values):
                    continue
                if reverse_boundary_step(self, frame, frames, values):
                    continue
                if promotion_step(self, frame, frames, values):
                    continue
                if point_step(self, frame, frames, values):
                    continue
                if op == "advance":
                    action, side, state, view = a
                    if self._children(action) is None:
                        values.append(
                            primitive_advance(
                                self.adapter,
                                action,
                                side,
                                state,
                                view,
                                action_admission=self._action_admission_token,
                            )
                        )
                    else:
                        if (
                            not isinstance(state, _Prefix)
                            or state.action != action
                            or state.side != side
                        ):
                            raise ValueError(
                                "composite transfer requires its exact causal prefix"
                            )
                        values.append(self._append_prefix(state, view))
                    continue
                if op == "emit":
                    action, left, symbol, right = a
                    children = self._children(action)
                    if children is None:
                        alphabet = self.adapter.alphabet(action)
                        source = self.tiles.leaf(alphabet, symbol)
                        self._leases.append(source)
                        wiring = self._wiring(action)
                        key, completed = probe_causal_result(
                            self.scheduler.results,
                            action,
                            source.tile,
                            PrimitiveCausalPorts(left, right),
                            wiring,
                            action_admission=self._action_admission_token,
                        )
                        if completed is not None:
                            payload = retain_completed(self, key, completed)
                            self.ledger.bump("tile_causal_result_hits")
                            values.append(payload)
                            continue
                        output_symbol = self._law(action).emit(
                            left,
                            symbol,
                            right,
                        )
                        output = self.tiles.leaf(alphabet, output_symbol)
                        self._leases.append(output)
                        interface = self.adapter.leaf_interface(
                            action,
                            source.tile,
                            wiring,
                        )
                        occurrence = self.adapter.leaf_observation(
                            action,
                            source.tile,
                            interface,
                            (left, right),
                        )
                        semantics = primitive_causal_semantics(
                            self.scheduler.results,
                            action,
                            source.tile,
                            output.tile,
                            PrimitiveCausalPorts(left, right),
                            wiring,
                            occurrence,
                        )
                        from number_compiler.hashlife.execution.tile_physical_support import (
                            primitive_physical_support,
                        )

                        support = primitive_physical_support(
                            self.scheduler,
                            action,
                            source.tile,
                            (left, right),
                        )
                        if support is not None:
                            semantics = replace(
                                semantics,
                                physical_support=support,
                            )
                        forward = BoundaryTileView(output.tile, 0, 1)
                        backward = BoundaryTileView(output.tile, 0, 1, 1)
                        payload = CausalCompletedOutput(
                            output.tile,
                            replace(
                                semantics,
                                outgoing_boundaries=BoundaryTileOperands(
                                    forward, backward
                                ),
                            ),
                            (left, right),
                        )
                        completed = publish_causal_completed(
                            self.scheduler.results,
                            key,
                            payload,
                        )
                        payload = retain_completed(self, key, completed)
                        values.append(payload)
                        self.ledger.bump("tile_causal_primitive_emits")
                        continue
                    before, after = children
                    if frame.stage == 4:
                        second = values.pop()
                        first = frame.saved[0]
                        values.append(
                            temporal_payload(
                                self.adapter,
                                before,
                                after,
                                first,
                                second,
                                left.explicit_edge or right.explicit_edge,
                            )
                        )
                        continue
                    if frame.stage == 0:
                        match (left, right):
                            case (_Prefix(), _Prefix()):
                                pass
                            case _:
                                raise ValueError(
                                    "composite emission requires two causal prefixes"
                                )
                        frame.stage = 1
                        frames.extend(
                            (
                                frame,
                                _Frame("anchor", (before, 1, right)),
                                _Frame("anchor", (before, 0, left)),
                            )
                        )
                        continue
                    if frame.stage == 1:
                        right_anchor, left_anchor = values.pop(), values.pop()
                        frame.stage, frame.saved = 2, (left_anchor, right_anchor)
                        frames.extend(
                            (
                                frame,
                                _Frame(
                                    "advance_symbol", (before, 1, right_anchor, symbol)
                                ),
                                _Frame(
                                    "advance_symbol", (before, 0, left_anchor, symbol)
                                ),
                                _Frame(
                                    "emit", (before, left_anchor, symbol, right_anchor)
                                ),
                            )
                        )
                        continue
                    if frame.stage == 2:
                        right_argument, left_argument, first = (
                            values.pop(),
                            values.pop(),
                            values.pop(),
                        )
                        frame.stage, frame.saved = 3, (first,)
                        frames.extend(
                            (
                                frame,
                                _Frame("residual", (action, 1, right, left_argument)),
                                _Frame("residual", (action, 0, left, right_argument)),
                            )
                        )
                        continue
                    second_right, second_left = values.pop(), values.pop()
                    first = frame.saved[0]
                    frame.stage = 4
                    frame.saved = (first,)
                    frames.extend(
                        (
                            frame,
                            _Frame(
                                "emit",
                                (
                                    after,
                                    second_left,
                                    self.tiles.resolve(first.output).symbol,
                                    second_right,
                                ),
                            ),
                        )
                    )
                    continue
                if op == "advance_symbol":
                    action, side, state, symbol = a
                    if type(side) is not int or side not in (0, 1):
                        raise ValueError("symbol advance requires an exact direction")
                    if self._children(action) is None:
                        # A primitive transition observes only the finite literal.
                        # Publishing a tile and a directed-transfer cache entry
                        # for it duplicates the admitted kernel's transition law.
                        values.append(
                            self._law(action).advance(BoundarySide(side), state, symbol)
                        )
                        self.ledger.bump("tile_causal_direct_symbol_transfers")
                    else:
                        with self.tiles.leaf(
                            self.adapter.alphabet(action), symbol
                        ) as leaf:
                            values.append(
                                self._append_prefix(
                                    state,
                                    BoundaryTileView(leaf.tile, 0, 1),
                                )
                            )
                    continue
                if op == "anchor":
                    action, side, state = a
                    if (
                        self._children(state.action) is None
                    ):  # pragma: no cover - defensive
                        raise ValueError("causal prefix belongs to a primitive action")
                    if state.view is None:
                        values.append(self._initial(action, side, state.producer_seed))
                    else:
                        frames.append(
                            _Frame(
                                "advance",
                                (
                                    action,
                                    side,
                                    self._initial(action, side, state.producer_seed),
                                    state.view,
                                ),
                            )
                        )
                    continue
                if op == "residual":
                    composite, side, prefix, argument = a
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
                                _Frame(
                                    "advance",
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
                        consumer_state = values.pop()
                        frame.stage = 0
                        frame.saved = (consumer_state,)
                    elif frame.saved:
                        consumer_state = frame.saved[0]
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
                                _Frame(
                                    "advance",
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
                                    _Frame(
                                        "reverse_boundary",
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
                                _Frame(
                                    "output_boundary",
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
                    produced = values.pop()
                    if frame.stage == 2:
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
                            "reverse_boundary_extent_discharged",
                            prefix.view.relative_extent,
                        )
                        values.append(consumed)
                        continue
                    frames.append(
                        _Frame(
                            "advance",
                            (
                                after,
                                side,
                                consumer_state,
                                produced,
                            ),
                        )
                    )
                    continue
                if boundary_step(self, frame, frames, values):
                    continue
                if op == "output":
                    action, tile, left, right = a
                    children = self._children(action)
                    if (
                        frame.stage == 0
                        and children is None
                        and type(left) is int
                        and type(right) is int
                    ):
                        wiring = self._wiring(action)
                        key, completed = probe_causal_result(
                            self.scheduler.results,
                            action,
                            tile,
                            PrimitiveCausalPorts(left, right),
                            wiring,
                            action_admission=self._action_admission_token,
                        )
                        if completed is None:
                            completed = self.scheduler._complete_direct(key)
                            self.ledger.bump("tile_causal_result_evaluations")
                        else:
                            self.ledger.bump("tile_causal_result_hits")
                        payload = retain_completed(self, key, completed)
                        values.append(payload)
                        continue
                    if frame.stage == 0 and children is not None:
                        key = self._composite_key(action, tile, left, right)
                        if key is not None:
                            completed = lookup_causal_result(
                                self.scheduler.results,
                                key,
                                action_admission=self._action_admission_token,
                            )
                            if completed is not None:
                                payload = retain_completed(self, key, completed)
                                self.ledger.bump("tile_causal_result_hits")
                                values.append(payload)
                                continue
                    if children is not None and cached_midpoint_step(
                        self,
                        frame,
                        frames,
                        values,
                        action,
                        tile,
                        left,
                        right,
                        children,
                    ):
                        continue
                    node = self.tiles.resolve(tile)
                    if not node.level:
                        if node.symbol is None:
                            raise ValueError("malformed tile leaf")
                        if frame.stage == 0:
                            frame.stage = 1
                            frames.extend(
                                (
                                    frame,
                                    _Frame("emit", (action, left, node.symbol, right)),
                                )
                            )
                            continue
                        payload = values.pop()
                        match payload:
                            case CausalCompletedOutput():
                                pass
                            case _:
                                raise AssertionError(
                                    "causal leaf emission returned another result sort"
                                )
                        payload = publish_composite_output(
                            self, action, tile, left, right, payload
                        )
                        values.append(payload)
                        continue
                    assert node.left is not None and node.right is not None
                    if frame.stage == 0:
                        frame.stage = 1
                        frames.extend(
                            (
                                frame,
                                _Frame(
                                    "advance",
                                    (
                                        action,
                                        1,
                                        right,
                                        BoundaryTileView(
                                            node.right,
                                            0,
                                            self.tiles.resolve(node.right).width,
                                            1,
                                        ),
                                    ),
                                ),
                                _Frame(
                                    "advance",
                                    (
                                        action,
                                        0,
                                        left,
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
                        right_mid, left_mid = values.pop(), values.pop()
                        frame.stage, frame.saved = 2, (left_mid, right_mid)
                        frames.extend(
                            (
                                frame,
                                _Frame("output", (action, node.left, left, right_mid)),
                            )
                        )
                        continue
                    if frame.stage == 2:
                        left_out = values.pop()
                        left_mid, right_mid = frame.saved
                        frame.stage, frame.saved = 3, (left_out, left_mid, right_mid)
                        frames.extend(
                            (
                                frame,
                                _Frame("output", (action, node.right, left_mid, right)),
                            )
                        )
                        continue
                    right_out = values.pop()
                    left_out = frame.saved[0]
                    payload = combine_spatial_outputs(self, action, left_out, right_out)
                    payload = publish_composite_output(
                        self, action, tile, left, right, payload
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
            result = values.pop()
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
                action, tile, left, right = root.args
                key = self._composite_key(action, tile, left, right)
                completed = None if key is None else self.scheduler.results.lookup(key)
                if completed is None:
                    raise AssertionError("bound causal output was not published")
                return completed
            return self.tiles.retain(result.output)
        except BaseException:
            for failed_op, _failed_args in active:
                prefix = (
                    "boundary_output" if failed_op == "output_boundary" else failed_op
                )
                self.ledger.bump("tile_causal_" + prefix + "_failures")
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
