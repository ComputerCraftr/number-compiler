"""Completed future tiles and demand-only scheduling share one executor."""

from __future__ import annotations

from number_compiler.hashlife.execution.tile_scheduler import TileApplication


from tests.support.assertions import assert_rejected_atomically
from tests.support.tile_kernel import join_four

from collections.abc import Hashable
from dataclasses import dataclass
from typing import Never, TypeVar

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.hashlife.interfaces.diamond_quotient import (
    COMPONENT_ROLES,
    DiamondQuotientArena,
    LocalInterfaceID,
    MacroComponents,
    MacroInterface,
)
from number_compiler.hashlife.tiles.tile_context import (
    ChildContext,
    PrimitiveTileResult,
    ResultSemantics,
    TemporalCocycle,
)
from number_compiler.hashlife.tiles.tile_ports import ResultWiring
from number_compiler.hashlife.tiles.tile_result_records import CompletedResult
from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
from number_compiler.hashlife.tiles.tiles import (
    TileAlphabet,
    TileArena,
    TileID,
    TileLease,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict


class _Actions:
    def __init__(self, ledger: ResourceLedger) -> None:
        self.ledger = ledger
        self.owner = ArenaToken("tile-test-actions")
        self._signature: PortSignatureID | None = None
        self._signatures: dict[int, PortSignatureID] = {}
        self._nodes: LedgerDict[int, tuple[int, int] | None] = ledger.make_dict(
            ledger.register("tile-test-actions", "field_action"),
        )
        ledger.register_execution_root(self)
        powers = {4: (0, 0)}
        powers.update(
            {local_id: (local_id - 1, local_id - 1) for local_id in range(5, 14)}
        )
        nodes = {0: None, 1: None, 2: (0, 1), 3: (1, 0), **powers}
        ledger.reserve(self._nodes.owner, entries=len(nodes), nodes=len(nodes))
        self._nodes.update(nodes)

    def action(self, local_id: int) -> FieldCellActionID:
        self.validate_action(
            FieldCellActionID(
                self.owner,
                "field-cell-action",
                local_id,
            )
        )
        return FieldCellActionID(self.owner, "field-cell-action", local_id)

    def validate_action(self, action: FieldCellActionID) -> None:
        if type(action) is not FieldCellActionID:
            raise TypeError("expected a field action")
        action.validate(self.owner, "field-cell-action", size=len(self._nodes))
        if action.local_id not in self._nodes:
            raise ValueError("unpublished field action")

    def signature_for(self, action: FieldCellActionID) -> PortSignatureID:
        self.validate_action(action)
        if action.local_id in self._signatures:
            return self._signatures[action.local_id]
        if self._signature is None:
            raise ValueError("test action signature is not bound")
        return self._signature

    def children(
        self,
        action: FieldCellActionID,
    ) -> None | tuple[FieldCellActionID, FieldCellActionID]:
        self.validate_action(action)
        record = self._nodes[action.local_id]
        if record is None:
            return None
        return self.action(record[0]), self.action(record[1])


@dataclass
class _Adapter:
    ledger: ResourceLedger
    actions: _Actions
    tiles: TileArena
    outgoing: LocalInterfaceID
    leaf_interfaces: dict[tuple[int, int], LocalInterfaceID]
    leaf_records: dict[LocalInterfaceID, tuple[int, int]]
    leaf_calls: int = 0
    child_context_calls: int = 0
    active_calls: int = 0
    temporal_wirings: dict[tuple[str, int, int], ChildContext] | None = None

    complete_via_midpoint_tiles: bool = False

    def validate_wiring(self, action: FieldCellActionID, wiring: ResultWiring) -> None:
        self.validate_action(action)
        wiring.__post_init__()

    def validate_action(self, action: FieldCellActionID) -> None:
        self.actions.validate_action(action)

    def action_children(
        self,
        action: FieldCellActionID,
    ) -> tuple[FieldCellActionID, FieldCellActionID] | None:
        return self.actions.children(action)

    def action_cocycle(self, action: FieldCellActionID) -> TemporalCocycle:
        self.validate_action(action)
        if action.local_id >= 4:
            return TemporalCocycle(2 << (action.local_id - 4))
        return TemporalCocycle(
            1 if action.local_id in (0, 1) else 2,
            int(action.local_id != 0),
            int(action.local_id != 0),
        )

    def leaf_observation(
        self,
        action: FieldCellActionID,
        source: TileID,
        interface: object,
        ports: object,
    ) -> TemporalCocycle:
        self.validate_action(action)
        self.tiles.resolve(source)
        return TemporalCocycle()

    def leaf_interface(
        self,
        action: FieldCellActionID,
        source: TileID,
        wiring: ResultWiring,
    ) -> LocalInterfaceID:
        self.validate_action(action)
        node = self.tiles.resolve(source)
        assert node.level == 0 and node.symbol is not None
        return self.leaf_interfaces[action.local_id, node.symbol]

    def apply_leaf(
        self,
        interface: LocalInterfaceID,
        ports: tuple[int, ...],
    ) -> PrimitiveTileResult:
        action_id, symbol = self.leaf_records[interface]
        self.leaf_calls += 1
        output = (
            symbol
            if symbol == 3
            else (
                (symbol + 1) % 3
                if action_id == 0
                else (2 * symbol) % 3
                if action_id == 1
                else (2 * ((symbol + 1) % 3)) % 3
                if action_id == 2
                else ((2 * symbol) % 3 + 1) % 3
                if action_id == 3
                else (symbol + (2 << (action_id - 4))) % 3
            )
        )
        return PrimitiveTileResult(
            output,
            ResultSemantics(
                interface,
                ports,
                relative_extent=int(output != 3),
            ),
        )

    def child_context(
        self,
        action: FieldCellActionID,
        parent: TileID,
        left: TileID,
        right: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
        side: int,
    ) -> ChildContext:
        self.validate_action(action)
        assert self.tiles.resolve(parent).level > 0
        assert left != right or self.tiles.resolve(left) == self.tiles.resolve(right)
        assert side in (0, 1)
        self.child_context_calls += 1
        return ChildContext(ports, wiring)

    def join_semantics(
        self,
        action: FieldCellActionID,
        parent: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
        left: CompletedResult,
        right: CompletedResult,
    ) -> ResultSemantics:
        self.validate_action(action)
        half = self.tiles.resolve(parent).width // 2
        right_extent = right.relative_extent
        extent = half + right_extent if right_extent else left.relative_extent
        if (
            left.physical_ticks,
            left.event_weight,
            left.frame_shift,
        ) != (
            right.physical_ticks,
            right.event_weight,
            right.frame_shift,
        ):
            raise ValueError("spatial children carry different temporal cocycles")
        return ResultSemantics(
            self.outgoing,
            right.outgoing_ports,
            left.physical_ticks,
            left.event_weight,
            left.frame_shift,
            0,
            extent,
        )

    def temporal_before_context(
        self,
        action: FieldCellActionID,
        before: FieldCellActionID,
        original_ports: tuple[int, ...],
        wiring: ResultWiring,
    ) -> ChildContext:
        self.validate_action(action)
        self.validate_action(before)
        if self.temporal_wirings is not None:
            return self.temporal_wirings["before", action.local_id, before.local_id]
        return ChildContext(original_ports, wiring)

    def temporal_after_context(
        self,
        action: FieldCellActionID,
        after: FieldCellActionID,
        before_result: CompletedResult,
        original_ports: tuple[int, ...],
        wiring: ResultWiring,
    ) -> ChildContext:
        self.validate_action(action)
        self.validate_action(after)
        if self.temporal_wirings is not None:
            return self.temporal_wirings["after", action.local_id, after.local_id]
        return ChildContext(original_ports, wiring)

    def temporal_semantics(
        self,
        action: FieldCellActionID,
        before: CompletedResult,
        after: CompletedResult,
        original_ports: tuple[int, ...],
        wiring: ResultWiring,
    ) -> ResultSemantics:
        self.validate_action(action)
        return ResultSemantics(
            self.outgoing,
            original_ports,
            before.physical_ticks + after.physical_ticks,
            before.event_weight + after.event_weight,
            before.frame_shift + after.frame_shift,
            before.relative_origin + after.relative_origin,
            after.relative_extent,
        )

    def output_active(
        self,
        action: FieldCellActionID,
        source: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
    ) -> bool:
        self.validate_action(action)
        self.active_calls += 1
        return self.tiles.resolve(source).last_active is not None


@dataclass
class _Runtime:
    ledger: ResourceLedger
    tiles: TileArena
    actions: _Actions
    adapter: _Adapter
    scheduler: TileScheduler
    wiring: ResultWiring
    root: TileLease

    def close(self) -> None:
        self.root.close()


def _runtime() -> _Runtime:
    ledger = ResourceLedger()
    functions = SemanticFunctionArena(ledger)
    interfaces = DiamondQuotientArena(functions)
    variable = PortVariable(0, 0, "carry", 0)
    port = FinitePort(variable, 2)
    signature = FunctionSignature((port,), BOOL)
    zero = functions.atom(signature, 0)
    one = functions.atom(signature, 1)
    interface = interfaces.intern_interface(
        MacroInterface(
            SemanticIdentity("tile-test-v1", ("pointwise",)),
            (port,),
            (BOOL,) * len(COMPONENT_ROLES),
            one,
        )
    )
    quotient = interfaces.intern(
        interface,
        MacroComponents(*(zero for _ in COMPONENT_ROLES)),
    )
    leaf_interfaces: dict[tuple[int, int], LocalInterfaceID] = {}
    leaf_records: dict[LocalInterfaceID, tuple[int, int]] = {}
    for action_id in range(14):
        for symbol in range(4):
            code = action_id * 4 + symbol
            components = MacroComponents(
                *(
                    one if code & (1 << index) else zero
                    for index in range(len(COMPONENT_ROLES))
                )
            )
            leaf_interface = interfaces.intern(interface, components)
            leaf_interfaces[action_id, symbol] = leaf_interface
            leaf_records[leaf_interface] = (action_id, symbol)
    tiles = TileArena(ledger)
    alphabet = tiles.intern_alphabet(TileAlphabet(4, 3, 4, 2, "test", "v1"))
    leaves = [tiles.leaf(alphabet, symbol) for symbol in (0, 1, 2, 3)]
    left, right, root = join_four(tiles, leaves)
    for lease in (*leaves, left, right):
        lease.close()
    actions = _Actions(ledger)
    actions._signature = interface
    results = CompletedResultArena(
        tiles,
        interfaces,
        action_authority=actions,
        validate_action=actions.validate_action,
        signature_for=actions.signature_for,
    )
    adapter = _Adapter(
        ledger,
        actions,
        tiles,
        quotient,
        leaf_interfaces,
        leaf_records,
    )
    scheduler = TileScheduler(tiles, results, adapter)
    return _Runtime(
        ledger,
        tiles,
        actions,
        adapter,
        scheduler,
        ResultWiring(interface),
        root,
    )


def _application_fixture() -> tuple[_Runtime, TileApplication, int]:
    runtime = _runtime()
    application = runtime.scheduler.application(
        runtime.actions.action(2), runtime.root.tile, (0,), runtime.wiring
    )
    return runtime, application, len(runtime.tiles._leases)


def _assert_pin_rollback(runtime: _Runtime, leases_before: int) -> None:
    assert len(runtime.tiles._leases) == leases_before
    account = runtime.ledger.inventory()[runtime.scheduler._pin_owner]
    assert (account.entries, account.nodes, account.accounting_delta) == (0, 0, 0)


def test_physical_constructor_installs_deferred_scheduler_dependencies() -> None:
    runtime = _runtime()
    try:
        assert type(runtime.scheduler.tiles) is TileArena
        assert type(runtime.scheduler.results) is CompletedResultArena
        assert type(runtime.scheduler) is TileScheduler
        assert not runtime.scheduler._source_only
    finally:
        runtime.close()


def _symbols(runtime: _Runtime, tile: TileID) -> tuple[int, ...]:
    width = runtime.tiles.resolve(tile).width
    return tuple(runtime.tiles.point(tile, coordinate) for coordinate in range(width))


def test_composed_actions_are_noncommuting_and_output_complete() -> None:
    runtime = _runtime()
    try:
        first = runtime.scheduler.complete(
            runtime.actions.action(2),
            runtime.root.tile,
            (0,),
            runtime.wiring,
        )
        second = runtime.scheduler.complete(
            runtime.actions.action(3),
            runtime.root.tile,
            (0,),
            runtime.wiring,
        )
        try:
            assert _symbols(runtime, first.output) == (2, 1, 0, 3)
            assert _symbols(runtime, second.output) == (1, 0, 2, 3)
            assert first.result.physical_ticks == second.result.physical_ticks == 2
        finally:
            first.close()
            second.close()
    finally:
        runtime.close()


def test_tile_identity_does_not_swallow_distinct_result_semantics() -> None:
    runtime = _runtime()
    alphabet = runtime.tiles.resolve(runtime.root.tile).alphabet
    blank = runtime.tiles.leaf(alphabet, 3)
    try:
        first = runtime.scheduler.complete(
            runtime.actions.action(0),
            blank.tile,
            (0,),
            runtime.wiring,
        )
        second = runtime.scheduler.complete(
            runtime.actions.action(1),
            blank.tile,
            (0,),
            runtime.wiring,
        )
        try:
            assert first.output == second.output
            assert first.result.event_weight == 0
            assert second.result.event_weight == 1
        finally:
            first.close()
            second.close()
    finally:
        blank.close()
        runtime.close()


def test_cold_point_descends_only_one_branch_and_never_builds_a_parent() -> None:
    runtime = _runtime()
    try:
        before = runtime.ledger.counters.copy()
        assert (
            runtime.scheduler.point(
                runtime.actions.action(2),
                runtime.root.tile,
                (0,),
                runtime.wiring,
                2,
            )
            == 0
        )
        assert runtime.adapter.leaf_calls == 1
        assert runtime.adapter.child_context_calls == 2
        assert (
            runtime.ledger.counters.get("tile_scheduler_spatial_compositions", 0) == 0
        )
        assert (
            runtime.ledger.counters.get("tile_publications", 0)
            - before.get(
                "tile_publications",
                0,
            )
            <= 2
        )
    finally:
        runtime.close()


def test_cold_width_uses_bounded_activity_and_one_leaf() -> None:
    runtime = _runtime()
    try:
        assert (
            runtime.scheduler.width(
                runtime.actions.action(2),
                runtime.root.tile,
                (0,),
                runtime.wiring,
            )
            == 3
        )
        assert runtime.adapter.leaf_calls == 1
        assert runtime.adapter.active_calls <= 4
        assert (
            runtime.ledger.counters.get("tile_scheduler_spatial_compositions", 0) == 0
        )
    finally:
        runtime.close()


def test_cached_midpoint_and_fused_routes_publish_the_same_result() -> None:
    fused = _runtime()
    cached = _runtime()
    try:
        fused_result = fused.scheduler.complete(
            fused.actions.action(2),
            fused.root.tile,
            (0,),
            fused.wiring,
        )
        midpoint = cached.scheduler.complete(
            cached.actions.action(0),
            cached.root.tile,
            (0,),
            cached.wiring,
        )
        cached_result = cached.scheduler.complete(
            cached.actions.action(2),
            cached.root.tile,
            (0,),
            cached.wiring,
        )
        try:
            assert _symbols(fused, fused_result.output) == _symbols(
                cached,
                cached_result.output,
            )
            assert (
                fused_result.result.physical_ticks
                == cached_result.result.physical_ticks
            )
            assert fused_result.result.event_weight == cached_result.result.event_weight
            assert cached.ledger.counters["tile_scheduler_midpoint_hits"] == 1
        finally:
            fused_result.close()
            midpoint.close()
            cached_result.close()
    finally:
        fused.close()
        cached.close()


def test_application_root_lease_makes_warm_observations_executable(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime = _runtime()
    application = runtime.scheduler.application(
        runtime.actions.action(2),
        runtime.root.tile,
        (0,),
        runtime.wiring,
    )
    try:
        result = application.complete()
        assert result.relative_extent == 3

        def forbidden(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("warm observation replayed construction")

        monkeypatch.setattr(runtime.adapter, "action_children", forbidden)
        monkeypatch.setattr(runtime.adapter, "leaf_interface", forbidden)
        monkeypatch.setattr(runtime.adapter, "apply_leaf", forbidden)
        monkeypatch.setattr(runtime.adapter, "child_context", forbidden)
        monkeypatch.setattr(runtime.adapter, "join_semantics", forbidden)
        monkeypatch.setattr(runtime.adapter, "temporal_before_context", forbidden)
        monkeypatch.setattr(runtime.adapter, "temporal_after_context", forbidden)
        monkeypatch.setattr(runtime.adapter, "temporal_semantics", forbidden)
        monkeypatch.setattr(runtime.adapter, "output_active", forbidden)
        assert application.point(1) == 1
        assert application.width() == 3
    finally:
        application.close()
        runtime.close()


def test_incomplete_application_pins_and_reuses_demanded_leaf_result() -> None:
    runtime = _runtime()
    application = runtime.scheduler.application(
        runtime.actions.action(2),
        runtime.root.tile,
        (0,),
        runtime.wiring,
    )
    try:
        assert application.point(2) == 0
        leaf_calls = runtime.adapter.leaf_calls
        assert len(runtime.scheduler._pins) == 1
        assert application.point(2) == 0
        assert runtime.adapter.leaf_calls == leaf_calls
        application.complete()
        assert not runtime.scheduler._pins
    finally:
        application.close()
        runtime.close()


def test_application_identity_fields_are_immutable() -> None:
    runtime = _runtime()
    application = runtime.scheduler.application(
        runtime.actions.action(2),
        runtime.root.tile,
        (0,),
        runtime.wiring,
    )
    try:
        with pytest.raises(AttributeError):
            application.ports = (1,)
        with pytest.raises(AttributeError):
            application.action = runtime.actions.action(0)
        with pytest.raises(AttributeError):
            application.wiring = ResultWiring(runtime.wiring.signature, 1)
    finally:
        application.close()
        runtime.close()


@pytest.mark.parametrize("symbol", (1, 3), ids=("active", "blank"))
def test_compiled_power_leaf_work_is_constant_through_n1024(symbol: int) -> None:
    runtime = _runtime()
    alphabet = runtime.tiles.resolve(runtime.root.tile).alphabet
    source = runtime.tiles.leaf(alphabet, symbol)
    try:
        for local_id, steps in zip(
            range(7, 14), (16, 32, 64, 128, 256, 512, 1024), strict=True
        ):
            before = runtime.adapter.leaf_calls
            application = runtime.scheduler.application(
                runtime.actions.action(local_id),
                source.tile,
                (0,),
                runtime.wiring,
            )
            try:
                expected = symbol if symbol == 3 else (symbol + steps) % 3
                assert application.point(0) == expected
                result = application.complete()
                assert result.physical_ticks == steps
                assert runtime.adapter.leaf_calls - before <= 1
            finally:
                application.close()
        assert runtime.ledger.counters.get("sequential_generation_advances", 0) == 0
    finally:
        source.close()
        runtime.close()


def test_cached_midpoint_uses_certified_distinct_child_wirings() -> None:
    ledger = ResourceLedger()
    functions = SemanticFunctionArena(ledger)
    interfaces = DiamondQuotientArena(functions)
    declarations: list[PortSignatureID] = []
    locals_by_action: dict[int, dict[int, LocalInterfaceID]] = {}
    leaf_records: dict[LocalInterfaceID, tuple[int, int]] = {}
    for action_id, cardinality in enumerate((2, 3, 4, 4)):
        port = FinitePort(PortVariable(0, 0, f"carry-{action_id}", 0), cardinality)
        signature = FunctionSignature((port,), BOOL)
        zero = functions.atom(signature, 0)
        one = functions.atom(signature, 1)
        declaration = interfaces.intern_interface(
            MacroInterface(
                SemanticIdentity(f"distinct-{action_id}", ("distinct", action_id)),
                (port,),
                (BOOL,) * len(COMPONENT_ROLES),
                one,
                phase_count=2,
            )
        )
        declarations.append(declaration)
        locals_by_action[action_id] = {}
        for symbol in range(4):
            code = action_id * 4 + symbol
            local = interfaces.intern(
                declaration,
                MacroComponents(
                    *(
                        one if code & (1 << index) else zero
                        for index in range(len(COMPONENT_ROLES))
                    )
                ),
            )
            locals_by_action[action_id][symbol] = local
            leaf_records[local] = action_id, symbol
    tiles = TileArena(ledger)
    alphabet = tiles.intern_alphabet(TileAlphabet(4, 3, 4, 2, "test", "v1"))
    source = tiles.leaf(alphabet, 1)
    actions = _Actions(ledger)
    actions._signatures.update({index: declarations[index] for index in range(4)})
    results = CompletedResultArena(
        tiles,
        interfaces,
        action_authority=actions,
        validate_action=actions.validate_action,
        signature_for=actions.signature_for,
    )
    adapter = _Adapter(
        ledger,
        actions,
        tiles,
        locals_by_action[2][0],
        {
            (action, symbol): local
            for action, records in locals_by_action.items()
            for symbol, local in records.items()
        },
        leaf_records,
    )
    adapter.temporal_wirings = {
        ("before", 2, 0): ChildContext((1,), ResultWiring(declarations[0], 1, 1)),
        ("after", 2, 1): ChildContext((2,), ResultWiring(declarations[1], 1, 1)),
    }
    scheduler = TileScheduler(tiles, results, adapter)
    composite_wiring = ResultWiring(declarations[2], 1, 1)
    try:
        fused = scheduler.complete(
            actions.action(2), source.tile, (3,), composite_wiring
        )
        fused_value = tiles.point(fused.output, 0)
        fused_semantics = fused.result
        fused.close()
        results.clear()
        midpoint = scheduler.complete(
            actions.action(0),
            source.tile,
            (1,),
            ResultWiring(declarations[0], 1, 1),
        )
        cached = scheduler.complete(
            actions.action(2), source.tile, (3,), composite_wiring
        )
        try:
            assert tiles.point(cached.output, 0) == fused_value
            assert cached.result.physical_ticks == fused_semantics.physical_ticks == 2
            assert cached.result.outgoing == locals_by_action[2][0]
            assert cached.result.outgoing_ports == fused_semantics.outgoing_ports
            assert ledger.counters["tile_scheduler_midpoint_hits"] == 1
        finally:
            midpoint.close()
            cached.close()
    finally:
        source.close()


def test_clipped_width_does_not_invent_activity_in_a_padding_gap() -> None:
    runtime = _runtime()
    alphabet = runtime.tiles.resolve(runtime.root.tile).alphabet
    leaves = [runtime.tiles.leaf(alphabet, symbol) for symbol in (0, 3, 3, 0)]
    left, right, source = join_four(runtime.tiles, leaves)
    for lease in (*leaves, left, right):
        lease.close()
    application = runtime.scheduler.application(
        runtime.actions.action(0),
        source.tile,
        (0,),
        runtime.wiring,
    )
    try:
        assert application.width(3) == 1
        application.complete()
        assert application.width(3) == 1
        assert application.width() == 4
    finally:
        application.close()
        source.close()
        runtime.close()


def test_direct_observations_reject_foreign_action_before_accounting() -> None:
    runtime = _runtime()
    foreign = FieldCellActionID(
        ArenaToken("foreign-tile-actions"),
        "field-cell-action",
        0,
    )
    try:
        before = assert_rejected_atomically(
            runtime.ledger,
            lambda: runtime.scheduler.point(
                foreign, runtime.root.tile, (0,), runtime.wiring, 0
            ),
            ValueError,
        )
        with pytest.raises(ValueError):
            runtime.scheduler.width(
                foreign,
                runtime.root.tile,
                (0,),
                runtime.wiring,
                limit=0,
            )
        assert runtime.ledger.snapshot() == before
    finally:
        runtime.close()


def test_result_semantics_preserves_exact_outgoing_boundary_operands() -> None:
    from number_compiler.hashlife.actions.lazy_compiler import UnsupportedInterfaceError
    from number_compiler.hashlife.tiles.tile_boundaries import (
        BoundaryTileOperands,
        BoundaryTileView,
    )
    from number_compiler.hashlife.tiles.tile_result_records import PoweredResultKey

    runtime = _runtime()
    try:
        lease = runtime.scheduler.complete(
            runtime.actions.action(2),
            runtime.root.tile,
            (0,),
            runtime.wiring,
        )
        try:
            original = lease.result
            boundaries = BoundaryTileOperands(
                left=BoundaryTileView(lease.output, relative_extent=4),
                right=BoundaryTileView(lease.output, relative_extent=4, orientation=1),
            )
            semantics = ResultSemantics(
                original.outgoing,
                original.outgoing_ports,
                physical_ticks=7,
                event_weight=3,
                frame_shift=-2,
                relative_origin=-1,
                relative_extent=4,
                outgoing_boundaries=boundaries,
            )
            result = semantics.completed(lease.output)
            assert result.outgoing_boundaries == boundaries
            assert (result.physical_ticks, result.event_weight, result.frame_shift) == (
                7,
                3,
                -2,
            )
            key = PoweredResultKey(
                runtime.actions.action(2),
                runtime.root.tile,
                (0,),
                runtime.wiring,
                boundaries,
            )
            before = runtime.ledger.snapshot()
            with pytest.raises(
                UnsupportedInterfaceError, match="boundary-tile execution law"
            ):
                runtime.scheduler._validate_execution_key(key)
            after = runtime.ledger.snapshot()
            assert before.entries == after.entries
            assert before.nodes == after.nodes
        finally:
            lease.close()
    finally:
        runtime.close()


def test_failed_demanded_pin_reservation_releases_result_lease(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )

    runtime, application, leases_before = _application_fixture()
    reserve = runtime.ledger.reserve

    def reject_pin(owner: int, entries: int = 0, nodes: int = 0) -> None:
        if owner == runtime.scheduler._pin_owner:
            raise BlockContextBudgetExceeded("injected pin reservation failure")
        return reserve(owner, entries, nodes)

    monkeypatch.setattr(runtime.ledger, "reserve", reject_pin)
    try:
        with pytest.raises(BlockContextBudgetExceeded, match="pin reservation"):
            application.point(2)
        assert not runtime.scheduler._pins
        _assert_pin_rollback(runtime, leases_before)
    finally:
        application.close()
        runtime.close()


def test_partial_demanded_pin_publication_rolls_back(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    runtime, application, leases_before = _application_fixture()
    write = LedgerDict.__setitem__

    def fail_after_write(
        store: LedgerDict[KeyT, ValueT], key: KeyT, value: ValueT
    ) -> None:
        write(store, key, value)
        if store is runtime.scheduler._pins:
            raise RuntimeError("injected partial pin publication")

    monkeypatch.setattr(LedgerDict, "__setitem__", fail_after_write)
    try:
        with pytest.raises(RuntimeError, match="partial pin publication"):
            application.point(2)
        assert not runtime.scheduler._pins
        _assert_pin_rollback(runtime, leases_before)
    finally:
        application.close()
        runtime.close()


KeyT = TypeVar("KeyT", bound=Hashable)
ValueT = TypeVar("ValueT")
