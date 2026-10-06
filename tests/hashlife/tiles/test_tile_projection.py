"""Lazy projection imports exact sources and delegates to one tile scheduler."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING, Never

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken, ExactSource
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
)
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.tile_execution_adapter import (
    FamilyTileHooks,
)
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.hashlife.interfaces.diamond_quotient import (
    COMPONENT_ROLES,
    DiamondQuotientArena,
    LocalInterfaceID,
    MacroComponents,
    MacroInterface,
)
from number_compiler.hashlife.observation.tile_projection import (
    LazyProjection,
    import_exact_source,
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
from number_compiler.hashlife.tiles.tiles import TileAlphabet, TileArena, TileID
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerDict
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from tests.support.assertions import assert_rejected_atomically
from tests.support.diamond_runtime import oracle
from tests.support.finite_functions import carry_atoms
from tests.support.tile_kernel import _runtime as primitive_runtime

if TYPE_CHECKING:
    from number_compiler.hashlife.tiles.tiles import TileAlphabetID


class _Actions:
    def __init__(self, ledger: ResourceLedger) -> None:
        self.ledger = ledger
        self.owner = ArenaToken("projection-test-actions")
        self.action_kind = "field-cell-action"
        store_owner = ledger.register("projection-test-actions", "field_action")
        self._nodes: LedgerDict[int, None] = ledger.make_dict(store_owner)
        ledger.reserve(store_owner, entries=1, nodes=1)
        self._nodes[0] = None
        self.signature_id: PortSignatureID | None = None
        ledger.register_execution_root(self)

    @property
    def action(self) -> FieldCellActionID:
        return FieldCellActionID(self.owner, self.action_kind, 0)

    def validate_action(self, action: FieldCellActionID) -> None:
        if type(action) is not FieldCellActionID:
            raise TypeError("expected a field action")
        action.validate(self.owner, self.action_kind, size=1)
        if action.local_id not in self._nodes:
            raise ValueError("unpublished field action")

    def signature_for(self, action: FieldCellActionID) -> PortSignatureID:
        self.validate_action(action)
        if self.signature_id is None:
            raise RuntimeError("test signature is not installed")
        return self.signature_id


@dataclass
class _IdentityAdapter:
    ledger: ResourceLedger
    actions: _Actions
    tiles: TileArena
    interfaces: dict[int, LocalInterfaceID]
    symbols: dict[LocalInterfaceID, int]
    family_hooks: FamilyTileHooks | None = None

    complete_via_midpoint_tiles: bool = False

    def validate_wiring(self, action: FieldCellActionID, wiring: ResultWiring) -> None:
        self.validate_action(action)
        wiring.__post_init__()

    def validate_action(self, action: FieldCellActionID) -> None:
        self.actions.validate_action(action)

    def action_children(self, action: FieldCellActionID) -> None:
        self.validate_action(action)

    def action_cocycle(self, action: FieldCellActionID) -> TemporalCocycle:
        self.validate_action(action)
        return TemporalCocycle()

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
        record = self.tiles.resolve(source)
        if record.level or record.symbol is None:
            raise ValueError("identity leaf needs one symbol")
        return self.interfaces[record.symbol]

    def apply_leaf(
        self,
        interface: LocalInterfaceID,
        ports: tuple[int, ...],
    ) -> PrimitiveTileResult:
        symbol = self.symbols[interface]
        return PrimitiveTileResult(
            symbol,
            ResultSemantics(interface, ports, relative_extent=int(symbol != 2)),
        )

    def child_context(
        self,
        action: FieldCellActionID,
        parent: object,
        left: object,
        right: object,
        ports: tuple[int, ...],
        wiring: ResultWiring,
        side: int,
    ) -> ChildContext:
        self.validate_action(action)
        if side not in (0, 1):
            raise ValueError("invalid child side")
        return ChildContext(ports, wiring)

    def join_semantics(
        self,
        action: FieldCellActionID,
        parent: TileID,
        ports: object,
        wiring: object,
        left: CompletedResult,
        right: CompletedResult,
    ) -> ResultSemantics:
        self.validate_action(action)
        half = self.tiles.resolve(parent).width // 2
        extent = (
            half + right.relative_extent
            if right.relative_extent
            else left.relative_extent
        )
        return ResultSemantics(
            left.outgoing,
            right.outgoing_ports,
            relative_extent=extent,
        )

    def temporal_before_context(
        self,
        composite: object,
        before: object,
        original_ports: object,
        wiring: object,
    ) -> Never:
        raise AssertionError("identity action has no temporal composition")

    def temporal_after_context(
        self,
        composite: object,
        after: object,
        before_result: object,
        original_ports: object,
        wiring: object,
    ) -> Never:
        raise AssertionError("identity action has no temporal composition")

    def temporal_semantics(
        self,
        composite: object,
        before_result: object,
        after_result: object,
        original_ports: object,
        wiring: object,
    ) -> Never:
        raise AssertionError("identity action has no temporal composition")

    def output_active(
        self, action: FieldCellActionID, source: TileID, ports: object, wiring: object
    ) -> bool:
        self.validate_action(action)
        return self.tiles.resolve(source).last_active is not None


def _runtime() -> tuple[
    ResourceLedger,
    _Actions,
    TileArena,
    TileAlphabetID,
    TileScheduler,
    ResultWiring,
]:
    ledger = ResourceLedger()
    functions = SemanticFunctionArena(ledger)
    quotient_arena = DiamondQuotientArena(functions)
    port, _unused_signature_binding, zero, one = carry_atoms(functions)
    declared = quotient_arena.intern_interface(
        MacroInterface(
            SemanticIdentity("tile-projection-test-v1", ("identity",)),
            (port,),
            (BOOL,) * len(COMPONENT_ROLES),
            one,
        )
    )
    interfaces = {}
    symbols = {}
    for symbol in range(3):
        bits = tuple(
            one if symbol & (1 << (index % 2)) else zero
            for index in range(len(COMPONENT_ROLES))
        )
        local = quotient_arena.intern(declared, MacroComponents(*bits))
        interfaces[symbol] = local
        symbols[local] = symbol
    actions = _Actions(ledger)
    actions.signature_id = declared
    tiles = TileArena(ledger)
    alphabet = tiles.intern_alphabet(TileAlphabet(3, 2, 2, 2, "binary", "v1"))
    results = CompletedResultArena(
        tiles,
        quotient_arena,
        action_authority=actions,
        validate_action=actions.validate_action,
        signature_for=actions.signature_for,
    )
    adapter = _IdentityAdapter(ledger, actions, tiles, interfaces, symbols)
    scheduler = TileScheduler(tiles, results, adapter)
    return ledger, actions, tiles, alphabet, scheduler, ResultWiring(declared)


def test_source_import_reads_original_leaves_and_compacts_padding() -> None:
    ledger, _, tiles, alphabet, _, _ = _runtime()
    source = ExactSource((1, 0, 1), 2, blank=2, extent=7, alphabet_size=2)
    geometry = SourceGeometry(ledger, source)
    root = import_exact_source(source, geometry, tiles, alphabet)
    try:
        assert tiles.resolve(root.tile).width == 8
        assert tuple(tiles.point(root.tile, index) for index in range(8)) == (
            1,
            0,
            1,
            2,
            2,
            2,
            2,
            2,
        )
        blank_nodes = [
            record
            for record in tiles._nodes.values()
            if record.symbol == 2
            or (record.symbol is None and record.first_active is None)
        ]
        assert len(blank_nodes) <= 4
        assert ledger.counters["source_leaf_reads"] == 3
    finally:
        root.close()


def test_source_import_padding_builds_one_monotonic_blank_tower() -> None:
    ledger, _, tiles, alphabet, _, _ = _runtime()
    extent = 1 << 100
    source = ExactSource((1,), 2, blank=2, extent=extent, alphabet_size=2)
    geometry = SourceGeometry(ledger, source)
    root = import_exact_source(source, geometry, tiles, alphabet)
    try:
        assert tiles.resolve(root.tile).width == extent
        assert ledger.counters["source_leaf_reads"] == 1
        assert ledger.counters["tile_intern_requests"] <= 4 * extent.bit_length()
        # SourceGeometry authenticates only the supplied source.  It does not
        # materialize the enormous blank extension in its exact source DAG.
        assert geometry._read_root is not None
        assert geometry._read_root.end == 1
    finally:
        root.close()


def test_lazy_projection_points_width_and_explicit_endpoint_tiles() -> None:
    ledger, actions, tiles, alphabet, scheduler, wiring = _runtime()
    source = ExactSource((1, 0, 1), 2, blank=2, extent=7, alphabet_size=2)
    geometry = SourceGeometry(ledger, source)
    projection = LazyProjection(
        scheduler,
        actions.action,
        source,
        geometry,
        alphabet,
        (0,),
        wiring,
    )
    try:
        assert projection.point(0) == 1
        assert projection.point(2) == 1
        assert projection.active_width() == 3
        before = projection.retained_entries()
        endpoint = tuple(projection.iter_endpoint_tiles())
        assert len(endpoint) == 3
        assert tuple(tiles.point(tile, 0) for tile in endpoint) == (
            1,
            0,
            1,
        )
        assert projection.retained_entries() >= before
    finally:
        projection.close()
    with pytest.raises(ValueError, match="closed"):
        projection.point(0)
    assert_rejected_atomically(
        ledger, lambda: projection.active_width(), ValueError, match="closed"
    )


def test_projection_validates_action_and_ports_before_source_import() -> None:
    ledger, actions, _tiles, alphabet, scheduler, wiring = _runtime()
    source = ExactSource((1,), 2, blank=2, extent=1, alphabet_size=2)
    geometry = SourceGeometry(ledger, source)
    snapshot = ledger.snapshot()
    foreign = FieldCellActionID(ArenaToken("foreign"), actions.action.kind, 0)
    with pytest.raises(ValueError, match="different arena"):
        LazyProjection(
            scheduler,
            foreign,
            source,
            geometry,
            alphabet,
            (0,),
            wiring,
        )
    assert geometry._read_root is None
    assert ledger.snapshot() == snapshot

    with pytest.raises(TypeError, match="exact immutable integers"):
        LazyProjection(
            scheduler,
            actions.action,
            source,
            geometry,
            alphabet,
            (False,),
            wiring,
        )
    assert geometry._read_root is None
    assert ledger.snapshot() == snapshot

    foreign_wiring = ResultWiring(
        PortSignatureID(
            ArenaToken("foreign-signature"),
            wiring.signature.kind,
            0,
        )
    )
    with pytest.raises(ValueError, match="different arena"):
        LazyProjection(
            scheduler,
            actions.action,
            source,
            geometry,
            alphabet,
            (0,),
            foreign_wiring,
        )
    assert geometry._read_root is None
    assert ledger.snapshot() == snapshot


def test_endpoint_iterator_pins_output_after_projection_closes() -> None:
    ledger, actions, tiles, alphabet, scheduler, wiring = _runtime()
    source = ExactSource((1, 0, 1), 2, blank=2, extent=4, alphabet_size=2)
    projection = LazyProjection(
        scheduler,
        actions.action,
        source,
        SourceGeometry(ledger, source),
        alphabet,
        (0,),
        wiring,
    )
    assert any(root is projection for root in ledger.iter_execution_roots())
    endpoint = projection.iter_endpoint_tiles()
    first = next(endpoint)
    projection.close()
    symbols = [tiles.point(first, 0)]
    symbols.extend(tiles.point(tile, 0) for tile in endpoint)
    assert tuple(symbols) == (1, 0, 1)
    assert ledger.counters["tile_endpoint_emissions"] == 3


def test_source_import_rejects_foreign_geometry_and_alphabet_before_tiles() -> None:
    ledger, _, tiles, alphabet, _, _ = _runtime()
    source = ExactSource((1,), 2, blank=2, extent=1, alphabet_size=2)
    foreign_ledger = ResourceLedger()
    foreign_geometry = SourceGeometry(foreign_ledger, source)
    assert_rejected_atomically(
        ledger,
        lambda: import_exact_source(source, foreign_geometry, tiles, alphabet),
        ValueError,
        match="one index ledger",
    )

    geometry = SourceGeometry(ledger, source)
    wrong = tiles.intern_alphabet(TileAlphabet(4, 3, 2, 2, "binary", "wrong"))
    retained = ledger.entries, ledger.nodes
    with pytest.raises(ValueError, match="does not describe"):
        import_exact_source(source, geometry, tiles, wrong)
    assert (ledger.entries, ledger.nodes) == retained


@pytest.mark.parametrize(
    ("effect", "values"),
    (
        (BaseBlockEffect(3), (2, 4, 2)),
        (BaseBlockEffect(10), (7, 12, 4)),
        (CollatzPhysicalBlockEffect(), (1, 0, 1, 1)),
    ),
)
def test_actual_primitive_family_projection_matches_independent_oracle(
    effect: BaseBlockEffect | CollatzPhysicalBlockEffect,
    values: tuple[int, ...],
) -> None:
    width = 8
    expected = tuple(oracle(effect, values, width, 1))
    ledger, tiles, adapter, action, scheduler = primitive_runtime(effect)
    source = ExactSource(
        values,
        effect.base,
        blank=effect.blank,
        extent=width,
        alphabet_size=effect.blank,
    )
    geometry = SourceGeometry(ledger, source)
    projection = LazyProjection(
        scheduler,
        action,
        source,
        geometry,
        adapter.alphabet(action),
        adapter.initial_ports(action),
        adapter.wiring(action),
    )
    try:
        assert tuple(projection.point(index) for index in range(width)) == expected
        active = max(
            (
                index + 1
                for index, symbol in enumerate(expected)
                if symbol != effect.blank
            ),
            default=0,
        )
        assert projection.active_width() == active
        endpoint = tuple(projection.iter_endpoint_tiles())
        assert tuple(tiles.point(tile, 0) for tile in endpoint) == expected[:active]
    finally:
        projection.close()
