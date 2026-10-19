"""Primitive bimachines execute through canonical tiles and finite interfaces."""

from __future__ import annotations

from array import array
from collections.abc import Mapping
from typing import Never, cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BoundarySide
from number_compiler.arithmetic.contracts.block_kernel import (
    BaseBlockEffect,
    FiniteBlockEffect,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.actions.lazy_compiler import UnsupportedInterfaceError
from number_compiler.hashlife.execution.tile_fused_kernel import leaf_product
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.interfaces import tile_reverse_functions
from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena
from number_compiler.hashlife.interfaces.diamond_quotient import DiamondQuotientArena
from number_compiler.hashlife.interfaces.semantic_bits import FactoredFunctionID
from number_compiler.hashlife.tiles.tile_context import ChildContext
from number_compiler.hashlife.tiles.tile_ports import ResultWiring
from number_compiler.hashlife.tiles.tiles import (
    TileAlphabet,
    TileArena,
    TileID,
    TileLease,
)
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from number_compiler.sequences.collatz.tile_family_hooks import (
    collatz_compatibility_tile_hooks,
    collatz_tile_hooks,
)
from tests.support.assertions import assert_rejected_atomically
from tests.support.tile_kernel import (
    literal_tile_output,
    make_tile_from_symbols,
    make_tile_runtime,
    make_tile_runtime_source,
    read_tile_symbols,
    runtime_signature,
)


def test_fused_leaf_reuses_direct_kernel_symbol_before_compilation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, _unused_tiles_binding, adapter, primitive, _scheduler, source = (
        make_tile_runtime_source(BaseBlockEffect(3), (0,))
    )
    action = adapter.power(primitive, 2)
    wiring = adapter.wiring(primitive)
    ports = adapter.initial_ports(primitive)
    try:
        direct = adapter.leaf_interface(primitive, source.tile, wiring)
        before = ledger.counters.get("tile_leaf_product_evaluations", 0)

        def forbidden(*_args: object) -> Never:
            raise AssertionError("fused output rebuilt a known kernel-symbol function")

        monkeypatch.setattr(adapter, "leaf_components", forbidden)
        monkeypatch.setattr(
            tile_reverse_functions, "reverse_leaf_components", forbidden
        )
        fused = adapter.fused_interface(action, source.tile, ports, wiring)
        assert fused == direct
        assert ledger.counters.get("tile_leaf_product_evaluations", 0) == before
        assert ledger.counters["tile_leaf_product_early_hits"] >= 1
    finally:
        source.close()


@pytest.mark.parametrize("bad", (False, True, 0.0, 1.0, -1, 6))
def test_leaf_product_rejects_symbol_alias_before_warm_lookup(
    bad: bool | float,
) -> None:
    ledger, _tiles, adapter, action, _scheduler = make_tile_runtime(BaseBlockEffect(3))
    wiring = adapter.wiring(action)
    leaf_product(adapter, action, 0, wiring)
    leaf_product(adapter, action, 1, wiring)
    assert_rejected_atomically(
        ledger,
        lambda: leaf_product(adapter, action, cast("int", bad), wiring),
        (TypeError, ValueError),
    )


def test_leaf_product_budget_rejects_before_kernel_work(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, _tiles, adapter, action, _scheduler = make_tile_runtime(BaseBlockEffect(3))
    wiring = adapter.wiring(action)
    before = ledger.snapshot()
    ledger.max_cache_entries = before.entries

    def forbidden(*_args: object) -> Never:
        raise AssertionError("exhausted leaf reservation executed the kernel")

    monkeypatch.setattr(adapter, "leaf_components", forbidden)
    monkeypatch.setattr(tile_reverse_functions, "reverse_leaf_components", forbidden)
    with pytest.raises(RuntimeError):
        leaf_product(adapter, action, 0, wiring)
    after = ledger.snapshot()
    assert after.entries == before.entries
    assert after.nodes == before.nodes
    assert after.inventory == before.inventory


def test_result_shape_uses_one_combined_action_signature_validation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _ledger, _tiles, adapter, action, scheduler, ports, wiring = runtime_signature(
        BaseBlockEffect(3)
    )
    original = adapter.validate_action
    calls = 0

    def counted(value: FieldCellActionID) -> None:
        nonlocal calls
        calls += 1
        original(value)

    monkeypatch.setattr(adapter, "validate_action", counted)
    scheduler.results.validate_shape(action, ports, wiring)
    assert calls == 1


def test_leaf_product_failed_construction_rolls_back_binding_reservation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, _tiles, adapter, action, _scheduler = make_tile_runtime(BaseBlockEffect(3))
    wiring = adapter.wiring(action)
    before = ledger.snapshot()

    def broken(*_args: object) -> Never:
        raise RuntimeError("injected leaf compiler failure")

    monkeypatch.setattr(adapter, "leaf_components", broken)
    monkeypatch.setattr(tile_reverse_functions, "reverse_leaf_components", broken)
    with pytest.raises(RuntimeError, match="injected leaf"):
        leaf_product(adapter, action, 0, wiring)
    after = ledger.snapshot()
    assert after.entries == before.entries
    assert after.nodes == before.nodes
    assert after.inventory == before.inventory


def test_leaf_function_reuse_survives_source_tile_retirement(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, tiles, adapter, action, _scheduler = make_tile_runtime(BaseBlockEffect(3))
    wiring = adapter.wiring(action)
    original = make_tile_from_symbols(tiles, adapter, action, (2,))
    retired = original.tile
    expected = adapter.leaf_interface(action, retired, wiring)
    original.close()
    with pytest.raises(ValueError):
        tiles.resolve(retired)
    replacement = make_tile_from_symbols(tiles, adapter, action, (2,))
    try:
        assert replacement.tile != retired

        def forbidden(*_args: object) -> Never:
            raise AssertionError("source retirement discarded semantic leaf reuse")

        monkeypatch.setattr(adapter, "leaf_components", forbidden)
        monkeypatch.setattr(
            tile_reverse_functions, "reverse_leaf_components", forbidden
        )
        assert adapter.leaf_interface(action, replacement.tile, wiring) == expected
        assert ledger.counters["tile_leaf_product_early_hits"] >= 1
    finally:
        replacement.close()


def test_decimal_leaf_interface_uses_exact_factored_output_law() -> None:
    effect = BaseBlockEffect(10)
    ledger, _tiles, adapter, action, _scheduler = make_tile_runtime(effect)
    kernel = adapter.primitive_law(action)
    wiring = adapter.wiring(action)
    before = ledger.counters.get("reverse_port_primitive_output_evaluations", 0)
    for symbol in range(effect.blank + 1):
        interface = leaf_product(adapter, action, symbol, wiring)
        for left in range(kernel.left_count):
            for right in range(kernel.right_count):
                expected = effect.emit(
                    kernel.decode(BoundarySide.LEFT, left),
                    symbol,
                    kernel.decode(BoundarySide.RIGHT, right),
                )
                assert adapter.observe(interface, "output", (left, right)) == expected
    assert ledger.counters.get(
        "reverse_port_primitive_output_evaluations", 0
    ) - before == ((effect.blank + 1) * kernel.left_count * kernel.right_count)
    assert ledger.counters.get("reverse_port_predicate_state_evaluations", 0) == 0


@pytest.mark.parametrize("base", (2, 3, 4, 5, 10))
def test_reverse_primitive_complete_tile_matches_exact_bimachine(base: int) -> None:
    effect = BaseBlockEffect(base)
    _ledger, tiles, adapter, action, scheduler = make_tile_runtime(effect)
    source_symbols = (0, base - 1, 2 * base - 2, effect.blank)
    source = make_tile_from_symbols(tiles, adapter, action, source_symbols)
    try:
        result = scheduler.complete(
            action,
            source.tile,
            adapter.initial_ports(action),
            adapter.wiring(action),
        )
        try:
            assert read_tile_symbols(tiles, result.output) == literal_tile_output(
                effect, source_symbols
            )
            assert result.result.relative_extent == tiles.resolve(result.output).extent
            assert result.result.physical_ticks == 1
        finally:
            result.close()
    finally:
        source.close()


def test_physical_collatz_primitive_complete_tile_matches_exact_bimachine() -> None:
    effect = CollatzPhysicalBlockEffect()
    _ledger, tiles, adapter, action, scheduler = make_tile_runtime(effect)
    source_symbols = (1, 0, 1, effect.blank)
    source = make_tile_from_symbols(tiles, adapter, action, source_symbols)
    try:
        result = scheduler.complete(
            action,
            source.tile,
            adapter.initial_ports(action),
            adapter.wiring(action),
        )
        try:
            assert read_tile_symbols(tiles, result.output) == literal_tile_output(
                effect, source_symbols
            )
            assert result.result.physical_ticks == 1
        finally:
            result.close()
    finally:
        source.close()


def test_primitive_cold_point_materializes_only_one_output_leaf() -> None:
    effect = BaseBlockEffect(10)
    ledger, _unused_tiles_binding, adapter, action, scheduler, source = (
        make_tile_runtime_source(effect, (2, 7, 11, effect.blank))
    )
    try:
        before = ledger.counters.get("tile_publications", 0)
        expected = literal_tile_output(effect, (2, 7, 11, effect.blank))[2]
        assert (
            scheduler.point(
                action,
                source.tile,
                adapter.initial_ports(action),
                adapter.wiring(action),
                2,
            )
            == expected
        )
        assert ledger.counters.get("tile_publications", 0) - before <= 1
        assert ledger.counters["tile_scheduler_leaf_function_applications"] == 1
        assert ledger.counters.get("tile_scheduler_spatial_compositions", 0) == 0
    finally:
        source.close()


def test_primitive_adapter_rejects_temporal_composition_instead_of_replay() -> None:
    effect = BaseBlockEffect(3)
    _ledger, _unused_tiles_binding, adapter, action, scheduler, source = (
        make_tile_runtime_source(effect, (0, effect.blank))
    )
    try:
        result = scheduler.complete(
            action,
            source.tile,
            adapter.initial_ports(action),
            adapter.wiring(action),
        )
        try:
            with pytest.raises(ValueError, match="not the canonical second child"):
                adapter.temporal_after_context(
                    action,
                    action,
                    result.result,
                    adapter.initial_ports(action),
                    adapter.wiring(action),
                )
        finally:
            result.close()
    finally:
        source.close()


def test_tile_alphabet_is_independent_of_the_producing_kernel() -> None:
    ledger = ResourceLedger()
    kernels = DiamondKernelArena(ledger)
    interfaces = DiamondQuotientArena(SemanticFunctionArena(ledger))
    tiles = TileArena(ledger)
    adapter = PrimitiveTileKernelAdapter(tiles, kernels, interfaces)
    reverse = adapter.admit(BaseBlockEffect(3))
    normalize = adapter.admit(DigitNormalizeBlockEffect(3))
    assert reverse != normalize
    assert adapter.alphabet(reverse) == adapter.alphabet(normalize)
    first = tiles.leaf(adapter.alphabet(reverse), 2)
    second = tiles.leaf(adapter.alphabet(normalize), 2)
    try:
        assert first.tile == second.tile
    finally:
        first.close()
        second.close()


def test_adapter_admission_hooks_reject_wrong_alphabet_and_unfused_action_purely() -> (
    None
):
    ledger, tiles, adapter, primitive, _scheduler = make_tile_runtime(
        BaseBlockEffect(3)
    )
    wrong = tiles.intern_alphabet(
        TileAlphabet(
            4,
            3,
            3,
            2,
            "another-cell-interpretation",
            "canonical-tile-alphabet-v1",
        )
    )
    leaf = tiles.leaf(wrong, 1)
    try:
        before = ledger.snapshot()
        with pytest.raises(ValueError, match="alphabet differs"):
            adapter.validate_input(primitive, leaf.tile)
        with pytest.raises(ValueError, match="alphabet differs"):
            adapter.validate_output(primitive, leaf.tile)
        with pytest.raises(UnsupportedInterfaceError, match="no bounded fused"):
            adapter.validate_fused_action(primitive)
        assert ledger.snapshot() == before
    finally:
        leaf.close()


def test_primitive_rejects_a_right_boundary_changed_by_dyadic_padding() -> None:
    effect = FiniteBlockEffect(
        base=2,
        exponent=1,
        left_count=1,
        right_count=2,
        alphabet_size=4,
        initial_left=0,
        initial_right=0,
        left_transitions=array("I", (0,) * 4),
        right_transitions=array("I", (0, 0, 0, 1, 1, 1, 1, 1)),
        outputs=bytes(
            symbol for _left in range(1) for symbol in range(4) for _right in range(2)
        ),
        kernel_name="padding-counterexample",
        storage_bytes=0,
        uncompressed_bytes=0,
        blank_left_tail=0,
        blank_right_tail=1,
        stable_blank_output=True,
    )
    ledger = ResourceLedger()
    adapter = PrimitiveTileKernelAdapter(
        TileArena(ledger),
        DiamondKernelArena(ledger),
        DiamondQuotientArena(SemanticFunctionArena(ledger)),
        family_hooks=collatz_tile_hooks(),
    )
    with pytest.raises(ValueError, match="right boundary.*blank padding"):
        adapter.admit(effect)


def test_weighted_tile_runtime_rejects_proof_c4_without_event_channel() -> None:
    from number_compiler.sequences.collatz.physical_kernel import (
        PhysicalCollatzFourBlockEffect,
    )

    ledger = ResourceLedger()
    adapter = PrimitiveTileKernelAdapter(
        TileArena(ledger),
        DiamondKernelArena(ledger),
        DiamondQuotientArena(SemanticFunctionArena(ledger)),
        family_hooks=collatz_compatibility_tile_hooks(PhysicalCollatzFourBlockEffect()),
    )
    with pytest.raises(ValueError, match="no certified odd-event output channel"):
        adapter.admit(PhysicalCollatzFourBlockEffect())


def test_distinct_tile_witnesses_reuse_canonical_child_interface_pair(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _ledger, tiles, adapter, action, _scheduler = make_tile_runtime(BaseBlockEffect(2))
    wiring = adapter.wiring(action)
    first_left = make_tile_from_symbols(tiles, adapter, action, (0, 0, 0, 0))
    second_left = make_tile_from_symbols(tiles, adapter, action, (0, 1, 0, 0))
    right = make_tile_from_symbols(tiles, adapter, action, (0, 0, 0, 0))
    first_root = tiles.join(first_left.tile, right.tile)
    second_root = tiles.join(second_left.tile, right.tile)
    try:
        first_effect = adapter.compile_interface(action, first_left.tile, wiring)
        second_effect = adapter.compile_interface(action, second_left.tile, wiring)
        assert first_left.tile != second_left.tile
        assert first_effect == second_effect
        expected = adapter.compile_interface(action, first_root.tile, wiring)
        nodes = len(adapter.quotients._nodes)
        hits = adapter.ledger.counters.get(
            "spatial_interface_composition_early_hits",
            0,
        )

        def poisoned(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("canonical spatial pair replayed its reducer")

        monkeypatch.setattr(adapter, "parent_components", poisoned)
        actual = adapter.compile_interface(action, second_root.tile, wiring)
        assert actual == expected
        assert len(adapter.quotients._nodes) == nodes
        assert (
            adapter.ledger.counters["spatial_interface_composition_early_hits"] > hits
        )
    finally:
        first_root.close()
        second_root.close()
        first_left.close()
        second_left.close()
        right.close()


@pytest.mark.parametrize("base", (2, 3, 10, 15))
def test_bounded_reverse_parent_interface_composes_without_substitution(
    monkeypatch: pytest.MonkeyPatch,
    base: int,
) -> None:
    _ledger, _unused_tiles_binding, adapter, action, _scheduler, source = (
        make_tile_runtime_source(BaseBlockEffect(base), (base - 1, 2 * base - 2))
    )
    substitutions = _substitution_counter(monkeypatch, adapter)
    try:
        adapter.compile_interface(action, source.tile, adapter.wiring(action))
        assert substitutions[0] == 0
        assert adapter.ledger.counters["reverse_port_parent_interfaces"] == 1
        assert adapter.ledger.counters["spatial_interface_composition_requests"] == 1
        assert (
            adapter.ledger.counters["spatial_interface_composition_publications"] == 1
        )
        assert (
            adapter.ledger.counters.get("spatial_interface_composition_late_aliases", 0)
            == 0
        )
    finally:
        source.close()


def test_uncertified_reverse_base_keeps_generic_finite_compiler(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _ledger, _unused_tiles_binding, adapter, action, _scheduler, source = (
        make_tile_runtime_source(BaseBlockEffect(16), (15, 30))
    )
    substitutions = _substitution_counter(monkeypatch, adapter)
    try:
        adapter.compile_interface(action, source.tile, adapter.wiring(action))
        assert substitutions[0] > 0
        assert adapter.ledger.counters.get("reverse_port_parent_interfaces", 0) == 0
    finally:
        source.close()


def test_fused_leaf_accepts_noninitial_producer_ports() -> None:
    effect = BaseBlockEffect(10)
    _ledger, tiles, adapter, primitive, _scheduler = make_tile_runtime(effect)
    action = adapter.power(primitive, 2)
    leaf = tiles.leaf(adapter.alphabet(primitive), 18)
    try:
        signature = adapter.quotients.interface(adapter.signature_for(action))
        producer = tuple(port.cardinality - 1 for port in signature.inputs)
        consumer = adapter.initial_ports(primitive)
        result = adapter.fused_leaf_result(
            action,
            leaf.tile,
            producer,
            consumer,
            adapter.wiring(action),
        )
        kernel = adapter.kernels.kernel(adapter._action(primitive).kernel)
        first = kernel.emit(producer[0], 18, producer[1])
        assert result.symbol == kernel.emit(consumer[0], first, consumer[1])
    finally:
        leaf.close()


def test_warm_fused_parent_interface_skips_children_and_reducer(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    adapter, action, source, ports, wiring = _fused_parent(2)
    try:
        expected = adapter.fused_interface(action, source.tile, ports, wiring)

        def poisoned(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("warm fused interface replayed child reduction")

        monkeypatch.setattr(adapter, "parent_components", poisoned)
        monkeypatch.setattr(adapter, "child_context", poisoned)
        assert adapter.fused_interface(action, source.tile, ports, wiring) == expected
    finally:
        source.close()


def test_cold_fused_parent_computes_each_child_context_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    adapter, action, source, ports, wiring = _fused_parent(3)
    original = adapter.child_context
    seen: set[tuple[TileID, tuple[int, ...], int]] = set()

    def once(
        current_action: FieldCellActionID,
        parent: TileID,
        left: TileID,
        right: TileID,
        current_ports: tuple[int, ...],
        current_wiring: ResultWiring,
        side: int,
    ) -> ChildContext:
        key = parent, current_ports, side
        if key in seen:
            raise AssertionError("fused parent recomputed a child context")
        seen.add(key)
        return original(
            current_action,
            parent,
            left,
            right,
            current_ports,
            current_wiring,
            side,
        )

    try:
        monkeypatch.setattr(adapter, "child_context", once)
        adapter.fused_interface(action, source.tile, ports, wiring)
        assert len(seen) == 6
    finally:
        source.close()


def test_failed_fused_parent_releases_charged_traversal_workspace(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.hashlife.execution.tile_causal_interfaces as interfaces

    ledger, tiles, adapter, primitive, _scheduler = make_tile_runtime(
        BaseBlockEffect(3)
    )
    action = adapter.power(primitive, 2)
    source = make_tile_from_symbols(tiles, adapter, primitive, (0, 1))

    def fail_parent(*_args: object, **_kwargs: object) -> Never:
        raise RuntimeError("injected fused parent failure")

    try:
        monkeypatch.setattr(interfaces, "combine_local_interfaces", fail_parent)
        with pytest.raises(RuntimeError, match="fused parent failure"):
            adapter.fused_interface(
                action,
                source.tile,
                adapter.initial_ports(primitive),
                adapter.wiring(action),
            )
        account = ledger.inventory()[adapter._fused_workspace.owner]
        assert adapter._fused_workspace.active is False
        assert adapter._fused_workspace.nodes == 0
        assert (account.nodes, account.observed_nodes) == (0, 0)
    finally:
        source.close()


def test_fused_direct_api_rejects_bad_ports_sides_and_nonleaf_before_mutation() -> None:
    ledger, tiles, adapter, primitive, _scheduler = make_tile_runtime(
        BaseBlockEffect(3)
    )
    action = adapter.power(primitive, 2)
    source = make_tile_from_symbols(tiles, adapter, primitive, (0, 2))
    wiring = adapter.wiring(action)
    producer = adapter.initial_ports(primitive)
    node = tiles.resolve(source.tile)
    assert node.left is not None and node.right is not None
    try:
        for bad in ((True, 0), (0.0, 0), (10**6, 0)):
            before = ledger.snapshot()
            with pytest.raises((TypeError, ValueError)):
                adapter.fused_output_active(
                    action,
                    source.tile,
                    producer,
                    cast("tuple[int, ...]", bad),
                    wiring,
                )
            with pytest.raises((TypeError, ValueError)):
                adapter.fused_leaf_result(
                    action,
                    node.left,
                    producer,
                    cast("tuple[int, ...]", bad),
                    wiring,
                )
            with pytest.raises((TypeError, ValueError)):
                adapter.fused_child_contexts(
                    action,
                    source.tile,
                    producer,
                    cast("tuple[int, ...]", bad),
                    wiring,
                    0,
                )
            assert ledger.snapshot() == before
        for side in (False, 0.0, -1, 2):
            before = ledger.snapshot()
            with pytest.raises((TypeError, ValueError)):
                adapter.child_context(
                    primitive,
                    source.tile,
                    node.left,
                    node.right,
                    producer,
                    wiring,
                    cast(int, side),
                )
            with pytest.raises((TypeError, ValueError)):
                adapter.fused_child_contexts(
                    action,
                    source.tile,
                    producer,
                    producer,
                    wiring,
                    cast(int, side),
                )
            assert ledger.snapshot() == before
        before = assert_rejected_atomically(
            ledger,
            lambda: adapter.fused_leaf_result(
                action, source.tile, producer, producer, wiring
            ),
            ValueError,
            match="one source symbol",
        )
    finally:
        source.close()


def _substitution_counter(
    monkeypatch: pytest.MonkeyPatch, adapter: PrimitiveTileKernelAdapter
) -> list[int]:
    substitutions = [0]
    substitute = adapter.bits.substitute

    def counted(
        function: FactoredFunctionID,
        replacements: Mapping[PortVariable, FactoredFunctionID],
        *,
        joint: bool = True,
    ) -> FactoredFunctionID:
        substitutions[0] += 1
        return substitute(function, replacements, joint=joint)

    monkeypatch.setattr(adapter.bits, "substitute", counted)
    return substitutions


def _fused_parent(
    base: int,
) -> tuple[
    PrimitiveTileKernelAdapter,
    FieldCellActionID,
    TileLease,
    tuple[int, ...],
    ResultWiring,
]:
    _ledger, tiles, adapter, primitive, _scheduler = make_tile_runtime(
        BaseBlockEffect(base)
    )
    action = adapter.power(primitive, 2)
    source = make_tile_from_symbols(tiles, adapter, primitive, (0, 1, 2, 3))
    return (
        adapter,
        action,
        source,
        adapter.initial_ports(primitive),
        adapter.wiring(action),
    )
