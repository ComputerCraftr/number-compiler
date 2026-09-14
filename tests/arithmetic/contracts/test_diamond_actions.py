from __future__ import annotations

from dataclasses import replace
from typing import Literal, Never, cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.exact_tree_context import source_reads_only
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
    ExactSource,
)
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.hashlife.actions.diamond_actions import (
    BoundedCellAction,
    CellID,
    FormalSymbolID,
    ImageCellArena,
    PortProgramID,
    PortSignature,
    PortSignatureID,
    TemporalActionArena,
)
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.resources.ledger import ResourceLedger
from tests.support.diamond_actions import arenas


def test_temporal_adapter_imports_binary_dag_and_keeps_real_identity() -> None:
    ledger, compiler, actions, _, first, second = arenas()
    root = compiler.compose(
        compiler.resolve(actions.primitive_reference(first)),
        compiler.resolve(actions.primitive_reference(second)),
    )
    imported = actions.intern(root)
    assert imported == actions.compose(first, second)
    assert actions.node(imported).first == first.local_id
    assert actions.node(imported).second == second.local_id
    assert actions.power(first, 0) == actions.identity
    assert actions.compose(actions.identity, first) == first
    assert actions.primitive(first).base == 10
    result = actions.power(first, 1 << 30)
    assert actions.node(result).exponent == 1 << 30
    assert len(actions._nodes) < 40
    assert all(row.accounting_delta == 0 for row in ledger.inventory())


def test_nested_images_normalize_before_cell_lookup_without_emission() -> None:
    ledger, _, actions, cells, first, second = arenas()
    source = cells.source(0, 4)
    combined = actions.compose(first, second)
    expected = cells.image(combined, source)
    intermediate = cells.image(first, source)
    before = len(cells._nodes)

    @source_reads_only
    def query() -> CellID:
        result = cells.image(second, intermediate)
        left, right = cells.split(result)
        assert cells.node(left).kind == cells.node(right).kind == "slice"
        assert cells.join(left, right) == result
        assert cells.mirror(cells.mirror(result)) == result
        with pytest.raises(ValueError, match="original-source"):
            cells.source_symbol(left)
        return result

    assert query() == expected
    assert len(cells._nodes) == before + 3  # two slices and one mirror
    assert ledger.counters["diamond_cell_interner_hits"] > 0
    assert not any(
        hasattr(node, "digits") or hasattr(node, "symbol") for node in cells._nodes
    )


def test_equal_original_tiles_share_cell_ids_and_nonpower_forest_is_exact() -> None:
    _, _, _, cells, _, _ = arenas(length=13)
    assert cells.source(4, 1) == cells.source(6, 1)
    forest = cells.source_span(0, 13)
    assert tuple(start for start, _ in forest) == (0, 8, 12)
    assert tuple(cells.node(cell).width for _, cell in forest) == (8, 4, 1)
    assert cells.source_forest() == tuple(cell for _, cell in forest)
    assert cells.source_symbol(cells.source(1, 0)) == 18
    parent = cells.source(0, 3)
    assert cells.join(*cells.split(parent)) == parent


def test_foreign_action_and_cell_reject_before_warm_and_identity_paths() -> None:
    ledger, _, actions, cells, first, _ = arenas()
    _, _, other_actions, other_cells, other_first, _ = arenas()
    source, foreign = cells.source(0, 4), other_cells.source(0, 4)
    cells.image(first, source)
    before = ledger.snapshot()
    with pytest.raises(ValueError):
        cells.image(other_first, source)
    with pytest.raises(ValueError):
        cells.image(actions.identity, foreign)
    with pytest.raises(ValueError):
        actions.power(other_actions.identity, 0)
    with pytest.raises(ValueError):
        cells.slice(foreign, 0, 4)
    with pytest.raises(ValueError):
        cells.resolve(CellID(cells.token, "diamond-cell", len(cells._nodes)))
    with pytest.raises(TypeError):
        cells.resolve(cast("CellID", ActionProgramID(cells.token, "diamond-cell", 0)))
    assert ledger.snapshot() == before


def test_failed_action_or_cell_publication_reserves_both_stores_atomically() -> None:
    ledger, _, actions, cells, first, second = arenas()
    source = cells.source(0, 4)
    ledger.max_cache_entries = ledger.entries + 1
    before = ledger.snapshot()
    with pytest.raises(BlockContextBudgetExceeded):
        actions.compose(first, second)
    assert ledger.snapshot() == before
    with pytest.raises(BlockContextBudgetExceeded):
        cells.mirror(source)
    assert ledger.snapshot() == before


def test_import_reservation_is_atomic_across_whole_compiler_dag() -> None:
    ledger, compiler, actions, _, first, _ = arenas()
    root = compiler.power(actions.primitive(first), 16).root
    assert root is not None
    ledger.max_cache_entries = ledger.entries + 2
    before = ledger.snapshot()
    with pytest.raises(BlockContextBudgetExceeded):
        actions.intern(root)
    assert ledger.snapshot() == before


def test_composed_port_signatures_use_children_not_product_domains() -> None:
    owner = ArenaToken("ports")
    first = PortSignatureID(owner, "diamond-port-signature", 0)
    second = PortSignatureID(owner, "diamond-port-signature", 1)
    signature = PortSignature(10, 20, None, None, first=first, second=second)
    program = PortProgramID(owner, "diamond-port-program", 0)
    action = BoundedCellAction(
        signature, program, program, program, program, program, program
    )
    assert action.output == program
    with pytest.raises(ValueError, match="product"):
        replace(signature, left_domain=757)
    with pytest.raises(ValueError, match="one port arena"):
        replace(action, output=PortProgramID(ArenaToken(), "diamond-port-program", 0))
    with pytest.raises(ValueError, match="one port arena"):
        replace(action, output=PortProgramID(owner, "summary", 0))


def test_eviction_cannot_recycle_canonical_actions_or_images() -> None:
    ledger, _, actions, cells, first, second = arenas()
    source = cells.source(0, 4)
    composed = actions.compose(first, second)
    image = cells.image(composed, source)
    ledger.evict_query_memos()
    assert actions.compose(first, second) == composed
    assert cells.image(composed, source) == image


def test_nested_image_budget_failure_does_not_publish_its_composed_action() -> None:
    ledger, _, actions, cells, first, second = arenas()
    source = cells.source(0, 4)
    inner = cells.image(first, source)
    ledger.max_cache_entries = ledger.entries + 2
    before = ledger.snapshot()
    with pytest.raises(BlockContextBudgetExceeded):
        cells.image(second, inner)
    assert ledger.snapshot() == before
    assert actions.node(first).kind == "atom"


def test_primitive_signature_binds_actual_kernel_and_roles() -> None:
    from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena

    ledger, _, actions, _, first, _ = arenas()
    kernels = DiamondKernelArena(ledger)
    kernel = kernels.intern(actions.primitive(first))
    primitive = kernels.kernel(kernel)
    signature = PortSignature(
        10, 20, primitive.left_count, primitive.right_count, kernel=kernel
    )
    signature.validate_kernel(kernels)
    assert signature.admissibility == "primitive"
    with pytest.raises(ValueError, match="does not describe"):
        replace(signature, right_domain=1).validate_kernel(kernels)
    with pytest.raises(ValueError, match="direction"):
        replace(signature, left_role=cast("Literal['left-boundary']", "right-boundary"))
    other = DiamondKernelArena(ledger)
    other.intern(actions.primitive(first))
    with pytest.raises(ValueError):
        signature.validate_kernel(other)


def test_source_join_uses_child_ids_when_representatives_are_not_siblings() -> None:
    ledger = ResourceLedger()
    compiler = LazyCompiler(ledger)
    actions = TemporalActionArena(compiler)
    source = (1, 2, 2, 3, 2, 2)
    geometry = SourceGeometry(
        ledger, ExactSource(source, 10, "generic", 19, 16, alphabet_size=19)
    )
    geometry.span(source, 19, 16)
    cells = ImageCellArena(actions, geometry)
    # The first occurrence of symbol2 is position1, not an aligned parent start.
    repeated = cells.source(1, 0)
    assert cells.source(4, 0) == repeated
    parent = cells.source(4, 1)
    count = len(cells._nodes)

    @source_reads_only
    def query() -> None:
        assert cells.join(repeated, repeated) == parent
        # The first padding pair occurs at6; the matching four-cell parent is8.
        padding = cells.source(6, 1)
        assert cells.join(padding, padding) == cells.source(8, 2)

    query()
    assert len(cells._nodes) == count + 2


def test_formal_alphabet_is_implicit_kernel_constants_without_geometry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, _, _, cells, _, _ = arenas()
    before = ledger.snapshot()
    source_nodes = tuple(cells.source_geometry.nodes.items())
    ledger.max_nodes = ledger.nodes
    ledger.max_cache_entries = ledger.entries

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("formal alphabet allocated or read source geometry")

    monkeypatch.setattr(cells.source_geometry, "read", forbidden)
    monkeypatch.setattr(cells.source_geometry, "tile_at", forbidden)

    @source_reads_only
    def compile_cofactors() -> None:
        # These are alternative ORIGINAL alphabet inputs, including blank19,
        # never a sequence of observed future outputs.
        for index in range(20):
            formal = cells.formal_symbol(index)
            assert formal == cells.formal_symbol(index)
            assert cells.validate_input(formal) == formal
            assert cells.input_level(formal) == 0
            assert cells.input_symbol(formal) == index
            with pytest.raises(TypeError, match="spatial cell"):
                cells.resolve(cast("CellID", formal))

    compile_cofactors()
    assert ledger.snapshot() == before
    assert tuple(cells.source_geometry.nodes.items()) == source_nodes
    assert not cells._nodes


def test_formal_symbol_rejects_foreign_kind_and_domain_before_any_mutation() -> None:
    ledger, _, _, cells, _, _ = arenas()
    _, _, _, other, _, _ = arenas()
    valid = cells.formal_symbol(0)
    for method in (cells.validate_input, cells.input_level, cells.input_symbol):
        assert method(valid) is not None  # exercise each warm interface first
        for invalid in (
            other.formal_symbol(0),
            FormalSymbolID(cells.formal_token, "diamond-cell", 0),
            FormalSymbolID(cells.formal_token, "diamond-formal-symbol", 20),
        ):
            before = ledger.snapshot()
            with pytest.raises(ValueError):
                method(invalid)
            assert ledger.snapshot() == before
    for invalid_symbol in (-1, 20, 10**100, True, 0.0):
        before = ledger.snapshot()
        with pytest.raises((TypeError, ValueError)):
            cells.formal_symbol(cast("int", invalid_symbol))
        assert ledger.snapshot() == before


def test_boundary_binding_accepts_only_own_formal_original_alphabet() -> None:
    from number_compiler.hashlife.interfaces.diamond_boundary import (
        BoundaryActionArena,
        ImageBinding,
    )
    from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena

    ledger, _, actions, cells, _, _ = arenas()
    boundaries = BoundaryActionArena(actions, DiamondKernelArena(ledger), cells)
    left = boundaries.literal(actions.identity, 0, 0)
    right = boundaries.literal(actions.identity, 1, 0)
    binding = ImageBinding(actions.identity, cells.formal_symbol(19), left, right)
    boundaries.validate_binding(binding)
    _, _, _, other, _, _ = arenas()
    before = ledger.snapshot()
    for invalid in (
        other.formal_symbol(19),
        FormalSymbolID(cells.formal_token, "diamond-formal-symbol", 20),
    ):
        with pytest.raises(ValueError):
            boundaries.validate_binding(replace(binding, cell=invalid))
        assert ledger.snapshot() == before
