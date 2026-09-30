from __future__ import annotations

from tests.support.assertions import assert_rejected_atomically

from typing import TYPE_CHECKING, Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
    BoundarySide,
)
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.hashlife.actions.diamond_actions import (
    ImageCellArena,
    TemporalActionArena,
)
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.execution.diamond_pair_macros import (
    PairMacroKey,
    PrimitivePairMacros,
)
from number_compiler.hashlife.execution.diamond_primitive_pair import (
    PrimitivePairActions,
)
from number_compiler.hashlife.interfaces.diamond_boundary import BoundaryActionArena
from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
    from number_compiler.hashlife.actions.diamond_actions import CellID


def macros() -> tuple[
    PrimitivePairMacros,
    ActionProgramID,
    ActionProgramID,
    ActionProgramID,
    CellID,
    tuple[int, int, int, int],
]:
    ledger = ResourceLedger()
    compiler = LazyCompiler(ledger)
    first = compiler.atom(BaseBlockEffect(2))
    second = compiler.atom(DigitNormalizeBlockEffect(2))
    actions = TemporalActionArena(compiler)
    a, b = actions.intern(first), actions.intern(second)
    pair = actions.compose(a, b)
    source = (1, 2, 1, 2)
    geometry = SourceGeometry(
        ledger, ExactSource(source, 2, "reverse-add", 3, 4, alphabet_size=3)
    )
    geometry.span(source, 3, 4)
    cells = ImageCellArena(actions, geometry)
    kernels = DiamondKernelArena(ledger)
    boundaries = BoundaryActionArena(actions, kernels, cells)
    return PrimitivePairMacros(boundaries), pair, a, b, cells.source(0, 2), source


@pytest.mark.parametrize("side", [0, 1])
def test_parent_bilateral_context_matches_full_primitive_interface(side: int) -> None:
    arena, pair, first, second, cell, source = macros()
    summary = arena.summary(pair, cell)
    boundaries, kernels = arena.boundaries, arena.kernels
    a = kernels.kernel(kernels.intern(arena.actions.primitive(first)))
    b = kernels.kernel(kernels.intern(arena.actions.primitive(second)))
    for left in range(a.left_count):
        for right in range(a.right_count):
            lefts, rights = [left], [right]
            for symbol in source:
                lefts.append(a.advance(BoundarySide.LEFT, lefts[-1], symbol))
            for symbol in reversed(source):
                rights.append(a.advance(BoundarySide.RIGHT, rights[-1], symbol))
            rights.reverse()
            output = [
                a.emit(lefts[index], symbol, rights[index + 1])
                for index, symbol in enumerate(source)
            ]
            for incoming in range(len(b.domain(BoundarySide(side)))):
                expected = incoming
                for symbol in output if side == 0 else reversed(output):
                    expected = b.advance(BoundarySide(side), expected, symbol)
                got = arena.apply_context(
                    summary,
                    boundaries.literal(first, 0, left),
                    boundaries.literal(first, 1, right),
                    boundaries.literal(second, side, incoming),
                    side,
                )
                assert boundaries.state(got).literal == expected


@pytest.mark.parametrize("side", [0, 1])
def test_parent_action_matches_successive_finite_symbol_actions(side: int) -> None:
    arena, pair, first, second, cell, source = macros()
    boundaries = arena.boundaries
    state = boundaries.pair(
        pair,
        side,
        boundaries.literal(first, side, 0),
        boundaries.constant(boundaries.literal(second, side, 0), first, 1 - side),
    )
    fast = PrimitivePairActions(boundaries)
    expected = state
    for symbol in source if side == 0 else reversed(source):
        expected = fast.advance(pair, expected, side, symbol)
    assert arena.advance(pair, cell, state, side) == expected


def test_warm_parent_probe_precedes_children_and_parameter_application(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena, pair, _, _, cell, _ = macros()
    expected = arena.summary(pair, cell)
    before = arena.ledger.snapshot()

    def forbidden(*args: object) -> Never:
        raise AssertionError("warm parent expanded a spatial descendant")

    monkeypatch.setattr(arena, "build_children", forbidden)
    monkeypatch.setattr(arena, "_leaf", forbidden)
    assert arena.summary(pair, cell) == expected
    after = arena.ledger.snapshot()
    assert after.entries == before.entries and after.nodes == before.nodes
    assert (
        after.counters["macro_transfer_cache_hits"]
        == before.counters.get("macro_transfer_cache_hits", 0) + 1
    )
    assert (
        after.counters["macro_transfer_requests"]
        == after.counters["macro_transfer_cache_hits"]
        + after.counters["macro_transfer_evaluations"]
    )


def test_parent_publication_is_atomic_and_eviction_preserves_canonical_effects() -> (
    None
):
    arena, pair, _, _, cell, _ = macros()
    summary = arena.summary(pair, cell)
    record = arena.resolve(summary)
    arena.ledger.evict_query_memos()
    assert not arena._bindings
    arena.ledger.max_cache_entries = arena.ledger.entries
    assert_rejected_atomically(
        arena.ledger,
        lambda: arena._publish(PairMacroKey(pair, cell), record),
        BlockContextBudgetExceeded,
    )
    arena.ledger.max_cache_entries = None
    assert arena.summary(pair, cell) == summary
    assert all(row.accounting_delta == 0 for row in arena.ledger.inventory())


def test_joined_original_cells_are_supported_but_joined_images_reject_before_probe() -> (
    None
):
    arena, pair, first, _, cell, _ = macros()
    left, right = arena.cells.split(cell)
    joined = arena.cells.join(right, left)
    assert arena.summary(pair, joined) == arena.summary(pair, cell)
    image = arena.cells.image(first, left)
    bad = arena.cells.join(image, right)
    assert_rejected_atomically(
        arena.ledger,
        lambda: arena.cache_probe(pair, bad),
        ValueError,
        match="original source geometry",
    )
