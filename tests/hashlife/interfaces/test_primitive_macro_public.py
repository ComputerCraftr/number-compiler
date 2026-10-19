"""Public fixed finite cells execute complete quotients before descendants."""

from typing import Never

import pytest

from number_compiler.arithmetic.automata.primitive_semantics import (
    PrimitiveSemanticsAdapter,
    division_witness,
)
from number_compiler.hashlife.execution.continuations.diamond_runtime import (
    DiamondRuntime,
)
from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena
from number_compiler.hashlife.interfaces.diamond_quotient import (
    DiamondQuotientArena,
)
from number_compiler.hashlife.interfaces.semantic_primitive_macro import (
    PrimitiveMacroArena,
)
from number_compiler.hashlife.interfaces.semantic_structures import (
    DiamondQuotientID,
)
from tests.support.diamond_query import build, oracle


@pytest.mark.parametrize("radix", (3, 6, 12))
def test_public_primitive_point_and_full_width_use_complete_macro(
    radix: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    effect = division_witness(radix)
    source = (1, 0, 1, 1)
    expected = oracle(effect, source, 8, 1)
    app = build(effect, source, 8, 1)

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("finite point or width entered legacy observation")

    monkeypatch.setattr(DiamondRuntime, "point", forbidden)
    monkeypatch.setattr(type(app), "_active", forbidden)
    assert tuple(app.point(index) for index in range(8)) == tuple(expected)
    assert app.active_width() == 4
    assert app.runtime.primitive_macros is not None
    assert app.runtime.semantic_quotients is not None
    assert all(
        type(binding.quotient) is DiamondQuotientID
        for binding in app.runtime.primitive_macros.bindings.values()
    )
    assert app.ledger.counters["primitive_macro_early_hits"] > 0


def test_public_warm_parent_answers_new_coordinates_with_all_construction_poisoned(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    effect = division_witness(3)
    source = (1, 0, 1, 1)
    expected = oracle(effect, source, 8, 1)
    app = build(effect, source, 8, 1)
    assert app.point(0) == expected[0]
    before = app.ledger.snapshot()

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("known parent replayed construction or child admission")

    for cls, name in (
        (PrimitiveMacroArena, "_leaf"),
        (PrimitiveMacroArena, "_parent"),
        (PrimitiveSemanticsAdapter, "compile"),
        (DiamondQuotientArena, "intern"),
        (DiamondKernelArena, "intern"),
        (DiamondRuntime, "point"),
        (type(app.runtime.cells), "split"),
    ):
        monkeypatch.setattr(cls, name, forbidden)
    for index in (7, 3, 5, 1, 2, 4, 6):
        assert app.point(index) == expected[index]
    assert app.active_width() == 4
    after = app.ledger.snapshot()
    assert (after.entries, after.nodes, after.inventory) == (
        before.entries,
        before.nodes,
        before.inventory,
    )
