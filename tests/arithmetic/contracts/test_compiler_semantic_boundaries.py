"""Warm semantic keys cannot bypass validation of an executable definition."""

from __future__ import annotations

import pytest

from devtools.proofs.block_composed import ComposedBlockEffect
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudget
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
)
from number_compiler.hashlife.actions.lazy_compiler import (
    LazyCompiler,
    ProgramComposition,
    UnsupportedInterfaceError,
)
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import ResourceLedger


class _Impostor(BaseBlockEffect):
    def emit(self, left: object, symbol: object, right: object) -> int:
        return 0


@pytest.mark.parametrize("warm", (False, True))
def test_compose_rejects_same_key_impostor_before_lookup_or_retention(
    warm: bool,
) -> None:
    compiler = LazyCompiler(ResourceLedger())
    atom, impostor = BaseBlockEffect(2), _Impostor(2)
    assert atom.canonical_key == impostor.canonical_key
    if warm:
        compiler.compose(atom, atom)
    before = compiler.ledger.snapshot()
    for first, second in ((atom, impostor), (impostor, atom), (impostor, impostor)):
        with pytest.raises(UnsupportedInterfaceError):
            compiler.compose(first, second)
        assert compiler.ledger.snapshot() == before


def test_compose_requires_explicit_import_of_a_mutable_compatibility_runtime() -> None:
    compiler = LazyCompiler(ResourceLedger())
    atom = BaseBlockEffect(2)
    runtime = ComposedBlockEffect(atom, atom, budget=BlockContextBudget())
    before = compiler.ledger.snapshot()
    with pytest.raises(UnsupportedInterfaceError):
        compiler.compose(runtime, atom)
    assert compiler.ledger.snapshot() == before
    imported = compiler.import_effect(runtime)
    result = compiler.compose(imported, atom)
    assert isinstance(result, ProgramComposition)
    assert result.first is imported
    assert not isinstance(result.second, ComposedBlockEffect)


def test_generic_import_checks_an_impostor_even_after_its_sibling_populates_the_key() -> (
    None
):
    atom, impostor = BaseBlockEffect(2), _Impostor(2)
    syntax = ProgramComposition(
        atom, impostor, ActionProgramID(ArenaToken(), "action-program", 0)
    )
    with pytest.raises(UnsupportedInterfaceError):
        LazyCompiler(ResourceLedger()).import_effect(syntax)


def test_generic_import_admits_all_descendants_before_a_warm_composed_key() -> None:
    atom, impostor, terminal = (
        BaseBlockEffect(10),
        _Impostor(10),
        DigitNormalizeBlockEffect(10),
    )
    owner = ArenaToken()
    good = ProgramComposition(
        atom, terminal, ActionProgramID(owner, "action-program", 0)
    )
    bad = ProgramComposition(
        impostor, terminal, ActionProgramID(owner, "action-program", 1)
    )
    assert good.canonical_key == bad.canonical_key
    outer = ProgramComposition(good, bad, ActionProgramID(owner, "action-program", 2))
    ledger = ResourceLedger()
    compiler = LazyCompiler(ledger)
    before = ledger.snapshot()
    with pytest.raises(UnsupportedInterfaceError):
        compiler.import_effect(outer)
    assert ledger.snapshot() == before
