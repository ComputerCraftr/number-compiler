"""Admission remains usable without the compatibility evaluator."""

import ast

import pytest

from devtools.paths import repository_root
from number_compiler.arithmetic.contracts.block_definition import (
    ComposedBlockDefinition,
    immutable_definition,
)
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.kernel_admission import (
    admit_effect,
    immutable_atom,
)
from number_compiler.arithmetic.contracts.physical_collatz_kernel import (
    PhysicalCollatzFourBlockEffect,
)
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
)
from number_compiler.hashlife.actions.lazy_compiler import (
    LazyCompiler,
    ProgramComposition,
    UnsupportedInterfaceError,
)
from number_compiler.hashlife.observation.diamond_observers import NonblankBlockEffect
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from tests.support.assertions import assert_rejected_atomically


@pytest.mark.parametrize(
    "effect",
    (
        BaseBlockEffect(10),
        DigitNormalizeBlockEffect(10),
        CollatzPhysicalBlockEffect(),
        PhysicalCollatzFourBlockEffect(),
        NonblankBlockEffect(2, 2),
    ),
)
def test_kernel_admission_preserves_complete_immutable_identity(
    effect: BaseBlockEffect
    | CollatzPhysicalBlockEffect
    | DigitNormalizeBlockEffect
    | NonblankBlockEffect
    | PhysicalCollatzFourBlockEffect,
) -> None:
    admitted = immutable_atom(effect)
    assert type(admitted) is type(effect)
    assert admitted.canonical_key == effect.canonical_key
    assert admit_effect(effect) == 1
    assert immutable_definition(effect).canonical_key == effect.canonical_key


def test_compiler_and_definition_do_not_require_a_legacy_executor() -> None:
    compiler = LazyCompiler(ResourceLedger())
    atom = compiler.atom(BaseBlockEffect(10))
    root = compiler.compose(atom, atom)
    imported = LazyCompiler(ResourceLedger()).import_effect(root)
    assert isinstance(imported, ProgramComposition) and isinstance(
        root, ProgramComposition
    )
    assert imported.canonical_key == root.canonical_key
    definition = ComposedBlockDefinition(atom, DigitNormalizeBlockEffect(10))
    assert definition.exponent == atom.exponent + DigitNormalizeBlockEffect(10).exponent


@pytest.mark.parametrize("warm", (False, True))
def test_full_dag_admission_rejects_hidden_alias_before_publication(warm: bool) -> None:
    class Alias(BaseBlockEffect):
        pass

    compiler = LazyCompiler(ResourceLedger())
    atom = BaseBlockEffect(10)
    if warm:
        compiler.compose(atom, atom)
    scope = ArenaToken("external syntax")
    hidden = ProgramComposition(
        atom, Alias(10), ActionProgramID(scope, "action-program", 0)
    )
    root = ProgramComposition(atom, hidden, ActionProgramID(scope, "action-program", 1))
    assert_rejected_atomically(
        compiler.ledger, lambda: compiler.import_effect(root), UnsupportedInterfaceError
    )


def test_admission_does_not_spend_zero_compiler_budget() -> None:
    ledger = ResourceLedger(max_nodes=0, max_cache_entries=0)
    compiler = LazyCompiler(ledger)
    before = ledger.snapshot()
    assert admit_effect(BaseBlockEffect(10)) == 1
    with pytest.raises(BlockContextBudgetExceeded):
        compiler.atom(BaseBlockEffect(10))
    assert ledger.snapshot() == before


def test_compilation_modules_have_no_legacy_executor_import() -> None:
    root = repository_root() / "src" / "number_compiler"
    for name in (
        "arithmetic/contracts/kernel_admission",
        "hashlife/actions/lazy_compiler",
        "arithmetic/contracts/block_definition",
    ):
        syntax = ast.parse((root / f"{name}.py").read_text())
        assert not any(
            isinstance(node, (ast.Import, ast.ImportFrom))
            and (
                isinstance(node, ast.ImportFrom)
                and node.module == "lazy_generic"
                or isinstance(node, ast.Import)
                and any(alias.name.endswith("lazy_generic") for alias in node.names)
            )
            for node in ast.walk(syntax)
        )
