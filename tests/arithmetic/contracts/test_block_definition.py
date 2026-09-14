"""Immutable composition syntax never owns or shares runtime residual caches."""

import gc
import weakref
from dataclasses import fields

import pytest

from devtools.proofs.block_composed import ComposedBlockEffect
from number_compiler.arithmetic.contracts import block_definition
from number_compiler.arithmetic.contracts.block_definition import (
    BlockDefinition,
    ComposedBlockDefinition,
)
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudget,
    BoundarySide,
)
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.hashlife.actions.lazy_compiler import (
    LazyCompiler,
    ProgramComposition,
)
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.ledger import ResourceLedger


def test_shared_definition_has_independent_runtime_contexts_and_readonly_semantics() -> (
    None
):
    atom = BaseBlockEffect(2)
    definition = ComposedBlockDefinition(atom, atom)
    first = ComposedBlockEffect.from_definition(definition, budget=BlockContextBudget())
    second = ComposedBlockEffect.from_definition(
        definition, budget=BlockContextBudget()
    )
    assert first.definition is second.definition is definition
    before = tuple(getattr(definition, field.name) for field in fields(definition))
    second_stats = second.runtime_stats()
    first.advance(BoundarySide.LEFT, first.initial(BoundarySide.LEFT), 0)
    assert first.runtime_stats()["left_transition_entries"] == 1
    assert second.runtime_stats() == second_stats
    assert (
        tuple(getattr(definition, field.name) for field in fields(definition)) == before
    )
    assert first._functional_intern[0] is not second._functional_intern[0]
    for name, replacement in (
        ("base", 3),
        ("blank", 7),
        ("exponent", 99),
        ("node_id", 1),
        ("first", atom),
        ("definition", definition),
    ):
        with pytest.raises(AttributeError):
            setattr(first, name, replacement)
    with pytest.raises(AttributeError):
        definition.__setattr__("first", first)


def test_nested_definitions_strip_runtime_children_and_recreate_their_owners() -> None:
    atom = BaseBlockEffect(2)
    child = ComposedBlockEffect(atom, atom, budget=BlockContextBudget())
    definition = ComposedBlockDefinition(child, child)
    assert definition.first is definition.second is child.definition
    first = ComposedBlockEffect.from_definition(definition, budget=BlockContextBudget())
    second = ComposedBlockEffect.from_definition(
        definition, budget=BlockContextBudget()
    )
    assert first.first is first.second
    assert first.first is not second.first
    assert first.first is not child
    assert isinstance(first.first, ComposedBlockEffect)
    assert isinstance(second.first, ComposedBlockEffect)
    assert first.first.definition is second.first.definition is child.definition
    pending: list[BlockDefinition] = [definition]
    while pending:
        node = pending.pop()
        assert not isinstance(node, ComposedBlockEffect)
        if isinstance(node, ComposedBlockDefinition):
            assert all(
                not isinstance(getattr(node, field.name), (dict, list, set))
                for field in fields(node)
            )
            pending.extend((node.first, node.second))


def test_definition_digest_collision_still_compares_complete_child_semantics(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class ConstantDigest:
        def hexdigest(self) -> str:
            return "intentional-collision"

    monkeypatch.setattr(block_definition, "sha256", lambda _data: ConstantDigest())
    atom = BaseBlockEffect(2)
    one = ComposedBlockDefinition(atom, atom)
    alias = ComposedBlockDefinition(BaseBlockEffect(2), BaseBlockEffect(2))
    different = ComposedBlockDefinition(atom, DigitNormalizeBlockEffect(2))
    assert one.canonical_key == alias.canonical_key
    assert one.canonical_key != different.canonical_key


def test_point_compiler_import_does_not_retain_the_legacy_runtime_context() -> None:
    atom = BaseBlockEffect(2)
    runtime = ComposedBlockEffect(atom, atom, budget=BlockContextBudget())
    reference = weakref.ref(runtime)
    compiler = LazyCompiler(ResourceLedger())
    program = compiler.import_effect(runtime)
    assert isinstance(program, ProgramComposition)
    assert not isinstance(program.first, ComposedBlockEffect)
    assert not isinstance(program.second, ComposedBlockEffect)
    del runtime
    gc.collect()
    assert reference() is None
