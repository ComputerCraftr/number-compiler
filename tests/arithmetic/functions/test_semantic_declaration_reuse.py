"""Canonical declaration lookup precedes rewrite, without caching observations."""

from __future__ import annotations

from dataclasses import replace
from itertools import product
from typing import TYPE_CHECKING, Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.functions.finite_function_types import (
    AtomSort,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_function_transactions import (
    _Transaction,
)
from number_compiler.hashlife.interfaces.semantic_bits import BitFunctionArena
from number_compiler.hashlife.interfaces.semantic_structures import (
    StructureArena,
    _Builder,
)
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from number_compiler.hashlife.interfaces.semantic_structures import (
        StructureID,
    )


def setup() -> tuple[ResourceLedger, StructureArena, FinitePort, StructureID]:
    ledger = ResourceLedger()
    structures = StructureArena(BitFunctionArena(ledger))
    x = FinitePort(PortVariable(0, 0, "outer", 0), 3)
    arg = FinitePort(PortVariable(2, 0, "argument", 0), 3)
    xx = structures.bits.variable((x, arg), x)
    yy = structures.bits.variable((x, arg), arg)
    body = structures.atom(structures.bits.add(xx, yy, AtomSort("sum", 5)))
    value = structures.curry(body, (arg,))
    return ledger, structures, x, value


def test_declaration_preserves_outer_dependencies_padding_and_bound_capture() -> None:
    _, structures, x, value = setup()
    source = structures.resolve(value)
    # A newly declared outer name collides with an old internal binder alias.
    extra = source.bound[0]
    inputs = tuple(sorted((x, extra), key=lambda port: port.variable))
    declared = structures.declare(value, inputs)
    node = structures.resolve(declared)
    assert node.signature == FunctionSignature(inputs, source.signature.output)
    assert node.bound != source.bound
    assert node.body is not None
    atom = structures.resolve(node.body).atom
    assert atom is not None
    for xx, yy, zz in product(range(4), repeat=3):
        actual = structures.bits.evaluate(
            atom, {x.variable: xx, extra.variable: yy, node.bound[0].variable: zz}
        )
        assert actual == (xx + zz if max(xx, yy, zz) < 3 else None)


def test_warm_semantic_declaration_avoids_construction_and_validates_handles(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, structures, x, value, extra, inputs = _declaration_fixture()
    result = structures.declare(value, inputs)

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("known complete declaration replayed construction")

    monkeypatch.setattr(_Builder, "rewrite", forbidden)
    monkeypatch.setattr(_Transaction, "decision", forbidden)
    retained = ledger.snapshot()
    assert structures.declare(value, inputs) == result
    assert (ledger.entries, ledger.nodes) == (retained.entries, retained.nodes)
    before = ledger.snapshot()
    foreign = StructureArena(BitFunctionArena(ResourceLedger())).token
    for field, invalid in (
        ("owner", foreign),
        ("local_id", True),
        ("local_id", 1.0),
        ("local_id", -1),
    ):
        bad = replace(value)
        object.__setattr__(bad, field, invalid)
        with pytest.raises((ValueError, TypeError)):
            structures.declare(bad, inputs)
        assert ledger.snapshot() == before
    with pytest.raises(ValueError, match="preserve every"):
        structures.declare(value, (extra,))
    assert ledger.snapshot() == before


def test_declaration_budget_rejection_is_atomic_and_eviction_preserves_ids(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, structures, x, value, extra, inputs = _declaration_fixture()
    before = ledger.snapshot()
    ledger.max_cache_entries = ledger.entries

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("exhausted declaration budget entered construction")

    with monkeypatch.context() as patch:
        patch.setattr(_Builder, "rewrite", forbidden)
        with pytest.raises(BlockContextBudgetExceeded):
            structures.declare(value, inputs)
    assert (ledger.entries, ledger.nodes, ledger.inventory()) == (
        before.entries,
        before.nodes,
        before.inventory,
    )
    ledger.max_cache_entries = None
    ledger.max_nodes = ledger.nodes
    with pytest.raises(BlockContextBudgetExceeded):
        structures.declare(value, inputs)
    assert (ledger.entries, ledger.nodes, ledger.inventory()) == (
        before.entries,
        before.nodes,
        before.inventory,
    )
    ledger.max_nodes = None
    result = structures.declare(value, inputs)
    structures._declarations.clear()
    assert structures.resolve(result).signature.inputs == inputs
    assert structures.declare(value, inputs) == result


def _declaration_fixture() -> tuple[
    ResourceLedger,
    StructureArena,
    FinitePort,
    StructureID,
    FinitePort,
    tuple[FinitePort, FinitePort],
]:
    ledger, structures, x, value = setup()
    extra = FinitePort(PortVariable(1, 0, "extra", 0), 3)
    inputs = (x, extra)
    return ledger, structures, x, value, extra, inputs
