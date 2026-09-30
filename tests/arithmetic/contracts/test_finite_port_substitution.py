from __future__ import annotations

from tests.support.finite_port_fixtures import three_input_ports

from itertools import product
from typing import TYPE_CHECKING, Never

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.scoped_handles import TransferSummaryID
from number_compiler.arithmetic.functions.finite_port_action import (
    FinitePortActionArena,
    PortVariable,
)

if TYPE_CHECKING:
    import number_compiler.arithmetic.contracts.scoped_handles


def _functions(
    arena: FinitePortActionArena,
    x: TransferSummaryID,
    y: number_compiler.arithmetic.contracts.scoped_handles.TransferSummaryID,
) -> list[TransferSummaryID]:
    return [
        arena.choose(
            x,
            arena.choose(
                y, arena.constant(bool(bits & 8)), arena.constant(bool(bits & 4))
            ),
            arena.choose(
                y, arena.constant(bool(bits & 2)), arena.constant(bool(bits & 1))
            ),
        )
        for bits in range(16)
    ]


def test_every_two_variable_function_and_simultaneous_replacement() -> None:
    arena = FinitePortActionArena()
    px, py = PortVariable(0, 0, "input", 0), PortVariable(0, 0, "input", 1)
    x, y = arena.variable(px), arena.variable(py)
    functions = _functions(arena, x, y)
    for f, g, h in product(range(16), repeat=3):
        result = arena.substitute(functions[f], {px: functions[g], py: functions[h]})
        for index, (a, b) in enumerate(product((False, True), repeat=2)):
            argument = 2 * bool(g & (1 << index)) + bool(h & (1 << index))
            expected = bool(f & (1 << argument))
            assert arena.apply(result, {px: a, py: b}) == expected


def test_effective_mapping_canonical_before_warm_lookup(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena, (px, py, pz), (x, y, z) = three_input_ports()
    function = arena.choose(x, y, arena.constant(False))
    result = arena.substitute(function, {px: z})
    before = arena.ledger.snapshot()

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("warm substitution descended into Shannon construction")

    monkeypatch.setattr(arena, "_intern", forbidden)
    monkeypatch.setattr(arena, "choose", forbidden)
    assert arena.substitute(function, {pz: x, py: y, px: z}) == result
    after = arena.ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    assert (
        after.counters["finite_port_substitution_cache_hits"]
        == before.counters.get("finite_port_substitution_cache_hits", 0) + 1
    )
    assert (
        after.counters["finite_port_substitution_cofactor_tasks"]
        == before.counters["finite_port_substitution_cofactor_tasks"]
    )
    assert (
        after.counters["finite_port_substitution_support_visits"]
        == before.counters["finite_port_substitution_support_visits"]
    )
    foreign = FinitePortActionArena()
    frozen = arena.ledger.snapshot()
    with pytest.raises(ValueError):
        arena.substitute(function, {px: z, pz: foreign.constant(False)})
    with pytest.raises(ValueError):
        arena.substitute(
            function,
            {
                px: TransferSummaryID(
                    arena.owner, "finite-port-function", arena.node_count
                )
            },
        )
    assert arena.ledger.snapshot() == frozen


def test_atomic_final_graph_publication_and_exhausted_fast_rejection() -> None:
    arena, (px, py, pz), (x, y, z) = three_input_ports()
    function = arena.choose(x, y, arena.constant(False))
    old = arena.ledger.snapshot()
    arena.ledger.max_cache_entries = (
        old.entries + 2
    )  # root+support fit; new result node+key do not
    with pytest.raises(BlockContextBudgetExceeded):
        arena.substitute(function, {px: z})
    failed = arena.ledger.snapshot()
    assert (
        failed.entries,
        failed.nodes,
        failed.peak_entries,
        failed.peak_nodes,
        failed.inventory,
    ) == (old.entries, old.nodes, old.peak_entries, old.peak_nodes, old.inventory)
    assert not arena._substitution.memo
    assert not arena._substitution.supports
    arena.ledger.max_cache_entries = old.entries
    tasks = failed.counters["finite_port_substitution_cofactor_tasks"]
    with pytest.raises(BlockContextBudgetExceeded):
        arena.substitute(function, {px: z})
    assert arena.ledger.counters["finite_port_substitution_cofactor_tasks"] == tasks
    arena.ledger.max_cache_entries = None
    output = arena.substitute(function, {px: z})
    node_count = arena.node_count
    arena.ledger.evict_query_memos()
    assert not arena._substitution.memo
    assert not arena._substitution.supports
    assert arena.substitute(function, {px: z}) == output
    assert arena.node_count == node_count
