"""Compressed physical carry projection over a supplied modular residue view."""

from __future__ import annotations

from dataclasses import replace

import pytest

from number_compiler.arithmetic.automata.residue_carry_slp import (
    ResidueCarrySLPProjector,
)
from number_compiler.arithmetic.automata.slp import SLPArena
from number_compiler.arithmetic.carry.carry_monoid import (
    apply_carry_fn,
    centered_carry_fn,
)
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger


def _expand(arena: SLPArena, root: int, *, limit: int = 1000) -> tuple[int, ...]:
    if arena.nodes[root].length > limit:
        raise ValueError("test expansion limit exceeded")
    result: list[int] = []
    pending: list[tuple[int, int]] = [(root, 1)]
    while pending:
        node_id, count = pending.pop()
        node = arena.nodes[node_id]
        if node.kind == "EMPTY":
            continue
        if node.kind == "TERM":
            result.extend((node.symbol,) * count)
        elif node.kind == "CONCAT":
            for _ in range(count):
                pending.append((node.right, 1))
                pending.append((node.left, 1))
        elif node.kind == "REPEAT":
            pending.append((node.child, count * node.count))
        else:
            raise AssertionError(node.kind)
    return tuple(result)


def _reference(
    word: tuple[int, ...], incoming: int
) -> tuple[tuple[int, ...], tuple[int, ...], int]:
    carry = incoming
    outgoing: list[int] = []
    jumps: list[int] = []
    for residue in word:
        following = apply_carry_fn(centered_carry_fn(residue - 9), carry)
        outgoing.append(following)
        jumps.append(following - carry)
        carry = following
    return tuple(outgoing), tuple(jumps), carry


@pytest.mark.parametrize("incoming", [0, 1])
def test_projection_matches_physical_two_state_carry(incoming: int) -> None:
    word = (8, 9, 10, 9, 8, 10)
    source = SLPArena()
    root = source.word(word)
    ledger = ResourceLedger()
    projector = ResidueCarrySLPProjector(ledger)

    result = projector.project(source, source.nodes[root], incoming=incoming)
    expected_outgoing, expected_jumps, expected_final = _reference(word, incoming)

    assert _expand(result.arena, result.outgoing_root) == expected_outgoing
    assert _expand(result.arena, result.jump_root) == expected_jumps
    assert _expand(result.arena, result.closed_jump_root) == (
        *expected_jumps,
        -expected_final,
    )
    assert result.final_carry == expected_final
    assert result.input_length == len(word)
    result.close()
    projector.close()
    assert ledger.entries == ledger.nodes == 0


def test_huge_repeat_uses_binary_composition_without_materialization(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = SLPArena()
    count = 10**30
    root = source.repeat(source.terminal(9), count)
    projector = ResidueCarrySLPProjector(ResourceLedger())

    def forbidden(*_args: object, **_kwargs: object) -> tuple[int, ...]:
        raise AssertionError("compressed carry projection materialized an SLP")

    monkeypatch.setattr(SLPArena, "materialize", forbidden)
    result = projector.project(source, source.nodes[root], incoming=1)

    assert result.arena.nodes[result.outgoing_root].length == count
    assert result.arena.nodes[result.jump_root].length == count
    assert result.final_carry == 1
    assert result.derived_nodes < 8 * count.bit_length()
    assert (
        projector.ledger.counters["residue_carry_slp_repeat_bits"] == count.bit_length()
    )
    output_row = next(
        row
        for row in projector.ledger.inventory()
        if row.name.startswith("residue-carry-slp-output-") and not row.disposed
    )
    assert output_row.nodes > output_row.entries


def test_shared_input_nodes_are_summarized_once() -> None:
    source = SLPArena()
    shared = source.word((8, 10, 9))
    root = source.concat(shared, shared)
    reachable = source.reachable(root)
    ledger = ResourceLedger()
    projector = ResidueCarrySLPProjector(ledger)

    result = projector.project(source, source.nodes[root])

    assert ledger.counters["residue_carry_slp_unique_nodes"] == len(reachable)
    assert result.input_length == 6


def test_invalid_residue_foreign_root_and_mutated_definition_are_rejected() -> None:
    projector = ResidueCarrySLPProjector(ResourceLedger())
    invalid = SLPArena()
    with pytest.raises(ValueError, match="definition"):
        invalid_root = invalid.terminal(19)
        projector.project(invalid, invalid.nodes[invalid_root])

    source = SLPArena()
    root = source.word((8, 9))
    with pytest.raises(TypeError, match="arena node"):
        projector.project(source, root)  # type: ignore[arg-type]

    foreign = SLPArena()
    foreign_root = foreign.word((8, 9))
    assert foreign_root == root
    with pytest.raises(ValueError, match="foreign or out of range"):
        projector.project(source, foreign.nodes[foreign_root])

    source.nodes[root] = replace(source.nodes[root], length=99)
    with pytest.raises(ValueError, match="definition"):
        projector.project(source, source.nodes[root])


def test_output_node_allocation_is_preflighted_and_failure_cleans_workspace() -> None:
    source = SLPArena()
    root = source.terminal(9)
    ledger = ResourceLedger(max_nodes=0)
    projector = ResidueCarrySLPProjector(ledger)

    with pytest.raises(BlockContextBudgetExceeded):
        projector.project(source, source.nodes[root])

    assert ledger.entries == ledger.nodes == 0
    assert any(
        row.name.startswith("residue-carry-slp-output-") and row.disposed
        for row in ledger.inventory()
    )


def test_repeat_length_validation_precharges_wide_integer_arithmetic() -> None:
    source = SLPArena()
    root = source.repeat(source.terminal(9), 1 << 500)
    ledger = ResourceLedger(max_nodes=2)
    projector = ResidueCarrySLPProjector(ledger)

    with pytest.raises(BlockContextBudgetExceeded):
        projector.project(source, source.nodes[root])

    assert ledger.entries == ledger.nodes == 0


def test_empty_word_has_empty_outputs_and_preserves_incoming() -> None:
    source = SLPArena()
    projector = ResidueCarrySLPProjector(ResourceLedger())
    result = projector.project(source, source.nodes[source.empty()], incoming=1)

    assert result.outgoing_root == result.arena.empty()
    assert result.jump_root == result.arena.empty()
    assert _expand(result.arena, result.closed_jump_root) == (-1,)
    assert result.final_carry == 1
    assert result.input_length == 0
