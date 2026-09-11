"""Legacy execution boundaries validate scoped handles before cache shortcuts."""

from typing import cast

import pytest

from devtools.proofs.collatz_symbolic_action import CollatzSymbolicActionArena
from number_compiler.arithmetic.automata.action_power import ActionPowerArena
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
    TransferSummaryID,
)
from number_compiler.arithmetic.fields.dyadic_tile import source_span
from number_compiler.hashlife.actions.lazy_compiler import ProgramComposition


@pytest.mark.parametrize("warm", (False, True))
def test_collatz_affine_rejects_foreign_before_identity_and_zero_bit_observer(
    warm: bool,
) -> None:
    arena, foreign_arena = CollatzSymbolicActionArena(), CollatzSymbolicActionArena()
    local, foreign = arena.atom(1), foreign_arena.atom(1)
    if warm:
        arena.compose(local, local)
    before = arena.compositions, arena.residue_queries, arena.endpoint_projections
    source = source_span((3,), blank=0, logical_length=1)
    with pytest.raises(ValueError):
        arena.compose(foreign, local)
    with pytest.raises(ValueError):
        arena.compose(foreign, arena.identity)
    with pytest.raises(ValueError):
        arena.residue(source, foreign, 0)
    with pytest.raises(ValueError):
        arena.project(source, foreign, 1)
    with pytest.raises(ValueError):
        arena.node(foreign)
    assert (
        arena.compositions,
        arena.residue_queries,
        arena.endpoint_projections,
    ) == before
    invalid = ActionProgramID(local.owner, local.kind, arena.action_count)
    with pytest.raises(ValueError):
        arena.compose(invalid, arena.identity)


@pytest.mark.parametrize("warm", (False, True))
def test_action_power_checks_ownership_and_kind_before_zero_and_warm_shortcuts(
    warm: bool,
) -> None:
    actions, other = CollatzSymbolicActionArena(), CollatzSymbolicActionArena()
    local, foreign = actions.atom(2), other.atom(2)
    powers = ActionPowerArena(
        actions.identity, actions.compose, validate=actions.validate
    )
    if warm:
        powers.power(local, 0)
        powers.compose(local, local)
    before = powers.metrics()
    for bad in (
        foreign,
        ActionProgramID(local.owner, "wrong-program-kind", local.local_id),
        ActionProgramID(local.owner, local.kind, actions.action_count),
    ):
        with pytest.raises(ValueError):
            powers.power(bad, 0)
        with pytest.raises(ValueError):
            powers.compose(actions.identity, bad)
    with pytest.raises(TypeError):
        powers.power(
            cast(
                "ActionProgramID",
                TransferSummaryID(local.owner, local.kind, local.local_id),
            ),
            0,
        )
    with pytest.raises(TypeError):
        powers.power(cast("ActionProgramID", local.local_id), 0)
    assert powers.metrics() == before


@pytest.mark.parametrize("warm", (False, True))
def test_action_power_rejects_program_id_subclass_before_identity_or_warm_lookup(
    warm: bool,
) -> None:
    actions = CollatzSymbolicActionArena()
    local = actions.atom(2)

    class ProgramIDAlias(ActionProgramID):
        pass

    alias = ProgramIDAlias(local.owner, local.kind, local.local_id)
    powers = ActionPowerArena(
        actions.identity, actions.compose, validate=actions.validate
    )
    if warm:
        powers.power(local, 0)
        powers.compose(local, local)
    before = powers.metrics()
    with pytest.raises(TypeError, match="scoped program ID"):
        powers.power(alias, 0)
    with pytest.raises(TypeError, match="scoped program ID"):
        powers.compose(actions.identity, alias)
    assert powers.metrics() == before


def test_program_composition_rejects_action_program_subclass_sort() -> None:
    owner = ArenaToken("program-construction")

    class ProgramIDAlias(ActionProgramID):
        pass

    with pytest.raises(TypeError, match="scoped action program ID"):
        ProgramComposition(
            BaseBlockEffect(10),
            BaseBlockEffect(10),
            ProgramIDAlias(owner, "action-program", 0),
        )


def test_canonical_collatz_handles_survive_memo_eviction_and_inspection_is_immutable() -> (
    None
):
    arena = CollatzSymbolicActionArena()
    original = arena.atom(1)
    original_node = arena.node(original)
    snapshot = arena.nodes
    with pytest.raises(AttributeError):
        getattr(snapshot, "clear")()
    with pytest.raises(AttributeError):
        setattr(arena, "nodes", [])
    powers = ActionPowerArena(arena.identity, arena.compose, validate=arena.validate)
    with pytest.raises(AttributeError):
        setattr(powers, "identity", original)
    squared = powers.power(original, 2)
    powers._powers.clear()
    powers._compositions.clear()
    newer = arena.atom(7)
    assert newer.local_id > squared.local_id > original.local_id
    assert arena.node(original) is original_node
    assert powers.power(original, 2) == squared
    assert snapshot[original.local_id] is original_node


@pytest.mark.parametrize("alias", (True, 1.0))
def test_collatz_affine_integer_arguments_reject_python_numeric_aliases(
    alias: bool | float,
) -> None:
    arena = CollatzSymbolicActionArena()
    action = arena.atom(1)
    source = source_span((3,), blank=0, logical_length=1)
    before = (
        arena.compositions,
        arena.residue_queries,
        arena.endpoint_projections,
        arena.action_count,
    )
    for operation in (
        lambda: arena.atom(cast(int, alias)),
        lambda: arena.residue(source, action, cast(int, alias)),
        lambda: arena.project(source, action, cast(int, alias)),
    ):
        with pytest.raises(TypeError):
            operation()
        assert (
            arena.compositions,
            arena.residue_queries,
            arena.endpoint_projections,
            arena.action_count,
        ) == before
