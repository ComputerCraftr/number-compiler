"""Exact oracle regression; these objects are not production carriers."""

import pytest

from devtools.proofs.carry_action_quotient import CarryActionQuotientArena
from devtools.proofs.reverse_action import ReverseAddMacroActionArena
from devtools.proofs.reverse_spacetime import (
    ReverseAddCausalSpacetimeEngine,
    ReverseAddPairField,
)
from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID


@pytest.mark.parametrize("warm", (False, True))
def test_reverse_macro_rejects_foreign_before_compose_apply_and_port_cache(
    warm: bool,
) -> None:
    engine = ReverseAddCausalSpacetimeEngine(base=10)
    source = ReverseAddPairField.from_pair((2,))
    primitive = engine.forcing_image(source).action
    arena, foreign_arena = (
        ReverseAddMacroActionArena(10),
        ReverseAddMacroActionArena(10),
    )
    local, foreign = arena.primitive(primitive), foreign_arena.primitive(primitive)
    assert local.local_id == foreign.local_id
    if warm:
        arena.compose(local, local)
    before = arena.compose_requests, arena.applications
    with pytest.raises(ValueError):
        arena.compose(foreign, local)
    with pytest.raises(ValueError):
        arena.apply(foreign, source.span)
    with pytest.raises(ValueError):
        arena.carry_projection(
            foreign, source.span, CarryActionQuotientArena(), base=10
        )
    assert (arena.compose_requests, arena.applications) == before
    invalid = ActionProgramID(local.owner, local.kind, arena.action_count)
    with pytest.raises(ValueError):
        arena.apply(invalid, source.span)
