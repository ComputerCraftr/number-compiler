import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.hashlife.actions.lazy_compiler import (
    LazyCompiler,
    ProgramComposition,
)
from number_compiler.resources.ledger import ResourceLedger


@pytest.mark.parametrize("warm", (False, True))
def test_compiler_rejects_foreign_program_before_warm_or_zero_power(warm: bool) -> None:
    left = LazyCompiler(ResourceLedger())
    right = LazyCompiler(ResourceLedger())
    atom = left.atom(BaseBlockEffect(10))
    other_atom = right.atom(BaseBlockEffect(10))
    local = left.compose(atom, atom)
    foreign = right.compose(other_atom, other_atom)
    assert isinstance(local, ProgramComposition) and isinstance(
        foreign, ProgramComposition
    )
    assert local.canonical_key == foreign.canonical_key
    if warm:
        left.compose(local, atom)
    before = left.ledger.snapshot()
    with pytest.raises(ValueError):
        left.compose(foreign, atom)
    with pytest.raises(ValueError):
        left.power(foreign, 0)
    with pytest.raises(ValueError):
        left.atom(foreign)
    assert left.ledger.snapshot() == before
    # Cross-arena syntax sharing is an explicit import, never implicit lookup.
    imported = left.import_effect(foreign)
    assert imported is local


def test_compiler_rejects_out_of_range_and_forged_local_program_ids() -> None:
    compiler = LazyCompiler(ResourceLedger())
    atom = compiler.atom(BaseBlockEffect(10))
    local = compiler.compose(atom, atom)
    assert isinstance(local, ProgramComposition)
    for index in (local.handle.local_id, len(compiler.nodes)):
        forged = ProgramComposition(
            atom, atom, ActionProgramID(compiler.token, "action-program", index)
        )
        with pytest.raises(ValueError):
            compiler.compose(forged, atom)
        with pytest.raises(ValueError):
            compiler.power(forged, 0)


def test_compilers_sharing_a_ledger_keep_distinct_owned_stores() -> None:
    ledger = ResourceLedger()
    left = LazyCompiler(ledger)
    right = LazyCompiler(ledger)

    assert left.owner != right.owner
    assert left.index_owner != right.index_owner
    assert left._nodes is not right._nodes
    assert left._ids is not right._ids
    left.atom(BaseBlockEffect(10))
    assert len(left.nodes) == 1
    assert right.nodes == ()
