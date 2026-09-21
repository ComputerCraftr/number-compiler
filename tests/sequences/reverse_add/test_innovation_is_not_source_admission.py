"""Arithmetic expressions and projections cannot authorize source images."""

import pytest

from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.fields.symbolic_innovation import (
    RadialMultiplier,
    SymbolicInnovationArena,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.cylinder_innovation import (
    primitive_successor_clause,
)
from number_compiler.sequences.reverse_add.source_images import (
    ReverseSourceImageWorkspace,
)


def test_formal_innovation_and_its_residue_are_not_source_image_payloads() -> None:
    ledger = ResourceLedger()
    workspace = ReverseSourceImageWorkspace(ledger, 196, 0)
    arena = SymbolicInnovationArena(ledger)
    key = SemanticIdentity("", ("test", "formal-primitive"))
    expression = arena.power(arena.action(RadialMultiplier(1, 0), arena.atom(key)), 4)
    residue = arena.project_cyclotomic(
        expression, order=8, bits=5, atoms={key: (1, 0, 0, 0)}
    )
    for payload in (expression, residue):
        with pytest.raises(TypeError, match="payload sort"):
            workspace.adapter.validate_payload(payload)
    arena.close()
    workspace.dispose()
    assert ledger.entries == ledger.nodes == 0


def test_primitive_coboundary_is_not_a_complete_temporal_image() -> None:
    """Authenticated primitive arithmetic does not prove complete admission."""
    from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
    from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts

    ledger = ResourceLedger()
    workspace = ReverseSourceImageWorkspace(ledger, 196, 0)
    arena = SymbolicInnovationArena(ledger)
    ports = SourceCarryPorts(ExactSource((6, 9, 1), 10, orbit="reverse-add"), ledger)
    clause = primitive_successor_clause(arena, ports)
    with pytest.raises(TypeError, match="payload sort"):
        workspace.adapter.validate_payload(clause)
    clause.close()
    arena.close()
    ports.dispose()
    workspace.dispose()
    assert ledger.entries == ledger.nodes == 0
