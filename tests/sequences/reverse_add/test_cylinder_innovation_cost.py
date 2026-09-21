"""Primitive expression construction is independent of its represented width.

This does not bound source admission or construct a second temporal clause.
Those costs must remain distinct from the fixed-size coboundary expression.
"""

from typing import Never

import pytest

from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.fields.symbolic_innovation import (
    SymbolicInnovationArena,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.cylinder_innovation import (
    PrimitiveSuccessorClause,
    primitive_successor_clause,
)
from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts


@pytest.mark.parametrize("width", (1, 16, 128, 1024))
@pytest.mark.parametrize("digit", (1, 9))
def test_whole_coboundary_has_bounded_nodes_without_point_consumption(
    width: int, digit: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    ledger = ResourceLedger()
    source = ExactSource((digit,) * width, 10, orbit="reverse-add")
    ports = SourceCarryPorts(source, ledger)
    arena = SymbolicInnovationArena(ledger)
    initial_nodes = arena.node_count

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("construction consumed a future coefficient")

    for name in (
        "beta_coefficient",
        "output_coefficient",
        "successor_pair_coefficient",
    ):
        monkeypatch.setattr(PrimitiveSuccessorClause, name, forbidden)
    clause = primitive_successor_clause(arena, ports)
    assert clause.growth == int(digit == 9)
    assert clause.output_extent == width + int(digit == 9)
    # Q, translated Q, scaled Q, E, reflected E and beta are a fixed
    # expression. This is a bound, not a claimed canonical node identity.
    assert 0 < arena.node_count - initial_nodes <= 8
    assert ledger.counters["reverse_source_ports_validation_coordinates"] == 2 * width
    assert ledger.counters["reverse_source_ports_source_reads"] > 0
    assert not ledger.counters.get("reverse_source_ports_second_pair_queries", 0)
    clause.close()
    arena.close()
    ports.dispose()
    assert ledger.entries == ledger.nodes == 0


def test_warm_clause_admission_needs_only_incremental_binding_capacity() -> None:
    ledger = ResourceLedger()
    ports = SourceCarryPorts(ExactSource((6, 9, 1), 10, orbit="reverse-add"), ledger)
    arena = SymbolicInnovationArena(ledger)
    first = primitive_successor_clause(arena, ports)
    first.close()
    nodes_before = arena.node_count
    ledger.tighten_limits(ledger.nodes + 1, ledger.entries + 2)
    second = primitive_successor_clause(arena, ports)
    assert arena.node_count == nodes_before
    assert second.growth == 0
    second.close()
    arena.close()
    ports.dispose()
    assert ledger.entries == ledger.nodes == 0
