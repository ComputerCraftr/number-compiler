"""A finite invariant cycle uses source proof plus phase composition only."""

from __future__ import annotations

from typing import Never, cast

import pytest

from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
from number_compiler.sequences.collatz.diamond_cycle import (
    PhysicalCycleProjection,
    physical_cycle,
)
from tests.support.assertions import assert_rejected_atomically
from tests.support.collatz_diamond_fixtures import build_collatz_diamond_runtime
from tests.support.diamond_runtime import build, oracle


@pytest.mark.parametrize("source", [(1,), (0, 0, 1), (0, 1)])
def test_every_cycle_phase_matches_complete_physical_kernel(
    source: tuple[int, int, int] | tuple[int, int] | tuple[int],
) -> None:
    for steps in range(9):
        runtime, root = build_collatz_diamond_runtime(
            CollatzPhysicalBlockEffect(), source, 8, steps
        )
        proof = physical_cycle(runtime, root)
        assert proof is not None
        expected = oracle(CollatzPhysicalBlockEffect(), source, 8, steps)
        assert [proof.point(p) for p in range(8)] == expected
        for maximum in range(9):
            assert proof.active_width(maximum) == max(
                (p + 1 for p in range(maximum) if expected[p] != 2), default=0
            )


def test_huge_cycle_power_never_runs_a_transition_or_future_projection(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    steps = 10**80 + 1
    runtime, root = build_collatz_diamond_runtime(
        CollatzPhysicalBlockEffect(), (1,), 8, steps
    )

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError(
            "cycle certification must inspect only source and immutable action DAG"
        )

    monkeypatch.setattr(runtime, "execute", forbidden)
    monkeypatch.setattr(runtime, "point", forbidden)
    monkeypatch.setattr(CollatzPhysicalBlockEffect, "advance", forbidden)
    monkeypatch.setattr(CollatzPhysicalBlockEffect, "emit", forbidden)
    proof = physical_cycle(runtime, root)
    assert proof is not None
    assert proof.phase == steps % 3
    assert proof.point(0) == 0
    assert (
        runtime.ledger.counters["physical_cycle_action_visits"]
        <= 4 * steps.bit_length()
    )
    assert runtime.ledger.counters.get("primitive_output_evaluations", 0) == 0


@pytest.mark.parametrize("source", [(1, 0), (0,), (1, 1), (0, 1, 0)])
def test_noncanonical_or_noncycle_source_is_not_reinterpreted_as_cycle(
    source: tuple[int, int, int] | tuple[int, int] | tuple[int],
) -> None:
    runtime, root = build_collatz_diamond_runtime(
        CollatzPhysicalBlockEffect(), source, 8, 100
    )
    assert physical_cycle(runtime, root) is None


def test_clipped_field_and_other_operator_cannot_claim_physical_cycle() -> None:
    runtime, root = build_collatz_diamond_runtime(
        CollatzPhysicalBlockEffect(), (1,), 2, 1
    )
    assert physical_cycle(runtime, root) is None
    runtime, root = build(BaseBlockEffect(2), (1,), 8, 2)
    assert physical_cycle(runtime, root) is None
    foreign, other = build_collatz_diamond_runtime(
        CollatzPhysicalBlockEffect(), (1,), 8, 2
    )
    assert_rejected_atomically(
        runtime.ledger, lambda: physical_cycle(runtime, other), ValueError
    )
    assert physical_cycle(foreign, other) is not None


@pytest.mark.parametrize("source", [(1,), (0, 0, 1), (0, 1)])
def test_application_cycle_queries_skip_generic_execution_and_source_reproof(
    source: tuple[int, int, int] | tuple[int, int] | tuple[int],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.hashlife.observation.diamond_query import DiamondApplication

    runtime, root = build_collatz_diamond_runtime(
        CollatzPhysicalBlockEffect(), source, 8, 10**80 + 1
    )

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError(
            "certified cycle queries must not execute or re-prove the source"
        )

    monkeypatch.setattr(runtime, "execute", forbidden)
    monkeypatch.setattr(runtime, "point", forbidden)
    application = DiamondApplication(runtime, root)
    # The cycle is constructed once at application creation; later observations
    # only consume that issued projection.
    proof = cast(PhysicalCycleProjection, application._cycles[0])
    before = runtime.ledger.snapshot()
    for _ in range(2):
        assert [application.point(p) for p in range(8)] == [
            proof.point(p) for p in range(8)
        ]
        assert application.active_width() == proof.active_width()
        assert application.active_width(0) == 0
    assert runtime.ledger.entries == before.entries
    assert runtime.ledger.counters["physical_cycle_point_queries"] == 16
    assert runtime.ledger.counters["physical_cycle_width_queries"] == 4
    assert (
        runtime.ledger.counters["physical_cycle_action_visits"]
        == before.counters["physical_cycle_action_visits"]
    )
    assert all(row.accounting_delta == 0 for row in runtime.ledger.inventory())


def test_application_cycle_validates_coordinates_and_scopes_before_warm_hit() -> None:
    from number_compiler.hashlife.observation.diamond_query import DiamondApplication

    runtime, root = build_collatz_diamond_runtime(
        CollatzPhysicalBlockEffect(), (1,), 8, 100
    )
    application = DiamondApplication(runtime, root)
    application.point(0)
    before = runtime.ledger.snapshot()
    for position in (-1, True, 8):
        with pytest.raises((ValueError, IndexError)):
            application.point(position)
    for maximum in (-1, True, 9):
        with pytest.raises(ValueError):
            application.active_width(maximum)
    assert runtime.ledger.snapshot() == before
    application.root = runtime.actions.identity
    with pytest.raises(ValueError, match="another source or action"):
        application.point(0)
    with pytest.raises(ValueError, match="another source or action"):
        application.active_width(0)
    assert runtime.ledger.snapshot() == before


def test_cycle_projection_is_not_retained_when_its_reservation_fails(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )
    from number_compiler.hashlife.observation.diamond_query import DiamondApplication

    runtime, root = build_collatz_diamond_runtime(
        CollatzPhysicalBlockEffect(), (1,), 8, 100
    )
    reserve = runtime.ledger.reserve

    def reject_cycle(owner: int, *, entries: int = 0, nodes: int = 0) -> None:
        if any(
            row.owner == owner and row.role == "finite_cycle_certificate"
            for row in runtime.ledger.inventory()
        ):
            raise BlockContextBudgetExceeded("cycle reservation exhausted")
        return reserve(owner, entries=entries, nodes=nodes)

    monkeypatch.setattr(runtime.ledger, "reserve", reject_cycle)
    application = DiamondApplication.__new__(DiamondApplication)
    with pytest.raises(BlockContextBudgetExceeded):
        type(application).__init__(application, runtime, root)
    assert not application._cycles
    assert all(row.accounting_delta == 0 for row in runtime.ledger.inventory())


def test_finite_cycle_certificate_requires_actual_source_and_complete_phase_proof() -> (
    None
):
    from dataclasses import replace

    from number_compiler.arithmetic.contracts.scoped_handles import (
        ArenaToken,
        ExactSource,
    )
    from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
    from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )
    from number_compiler.hashlife.execution.diamond_payload import (
        DiamondPayloadRegistry,
    )
    from number_compiler.hashlife.observation.diamond_query import DiamondApplication
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.resources.metric_collection import collect_ledger_metrics
    from number_compiler.resources.stores import LedgerList
    from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect
    from number_compiler.sequences.collatz.diamond_cycle import (
        PhysicalCycleProjection,
    )
    from number_compiler.sequences.collatz.tile_family_hooks import collatz_tile_hooks

    ledger = ResourceLedger()
    compiler = LazyCompiler(ledger, family_hooks=collatz_tile_hooks())
    effect = compiler.atom(CollatzPhysicalBlockEffect())
    source = ExactSource((1,), 2, blank=2, extent=8, alphabet_size=2)
    geometry = SourceGeometry(ledger, source)
    geometry.span(source.digits, 2, 8)
    engine = DiamondRuntime(compiler, geometry)
    action = engine.actions.power(engine.actions.intern(effect), 256)
    application = DiamondApplication(engine, action)
    record = application._cycles[0]
    assert type(record) is PhysicalCycleProjection
    before = ledger.snapshot()
    registry = DiamondPayloadRegistry(ledger)
    assert registry.valid(record)
    assert not registry.valid(replace(record))
    assert not registry.valid(replace(record, source=ArenaToken("foreign")))
    assert not registry.valid(replace(record, phase=(record.phase + 1) % 3))
    report = collect_ledger_metrics(ledger)
    assert ledger.snapshot() == before
    assert report.representation_boundary_complete == 1
    assert report.finite_cycle_certificate_nodes == 1
    owner = ledger.register("forged finite cycle", "finite_cycle_certificate")
    records: LedgerList[PhysicalCycleProjection]
    records = ledger.make_list(owner)
    ledger.reserve(owner, entries=1, nodes=1)
    records.append(replace(record, phase=(record.phase + 1) % 3))
    assert collect_ledger_metrics(ledger).representation_boundary_complete == 0
