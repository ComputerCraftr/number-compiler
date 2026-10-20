"""Prime owner and image authority remain independently audited."""

from __future__ import annotations

from dataclasses import replace

import pytest

from number_compiler.hashlife.execution.source_bound_images import (
    SourceBoundSchedulerCore,
)
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageDemand,
)
from number_compiler.resources.ledger import LedgerSnapshot, ResourceLedger
from number_compiler.resources.payload_audit import audit_registered_payloads
from tests.support.source_bound_images import source_audit


def _prime_invalid(
    ledger: ResourceLedger, core: SourceBoundSchedulerCore
) -> frozenset[tuple[int, int]]:
    return ledger.audit_payload_contracts().invalid | source_audit(ledger, core).invalid


def _assert_audit_only_change(before: LedgerSnapshot, after: LedgerSnapshot) -> None:
    counter = "payload_audit_contract_member_visits"
    assert after.counters.get(counter, 0) > before.counters.get(counter, 0)
    expected = dict(before.counters)
    expected[counter] = after.counters[counter]
    assert after == replace(before, counters=expected)


def test_prime_source_payload_audit_is_read_only_at_the_work_limit() -> None:
    from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG
    from number_compiler.sequences.prime.successor_action import (
        PrimeSuccessorActionArena,
    )
    from number_compiler.sequences.prime.successor_action_contracts import (
        PrimeSuccessorSource,
    )
    from number_compiler.sequences.prime.successor_image_adapter import (
        PrimeSuccessorImageAdapter,
    )

    dag = CoprimeRankDAG((2, 3), max_states=1024, max_work=100_000)
    arena = PrimeSuccessorActionArena(dag, 5)
    adapter = PrimeSuccessorImageAdapter(arena)
    core = SourceBoundSchedulerCore(dag.ledger)
    core.register(adapter)
    try:
        action = arena.prefix(11)
        image = core.apply_demanded(
            adapter,
            PrimeSuccessorSource(arena.descriptor_id, 0),
            action,
            SourceImageDemand("rank-before", (11,)),
        )
        core.projection(adapter, image, SourceImageDemand("rank-before", (11,)))
        dag.max_work = dag.work
        before, work = dag.ledger.snapshot(), dag.work
        report = audit_registered_payloads(dag.ledger)
        after = dag.ledger.snapshot()
        assert (
            report.forbidden_future_payloads,
            report.unbounded_future_integers,
            report.unknown_payloads,
        ) == (0, 0, 0)
        _assert_audit_only_change(before, after)
        assert dag.work == work
    finally:
        core.dispose()
        arena.close()
        dag.close()


@pytest.mark.parametrize("damage", ("node-width", "node-child", "container"))
def test_prime_source_payload_audit_rejects_forged_arena_ownership(
    damage: str,
) -> None:
    from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG
    from number_compiler.sequences.prime.successor_action import (
        PrimeSuccessorActionArena,
    )
    from number_compiler.sequences.prime.successor_action_contracts import (
        PrimeSuccessorSource,
    )
    from number_compiler.sequences.prime.successor_image_adapter import (
        PrimeSuccessorImageAdapter,
    )

    dag = CoprimeRankDAG((2, 3), max_states=1024, max_work=100_000)
    arena = PrimeSuccessorActionArena(dag, 5)
    adapter = PrimeSuccessorImageAdapter(arena)
    core = SourceBoundSchedulerCore(dag.ledger)
    core.register(adapter)
    try:
        core.apply(
            adapter,
            PrimeSuccessorSource(arena.descriptor_id, 0),
            arena.prefix(11),
        )
        if damage == "node-width":
            object.__setattr__(dict(arena.audit_snapshot().nodes)[2], "width", 99)
        elif damage == "node-child":
            composite = next(
                node
                for node in dict(arena.audit_snapshot().nodes).values()
                if node.before is not None
            )
            object.__setattr__(composite, "before", arena.descriptor_id)
        else:
            object.__setattr__(arena, "_audit_nodes", {})
        assert _prime_invalid(dag.ledger, core)
    finally:
        core.dispose()
        arena.close()
        dag.close()


def test_prime_source_payload_audit_rejects_replaced_adapter_arena() -> None:
    from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG
    from number_compiler.sequences.prime.successor_action import (
        PrimeSuccessorActionArena,
    )
    from number_compiler.sequences.prime.successor_action_contracts import (
        PrimeSuccessorSource,
    )
    from number_compiler.sequences.prime.successor_image_adapter import (
        PrimeSuccessorImageAdapter,
    )

    dag = CoprimeRankDAG((2, 3), max_states=1024, max_work=100_000)
    foreign_dag = CoprimeRankDAG((2, 3), max_states=1024, max_work=100_000)
    arena = PrimeSuccessorActionArena(dag, 5)
    foreign = PrimeSuccessorActionArena(foreign_dag, 5)
    adapter = PrimeSuccessorImageAdapter(arena)
    core = SourceBoundSchedulerCore(dag.ledger)
    core.register(adapter)
    try:
        core.apply(
            adapter,
            PrimeSuccessorSource(arena.descriptor_id, 0),
            arena.prefix(7),
        )
        adapter.arena = foreign
        audit = source_audit(dag.ledger, core)
        assert audit.invalid
    finally:
        adapter.arena = arena
        core.dispose()
        arena.close()
        foreign.close()
        dag.close()
        foreign_dag.close()


@pytest.mark.parametrize("damage", ("fresh-prime", "forbidden-residues", "port-count"))
def test_prime_descriptor_authority_and_port_extent_are_immutable(damage: str) -> None:
    from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG
    from number_compiler.sequences.prime.successor_action import (
        PrimeSuccessorActionArena,
    )
    from number_compiler.sequences.prime.successor_action_contracts import (
        PrimeSuccessorSource,
    )
    from number_compiler.sequences.prime.successor_image_adapter import (
        PrimeSuccessorImageAdapter,
    )

    dag = CoprimeRankDAG((2, 3, 5, 7), max_states=1024, max_work=100_000)
    arena = PrimeSuccessorActionArena(dag, 11)
    adapter = PrimeSuccessorImageAdapter(arena)
    core = SourceBoundSchedulerCore(dag.ledger)
    core.register(adapter)
    try:
        action = arena.prefix(1)
        core.apply(adapter, PrimeSuccessorSource(arena.descriptor_id, 0), action)
        if damage == "fresh-prime":
            # Both fresh-prime phases on the old period are 1; phase checks alone
            # cannot distinguish the admitted successor 11 from the later 19.
            assert 210 % 11 == 210 % 19 == 1
            object.__setattr__(arena.descriptor, "fresh_prime", 19)
        elif damage == "forbidden-residues":
            object.__setattr__(arena.descriptor, "forbidden_residues", (2,))
        else:
            effect = arena.port_effect(arena.base, 0)
            too_many = arena.descriptor.parent_period + 1
            object.__setattr__(effect, "parent_survivors", too_many)
            object.__setattr__(
                effect, "surviving_values", too_many - effect.deleted_survivors
            )
        before, work = dag.ledger.snapshot(), dag.work
        assert _prime_invalid(dag.ledger, core)
        _assert_audit_only_change(before, dag.ledger.snapshot())
        assert dag.work == work
        if damage != "port-count":
            with pytest.raises(
                ValueError, match="descriptor lost its source authority"
            ):
                arena.node(action)
    finally:
        core.dispose()
        arena.close()
        dag.close()
