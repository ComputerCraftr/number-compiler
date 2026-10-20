"""Independent decimal oracles for every NC15 candidate border cycle."""

from __future__ import annotations

import random
from dataclasses import asdict
from typing import cast

import pytest

from number_compiler.sequences.double_reverse.boundary_cycles import (
    CANDIDATE_COMPONENTS,
    Edge,
    candidate_component,
    edge_from_digits,
)
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.source_adapter import DoubleReverseSource
from number_compiler.sequences.double_reverse.temporal_border_bank import (
    OBSERVERS,
    observer_output,
    power_temporal_border,
)
from number_compiler.sequences.double_reverse.temporal_carry_safety import (
    LiftedBorder,
    component_safety_proof,
    conditional_carry_trace,
    forced_carry_prefix,
    lift_from_digits,
    lifted_step,
    source_carry_safety,
)


def _literal(x: int) -> int:
    return 2 * int(str(x)[::-1])


@pytest.mark.validation
def test_lifted_step_independent_literal_and_shrinks() -> None:
    rng = random.Random(994231)
    checked = 0
    contracted = 0
    for width in (6, 7, 8, 9, 14, 25):
        for _ in range(700):
            source = str(rng.randint(1, 9)) + "".join(
                str(rng.randrange(10)) for _ in range(width - 1)
            )
            target = str(_literal(int(source)))
            lift = lift_from_digits(source)
            actual_carry = int(int(source[-4]) >= 5)
            actual = lifted_step(lift, actual_carry)
            if len(target) < len(source):
                assert actual.shrinking_frontier
                contracted += 1
                continue
            assert actual.target == lift_from_digits(target)
            assert actual.growth == len(target) - len(source)
            assert actual.current_inward_carry == int(int(source[-3]) >= 5)
            assert actual.next_inward_carry == int(int(target[-3]) >= 5)
            checked += 1
    assert checked >= 3500
    assert contracted >= 50


@pytest.mark.validation
def test_exact_complete_lifted_component_closure() -> None:
    expected = (
        (900, True, None, (900,)),
        (600, False, 5, (600, 550, 470, 270, 170, 120, 0)),
        (600, False, 5, (600, 500, 460, 360, 160, 60, 0)),
        (400, False, 4, (400, 300, 240, 80, 30, 0)),
    )
    for component, (n, closed, maximum, survival) in enumerate(expected):
        proof = component_safety_proof(component)
        assert (
            proof.lifted_states,
            proof.universally_closed,
            proof.maximum_internal_transitions,
            proof.surviving_state_counts,
        ) == (n, closed, maximum, survival)
        for edge in CANDIDATE_COMPONENTS[component]:
            for third_high in range(10):
                for third_low in range(10):
                    lift = LiftedBorder(
                        (edge[0], edge[1], third_high),
                        (third_low, edge[2], edge[3]),
                    )
                    for bit in (0, 1):
                        candidate = lifted_step(lift, bit).target
                        if closed:
                            assert candidate is not None
                            assert candidate_component(candidate.edge) == component
                        elif (
                            candidate is not None
                            and candidate_component(candidate.edge) == component
                        ):
                            assert candidate != lift or maximum != 0


@pytest.mark.validation
def test_alternative_cycles_are_finite_after_three_cell_lifting() -> None:
    for component in (1, 2, 3):
        bound = component_safety_proof(component).maximum_internal_transitions
        assert bound is not None
        states = {
            LiftedBorder((a, b, c), (x, y, z))
            for (a, b, y, z) in CANDIDATE_COMPONENTS[component]
            for c in range(10)
            for x in range(10)
        }
        for _ in range(bound + 1):
            states = {
                candidate
                for border in states
                for bit in (0, 1)
                if (candidate := lifted_step(border, bit).target) is not None
                and candidate_component(candidate.edge) == component
            }
        assert not states


@pytest.mark.validation
def test_source_forced_carries_are_derived_across_two_generations() -> None:
    rng = random.Random(20261015)
    seeds: tuple[int, ...] = (
        173488,
        174388,
        1768742,
        4957342,
        4875188,
        1700042,
        1700542,
    )
    seeds += tuple(rng.randrange(100000, 999999) for _ in range(200))
    for seed in seeds:
        source = str(seed)
        lift = lift_from_digits(source)
        report = source_carry_safety(lift)
        assert report.current_forced_carry == int(int(source[-3]) >= 5)
        if report.shrinking_frontier:
            assert len(str(_literal(seed))) < len(source)
            continue
        next_value = _literal(seed)
        next_digits = str(next_value)
        assert edge_from_digits(next_digits) in report.possible_next_edges
        assert report.next_forced_carry == int(int(next_digits[-3]) >= 5)
        assert forced_carry_prefix(lift) == (
            report.current_forced_carry,
            report.next_forced_carry,
        )
        successor = _literal(next_value)
        # Both two-cell successor edges are unambiguous from the input
        # three-cell source even though the fourth-low carry is unknown.
        alternatives = [lifted_step(lift, b).target for b in (0, 1)]
        for alternative in alternatives:
            assert alternative is not None
            edges2 = {
                next_border.target.edge
                for b in (0, 1)
                if (next_border := lifted_step(alternative, b)).target is not None
            }
            if len(str(successor)) >= len(str(next_value)):
                assert edge_from_digits(str(successor)) in edges2


@pytest.mark.validation
def test_source_guarded_moore_envelopes_sharpen_unconstrained_ports() -> None:
    seeds = (173488, 174388, 1768742, 4957342, 4875188)
    for seed in seeds:
        lift = lift_from_digits(str(seed))
        for observer in OBSERVERS:
            if observer == "joint":
                continue
            for steps in range(6):
                free = power_temporal_border(lift.edge, steps, observer)
                real = seed
                total = 0
                for _tick in range(steps):
                    edge = edge_from_digits(str(real))
                    next_value = _literal(real)
                    # Output has no unknown digits once actual successor is known.
                    ingress = int(int(str(real)[-3]) >= 5)
                    value = observer_output(edge, ingress, observer)[0]
                    total += value
                    real = next_value
                assert free.minimum_emission_sum <= total <= free.maximum_emission_sum


def test_powered_safety_lift_is_only_derived_from_an_owner_issued_prefix() -> None:
    with DoubleReverseTerm(196, 64) as term:
        prefix, envelopes = term.temporal_border_bank()
        assert prefix == 16
        assert len(envelopes) == len(OBSERVERS) - 1
        assert all(envelope.steps == 48 for envelope in envelopes)
        engine = term.temporal_engine
        entry = engine.source_prefix()
        assert entry is not None
        forged = type(entry)(
            entry.source,
            entry.target,
            entry.physical_steps,
            entry.certified_phase,
        )
        with pytest.raises(ValueError, match="not owner-issued"):
            engine.validate_source_prefix(forged)
        assert term.published_image is None


def test_cli_source_carry_safety_and_no_endpoint(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbid(_term: DoubleReverseTerm) -> None:
        raise AssertionError("safety observer constructed the endpoint")

    monkeypatch.setattr(DoubleReverseTerm, "prepare_endpoint", forbid)
    with DoubleReverseTerm(196, 64) as term:
        prefix, source, proofs = term.temporal_carry_safety()
        assert prefix == 16
        assert source.component == 0
        assert source.high3 == (1, 7, 3)
        assert source.current_forced_carry == 0
        assert source.next_forced_carry == 1
        assert [p.maximum_internal_transitions for p in proofs] == [None, 5, 5, 4]
        assert asdict(source)["universally_closed_component"] is True
        assert term.published_image is None
    with DoubleReverseTerm(1700542, 4) as term:
        prefix, source, _ = term.temporal_carry_safety()
        assert prefix == 0
        assert source.component == 0
    with DoubleReverseTerm(16488, 4) as term:
        prefix, source, _ = term.temporal_carry_safety()
        assert prefix == 0
        assert source.component == 1
        assert source.source_maximum_internal_transitions is not None
        assert source.source_maximum_internal_transitions <= 5


def test_carry_safety_rejects_forged_same_arena_source_without_rendering() -> None:
    with DoubleReverseTerm(173488, 0) as term:
        source = cast(DoubleReverseSource, object.__getattribute__(term, "_source"))
        original_root = source.root
        foreign_root = term.source_arena.word((9, 9, 9, 9, 9, 9))
        object.__setattr__(source, "root", foreign_root)
        try:
            with pytest.raises(ValueError, match="source binding"):
                term.temporal_carry_safety()
            with pytest.raises(ValueError, match="source binding"):
                term.prepare_endpoint()
            assert term.published_image is None
        finally:
            object.__setattr__(source, "root", original_root)

        original_source = cast(
            DoubleReverseSource, object.__getattribute__(term, "_source")
        )
        object.__setattr__(
            term,
            "_source",
            type(original_source)(
                original_source.issuer, original_source.seed, foreign_root
            ),
        )
        try:
            with pytest.raises(ValueError, match="source binding"):
                term.temporal_carry_safety()
            assert term.published_image is None
        finally:
            object.__setattr__(term, "_source", original_source)


def test_carry_safety_reuses_the_term_owned_refinement(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.resources.metric_collection import collect_ledger_metrics
    from number_compiler.sequences.double_reverse import temporal_carry_safety_audit

    with DoubleReverseTerm(173488, 0) as term:
        owner_before = term.resource_ledger.inventory_owner(term.carry_safety_owner)
        assert owner_before.role == "double_reverse_temporal_memo"
        assert owner_before.entries == owner_before.nodes == 0
        assert collect_ledger_metrics(term.resource_ledger).resource_audit_complete == 1

        first = term.temporal_carry_safety()
        assert len(term.carry_safety_entries()) == 1
        owner_after = term.resource_ledger.inventory_owner(term.carry_safety_owner)
        assert owner_after.entries == 1
        assert owner_after.nodes > owner_after.entries
        report = collect_ledger_metrics(term.resource_ledger)
        assert report.resource_audit_complete == 1
        assert report.forbidden_future_payloads == 0
        assert report.resource_accounting_mismatch == 0
        assert any(
            item.owner == term.carry_safety_owner
            and item.role == "double_reverse_temporal_memo"
            and item.observed_entries == 1
            for item in report.resource_inventory
        )

        def forbidden_component_rebuild(_component: int) -> object:
            raise AssertionError("cached carry-safety refinement was rebuilt")

        monkeypatch.setattr(
            temporal_carry_safety_audit,
            "component_layers",
            forbidden_component_rebuild,
        )
        assert term.temporal_carry_safety() == first


def test_carry_safety_cache_releases_its_reservation_on_dispose() -> None:
    term = DoubleReverseTerm(173488, 0)
    ledger = term.resource_ledger
    term.temporal_carry_safety()
    owner = term.carry_safety_owner
    assert ledger.inventory_owner(owner).entries == 1
    term.dispose()
    snapshot = ledger.snapshot()
    assert snapshot.entries == snapshot.nodes == 0
    disposed = ledger.inventory_owner(owner)
    assert disposed.disposed
    assert disposed.entries == disposed.nodes == 0


def test_carry_safety_cache_rejects_same_key_mutated_result_fields() -> None:
    with DoubleReverseTerm(173488, 0) as term:
        term.temporal_carry_safety()
        _key, issued = term.carry_safety_entries()[0]
        source = issued.result[1]
        mutations = (
            ("possible_next_edges", ()),
            ("shrinking_frontier", not source.shrinking_frontier),
            ("source_maximum_internal_transitions", 999),
            ("component_maximum_internal_transitions", 999),
            (
                "universally_closed_component",
                not source.universally_closed_component,
            ),
            (
                "exact_width_change",
                999
                if source.exact_width_change is None
                else source.exact_width_change + 1,
            ),
            ("unconditional_entry_or_shrink_bound", 999),
        )
        for field, altered in mutations:
            original = getattr(source, field)
            object.__setattr__(source, field, altered)
            try:
                with pytest.raises(ValueError, match="altered after issue"):
                    term.temporal_carry_safety()
            finally:
                object.__setattr__(source, field, original)

        proof = issued.result[2][1]
        original_counts = proof.surviving_state_counts
        object.__setattr__(proof, "surviving_state_counts", (*original_counts, 999))
        try:
            with pytest.raises(ValueError, match="altered after issue"):
                term.temporal_carry_safety()
        finally:
            object.__setattr__(proof, "surviving_state_counts", original_counts)


def test_a_shrinking_frontier_cannot_be_promoted_to_a_repeat() -> None:
    for source in ("123400", "170000", "120040"):
        lift = lift_from_digits(source)
        safety = source_carry_safety(lift)
        if len(str(_literal(int(source)))) < len(source):
            assert safety.shrinking_frontier
            with pytest.raises(ValueError, match="shrinking"):
                forced_carry_prefix(lift)


@pytest.mark.validation
def test_backward_carry_safety_prunes_a_certified_edge_trace() -> None:
    # The double reversal's first two carries are source-derived. For an
    # independently authenticated longer edge trace, backward compatibility
    # further removes impossible fourth-digit choices without guessing them.
    seed = 173488
    edge_word: list[Edge] = []
    sources: list[int] = []
    for _ in range(8):
        sources.append(seed)
        edge_word.append(edge_from_digits(str(seed)))
        seed = _literal(seed)
    trace = conditional_carry_trace(lift_from_digits(str(sources[0])), tuple(edge_word))
    assert len(trace.allowed_inward_carries) == 7
    assert trace.allowed_inward_carries[:4] == ((0,), (1,), (0,), (0,))
    assert trace.allowed_fourth_carries[1] == (1,)
    for index in range(7):
        source = str(sources[index])
        assert int(int(source[-3]) >= 5) in trace.allowed_inward_carries[index]
        assert int(int(source[-4]) >= 5) in trace.allowed_fourth_carries[index]

    for seed, second_prefix in ((1700042, (4, 8)), (1700542, (4, 9))):
        successor = _literal(seed)
        trace = conditional_carry_trace(
            lift_from_digits(str(seed)),
            (edge_from_digits(str(seed)), edge_from_digits(str(successor))),
        )
        assert edge_from_digits(str(successor))[:2] == second_prefix
        assert trace.allowed_inward_carries == ((int(int(str(seed)[-3]) >= 5),),)

    with pytest.raises(ValueError, match="contradicts"):
        conditional_carry_trace(
            lift_from_digits("1700542"),
            (edge_from_digits("1700542"), edge_from_digits("4800142")),
        )


def test_alternative_abstract_cycle_repeat_is_rejected_before_powering() -> None:
    from number_compiler.sequences.double_reverse.boundary_cycles import (
        CANDIDATE_COMPONENTS,
    )

    for comp, seed in ((1, 16488), (2, 1697542), (3, 16922)):
        lift = lift_from_digits(str(seed))
        edge = lift.edge
        assert edge in CANDIDATE_COMPONENTS[comp]
        with pytest.raises(ValueError, match="proved carry-safety bound"):
            conditional_carry_trace(lift, (edge,) * 8)
