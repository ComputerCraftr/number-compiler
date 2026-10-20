from random import Random
from typing import Literal, cast

import pytest

from number_compiler.sequences.collatz.power import (
    CollatzAffineBranch,
    CollatzPowerArena,
    collatz_apply_word,
    collatz_branch_word,
    compose_collatz_branches,
)


def test_collatz_partial_affine_atoms_and_impossible_odd_odd() -> None:
    even = CollatzAffineBranch.atom("E")
    odd = CollatzAffineBranch.atom("O")
    assert even.apply(10) == 5
    assert odd.apply(7) == 22
    assert compose_collatz_branches(odd, odd).empty
    oe = compose_collatz_branches(odd, even)
    assert oe.apply(7) == 11
    assert oe.domain_bits == 1 and oe.residue == 1


def test_collatz_partial_affine_composition_is_associative() -> None:
    atoms = [CollatzAffineBranch.atom("E"), CollatzAffineBranch.atom("O")]
    for a in atoms:
        for b in atoms:
            for c in atoms:
                lhs = compose_collatz_branches(compose_collatz_branches(a, b), c)
                rhs = compose_collatz_branches(a, compose_collatz_branches(b, c))
                assert lhs.semantic_key() == rhs.semantic_key()


def test_collatz_powered_branch_dag_matches_reference_orbits() -> None:
    rng = Random(0xC011A72)
    for _ in range(64):
        seed = rng.randrange(1, 1 << 18)
        steps = rng.randrange(0, 96)
        branches = collatz_branch_word(seed, steps)
        arena = CollatzPowerArena()
        root = arena.from_branches(branches)
        assert root.effect.accepts(seed)
        assert root.effect.apply(seed) == collatz_apply_word(seed, branches)
        assert root.effect.steps == steps


def test_collatz_power_charges_domain_information_not_only_dag_nodes() -> None:
    arena = CollatzPowerArena()
    root = arena.power(arena.atom("E"), 1 << 12)
    metrics = arena.metrics(root)
    assert root.effect.apply(1 << 5000) == 1 << (5000 - (1 << 12))
    assert metrics["arena_nodes"] <= 16
    assert metrics["domain_bits"] == 1 << 12
    # E^N is a genuine compact special case: the residue itself is zero, so N
    # is represented by a length field rather than an N-bit random certificate.
    assert metrics["operator_description_bits"] < 2000


def test_collatz_concrete_random_path_residue_can_remain_linear_information() -> None:
    branches = collatz_branch_word(27, 100)
    arena = CollatzPowerArena()
    root = arena.from_branches(branches)
    assert root.effect.apply(27) == collatz_apply_word(27, branches)
    assert root.effect.domain_bits > 50
    # The implementation reports the domain information instead of claiming
    # that balanced DAG depth alone makes the full-state Collatz map compact.
    assert (
        arena.metrics(root)["operator_description_bits"]
        >= root.effect.domain_bits.bit_length()
    )


def test_accelerated_valuation_event_is_one_domain_free_transport_atom() -> None:
    from number_compiler.sequences.collatz.pair import accelerated_odd_collatz
    from number_compiler.sequences.collatz.power import CollatzEventArena

    arena = CollatzEventArena()
    for source in range(1, 4096, 2):
        step = accelerated_odd_collatz(source)
        node = arena.event(step.valuation)
        assert arena.apply_exact(node, source) == step.target
        assert node.effect.events == 1
        assert node.effect.physical_steps == step.valuation + 1
        assert node.effect.shift == step.valuation
        # Event evidence is owned by the producer; the transport does not
        # materialize the k+1-bit source-independent residue certificate.
        assert (
            node.effect.description_bits < 8 * max(1, step.valuation.bit_length()) + 32
        )


def test_event_arena_consumes_valuations_without_expanding_forced_even_runs() -> None:
    from number_compiler.sequences.collatz.pair import accelerated_odd_collatz
    from number_compiler.sequences.collatz.power import CollatzEventArena

    source = 27
    value = source
    valuations: list[int] = []
    for _ in range(32):
        step = accelerated_odd_collatz(value)
        valuations.append(step.valuation)
        value = step.target

    event_arena = CollatzEventArena()
    event_root = event_arena.from_valuations(valuations)
    assert event_arena.apply_exact(event_root, source) == value
    assert event_root.effect.events == len(valuations)
    assert event_root.effect.shift == sum(valuations)
    assert event_root.effect.physical_steps == sum(k + 1 for k in valuations)

    expanded: tuple[Literal["O", "E"], ...] = tuple(
        cast(Literal["O", "E"], branch)
        for k in valuations
        for branch in ("O", *("E" for _ in range(k)))
    )
    branch_arena = CollatzPowerArena()
    branch_root = branch_arena.from_branches(expanded)
    assert branch_root.effect.accepts(source)
    assert branch_root.effect.apply(source) == value
    assert len(expanded) == event_root.effect.physical_steps
    assert len(expanded) > len(valuations)
    assert event_arena.composition_operations < branch_arena.composition_operations


def test_million_division_event_descriptor_does_not_materialize_million_bit_domain() -> (
    None
):
    from number_compiler.sequences.collatz.power import CollatzEventArena

    k = 1_000_000
    arena = CollatzEventArena()
    node = arena.event(k)
    metrics = arena.metrics(node)
    assert node.effect.shift == k
    assert metrics["events"] == 1
    assert metrics["physical_steps"] == k + 1
    assert metrics["operator_description_bits"] < 128
    assert metrics["cocycle_materializations"] == 0


def test_event_cocycle_lowering_is_explicit_and_memoized() -> None:
    from number_compiler.sequences.collatz.power import CollatzEventArena

    arena = CollatzEventArena()
    root = arena.from_valuations((2, 3, 1, 4))
    assert arena.metrics(root)["cocycle_materializations"] == 0
    first = arena.materialize_cocycle(root)
    materialized = arena.cocycle_materializations
    second = arena.materialize_cocycle(root)
    assert first is second
    assert arena.cocycle_materializations == materialized
    assert first.shift == 10


def test_event_lowering_rejects_foreign_colliding_ids_before_cache_access() -> None:
    import pytest

    from number_compiler.sequences.collatz.power import CollatzEventArena

    for warm in (False, True):
        owner, foreign = CollatzEventArena(), CollatzEventArena()
        admitted, alien = owner.event(1), foreign.event(3)
        assert admitted.node_id == alien.node_id
        if warm:
            assert owner.materialize_cocycle(admitted).shift == 1
        before = owner.cocycle_materializations
        with pytest.raises(ValueError, match="another arena"):
            owner.materialize_cocycle(alien)
        assert owner.cocycle_materializations == before
        assert owner.materialize_cocycle(admitted).shift == 1


def test_event_consumers_reject_foreign_and_copied_handles() -> None:
    from dataclasses import replace

    import pytest

    from number_compiler.sequences.collatz.power import CollatzEventArena

    owner, foreign = CollatzEventArena(), CollatzEventArena()
    admitted = owner.event(3)
    for alien in (foreign.event(3), replace(admitted)):
        with pytest.raises(ValueError, match="another arena"):
            owner.apply_exact(alien, 13)
        with pytest.raises(ValueError, match="another arena"):
            owner.metrics(alien)
        with pytest.raises(ValueError, match="another arena"):
            owner.materialize_cocycle(alien)
    assert owner.apply_exact(admitted, 13) == 5


def test_warm_event_lowering_does_not_recompose_cached_subtrees(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.fields.morphism_core import DyadicAffineCocycle
    from number_compiler.sequences.collatz.power import CollatzEventArena

    owner = CollatzEventArena()
    root = owner.from_valuations((1, 3, 2, 4))
    expected = owner.materialize_cocycle(root)

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("warm lowering recomposed an admitted cocycle")

    monkeypatch.setattr(DyadicAffineCocycle, "then", forbidden)
    assert owner.materialize_cocycle(root) is expected


@pytest.mark.parametrize("alias", (True, 1.0))
def test_event_identity_rejects_numeric_id_alias_before_warm_lookup(
    alias: object,
) -> None:
    from number_compiler.sequences.collatz.power import CollatzEventArena

    owner = CollatzEventArena()
    node = owner.identity
    owner.materialize_cocycle(node)
    object.__setattr__(node, "node_id", alias)
    with pytest.raises(ValueError, match="another arena"):
        owner.materialize_cocycle(node)


def test_exact_event_application_rejects_corrupted_descendant_bindings() -> None:
    from number_compiler.sequences.collatz.power import (
        CollatzEventArena,
        CollatzEventTransport,
    )

    owner = CollatzEventArena()
    first, second = owner.event(1), owner.event(3)
    root = owner.concat(first, second)
    # Swapping valuations preserves the root's totals but changes its action.
    # Frozen assignment is forbidden; explicitly challenge canonical admission.
    for node, valuation in ((first, 3), (second, 1)):
        object.__setattr__(node, "valuation", valuation)
        object.__setattr__(
            node, "effect", CollatzEventTransport.valuation_atom(valuation)
        )
    owner.validate_node(root)
    with pytest.raises(ValueError, match="canonical arena binding"):
        owner.apply_exact(root, 29)
