"""Canonical forcing unions and source-free composition of admitted branches."""

from dataclasses import replace
from itertools import permutations

import pytest

from number_compiler.sequences.collatz.hensel_cylinders import (
    HenselAffineBlock,
    HenselCylinder,
)
from number_compiler.sequences.collatz.hensel_slabs import (
    HenselSlabArena,
    normalize_cylinders,
)


def test_siblings_subsumption_permutation_and_shared_dag() -> None:
    arena = HenselSlabArena(max_precision=16)
    atoms = (
        (7, HenselCylinder(3, 1)),
        (7, HenselCylinder(3, 5)),
        (7, HenselCylinder(9, 257)),
    )
    parent = arena.intern(((7, HenselCylinder(2, 1)),))
    for order in permutations(atoms):
        assert arena.intern(order) == parent
    assert normalize_cylinders((HenselCylinder(4, 1), HenselCylinder(4, 9))) == (
        HenselCylinder(3, 1),
    )
    second = arena.intern(((8, HenselCylinder(2, 1)),))
    assert arena.resolve(second).roots[0][1] == arena.resolve(parent).roots[0][1]
    both = arena.union(parent, second)
    assert arena.evaluate(both, 1) == frozenset((7, 8))
    assert arena.evaluate(both, 2) == frozenset()
    assert arena.restrict(both, HenselCylinder(3, 5)) == arena.intern(
        ((7, HenselCylinder(3, 5)), (8, HenselCylinder(3, 5)))
    )
    assert arena.metrics(both)["dag_nodes"] == 4
    foreign = HenselSlabArena(max_precision=16).intern(())
    with pytest.raises(ValueError, match="foreign"):
        arena.resolve(foreign)


def test_dag_and_cylinder_cover_evaluate_identically_with_overlapping_labels() -> None:
    arena = HenselSlabArena(max_precision=8)
    slab = arena.intern(
        (
            (1, HenselCylinder(4, 3)),
            (1, HenselCylinder(4, 11)),
            (2, HenselCylinder(2, 3)),
            (3, HenselCylinder(0, 0)),
        )
    )
    for value in range(256):
        observed = frozenset(
            label
            for label, root in arena.resolve(slab).roots
            if arena.decisions.evaluate(root, tuple((value >> i) & 1 for i in range(8)))
        )
        assert observed == arena.evaluate(slab, value)


def test_branch_power_1024_composes_without_primitive_or_observation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena = HenselSlabArena(max_precision=2048)
    slab = arena.intern(((1, HenselCylinder(6, 63)),))
    action = arena.primitive(1, slab)
    with monkeypatch.context() as poison:

        def forbidden(*_args: object, **_kwargs: object) -> None:
            raise AssertionError("slab squaring replayed primitive or observed a value")

        poison.setattr(arena, "primitive", forbidden)
        poison.setattr(arena, "primitive_block", forbidden)
        poison.setattr(arena, "pullback", forbidden)
        poison.setattr(arena, "evaluate", forbidden)
        poison.setattr(HenselAffineBlock, "apply_exact", forbidden)
        for _ in range(10):
            action = arena.compose(action, action)
    assert action.transport.steps == 1024
    assert arena.primitive_constructions == 1 and arena.temporal_compositions == 10
    assert action.slab == slab
    assert action.domain == HenselCylinder(1025, -1)
    assert arena.metrics(slab)["dag_nodes"] == 8
    assert arena.metrics(slab)["retained_dag_nodes"] == 8
    assert arena.metrics(slab)["slab_ids"] == 1
    source = (1 << 1025) - 1
    assert action.transport.apply_exact(source) == 2 * 3**1024 - 1


def test_composed_branch_domain_is_not_just_collapsed_transport_integrality() -> None:
    arena = HenselSlabArena(max_precision=16)
    empty = arena.intern(())
    first = arena.primitive(1, empty)
    second = arena.primitive(2, empty)
    combined = arena.compose(first, second)
    assert combined.domain is not None
    for value in range(1, 256, 2):
        n = 3 * value + 1
        v1 = (n & -n).bit_length() - 1
        mid = n >> v1
        n2 = 3 * mid + 1
        v2 = (n2 & -n2).bit_length() - 1
        assert combined.domain.contains(value) == ((v1, v2) == (1, 2))
        if combined.domain.contains(value):
            assert combined.transport.apply_exact(value) == n2 >> v2
    dead = arena.compose(replace(first, domain=None), second)
    assert dead.domain is None
