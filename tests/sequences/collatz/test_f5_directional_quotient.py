"""Finite consumer refinement, independently of temporal/source closure."""

from collections import Counter
from math import comb
from typing import Never

import pytest

from devtools.proofs import collatz_harmonic_ports
from number_compiler.arithmetic.carry.collatz_binary_forcing import radix64_phi5
from number_compiler.arithmetic.carry.collatz_f5_quotient import (
    F5_DIRECTIONAL_COUNTS,
    F5_JOIN_TABLES,
    RADIX64_F5_CLASSES,
    radix64_f5_class,
    radix64_f5_directional_views,
    radix64_pair_f5_views,
)
from number_compiler.arithmetic.functions.finite_function_types import (
    AtomSort,
    FinitePort,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.semantic_bits import BitFunctionArena
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.output_morphism import (
    DIGIT,
    CollatzOutputMorphism,
)


def test_canonical_phase_matches_independent_binary_output_identity() -> None:
    assert collatz_harmonic_ports.radix64_phi5 is radix64_phi5
    for digit in range(64):
        raw = 3 * digit + 1
        expected = (
            sum(
                comb(i, 2)
                * (-1) ** (i - 2)
                * (((raw >> i) & 1) - ((digit >> i) & 1) - ((digit >> (i - 1)) & 1))
                for i in range(2, 8)
            )
            % 5
        )
        assert radix64_phi5(digit) == expected
    assert Counter(radix64_phi5(d) for d in range(64)) == {
        0: 28,
        1: 16,
        2: 4,
        3: 7,
        4: 9,
    }
    assert len(RADIX64_F5_CLASSES) == 15


def test_hensel_neighbor_needs_more_than_the_fifteen_leaf_classes() -> None:
    left, right = 67, 75

    def key(n: int) -> tuple[int, int]:
        return radix64_f5_class(n % 64), radix64_f5_class(n // 64)

    assert key(left) == key(right)
    # Both are positive odd, two-cell sources with exactly the same gap, e=1.
    assert (3 * left + 1) % 4 == (3 * right + 1) % 4 == 2
    targets = ((3 * left + 1) // 2, (3 * right + 1) // 2)
    assert targets == (101, 113)
    assert radix64_f5_class(targets[0] % 64) != radix64_f5_class(targets[1] % 64)
    ports = [
        radix64_f5_directional_views((3 * (n % 64) + 1) % 64, 1)[0]
        for n in (left, right)
    ]
    assert ports[0] != ports[1]


def test_directional_quotient_is_exact_and_separately_minimal() -> None:
    assert F5_DIRECTIONAL_COUNTS == ((15, 1), (12, 2), (10, 4), (8, 8), (4, 9), (2, 13))
    for shift, rows in enumerate(F5_JOIN_TABLES):
        assert len(set(rows)) == len(rows)
        columns = tuple(zip(*rows, strict=True))
        assert len(set(columns)) == len(columns)
        for a in range(64):
            left, _ = radix64_f5_directional_views(a, shift)
            for b in range(64):
                _, right = radix64_f5_directional_views(b, shift)
                target = (a >> shift) + ((b % (1 << shift)) << (6 - shift))
                assert radix64_pair_f5_views(left, right, shift) == radix64_f5_class(
                    target
                )


@pytest.mark.parametrize("shift", range(6))
def test_symbolic_pairing_reuses_the_hashlife_semantic_arena(
    shift: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    ledger = ResourceLedger()
    bits = BitFunctionArena(ledger)
    morphism = CollatzOutputMorphism(bits)
    lsize, rsize = F5_DIRECTIONAL_COUNTS[shift]
    ports = (
        FinitePort(PortVariable(0, 0, "F5-left", 0), lsize),
        FinitePort(PortVariable(0, 1, "F5-right", 0), rsize),
    )
    left = bits.variable(ports, ports[0], AtomSort(f"collatz-F5-left-e{shift}", lsize))
    right = bits.variable(
        ports, ports[1], AtomSort(f"collatz-F5-right-e{shift}", rsize)
    )

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("reduced F5 consumer reconstructed an exact target digit")

    monkeypatch.setattr(morphism, "join_directional", forbidden)
    monkeypatch.setattr(morphism, "shift", forbidden)
    result = morphism.pair_f5_views(left, right, shift)
    before = ledger.snapshot()
    assert morphism.pair_f5_views(left, right, shift) == result
    assert ledger.snapshot().nodes == before.nodes
    assert ledger.counters["collatz_f5_directional_hits"] == 1
    assert (
        ledger.counters["semantic_function_workspace_allocated_entries"]
        == before.counters["semantic_function_workspace_allocated_entries"]
    )
    morphism.clear_f5_cache()
    assert morphism.pair_f5_views(left, right, shift) == result
    assert ledger.snapshot().nodes == before.nodes
    for lvalue, row in enumerate(F5_JOIN_TABLES[shift]):
        for rvalue, expected in enumerate(row):
            assert (
                bits.evaluate(
                    result, {ports[0].variable: lvalue, ports[1].variable: rvalue}
                )
                == expected
            )
    assert all(row.accounting_delta in (None, 0) for row in ledger.inventory())
    morphism.clear_f5_cache()


def test_phase_and_directional_methods_bind_the_existing_source_function() -> None:
    bits = BitFunctionArena(ResourceLedger())
    morphism = CollatzOutputMorphism(bits)
    port = FinitePort(PortVariable(0, 0, "source", 0), 64)
    digit = bits.variable((port,), port, DIGIT)
    phase = morphism.f5_class(digit)
    for shift in range(6):
        left, right = morphism.f5_directional_views(digit, shift)
        for d in range(64):
            binding = {port.variable: d}
            assert bits.evaluate(phase, binding) == radix64_f5_class(d)
            assert (
                bits.evaluate(left, binding),
                bits.evaluate(right, binding),
            ) == radix64_f5_directional_views(d, shift)
    foreign_bits = BitFunctionArena(ResourceLedger())
    foreign = foreign_bits.variable((port,), port, DIGIT)
    with pytest.raises(ValueError):
        morphism.f5_class(foreign)
    left, right = morphism.f5_directional_views(digit, 1)
    with pytest.raises(ValueError):
        morphism.pair_f5_views(left, right, 2)


def test_macro_catalog_is_exact_closed_and_minimal_for_its_observers() -> None:
    from number_compiler.arithmetic.carry.collatz_f5_quotient import (
        F5_SPATIAL_LEAF_ALPHABET,
        F5_SPATIAL_MACRO_ALPHABET,
        spatial_action_alphabet,
    )
    from number_compiler.arithmetic.carry.collatz_output_quotient import DOMAIN_ACTIONS
    from number_compiler.arithmetic.functions.finite_observer import (
        minimize_finite_observer,
    )

    leaves, macros = F5_SPATIAL_LEAF_ALPHABET, F5_SPATIAL_MACRO_ALPHABET
    assert {a.then(b) for a in leaves for b in leaves} == spatial_action_alphabet(2)
    assert {a.then(b) for a in macros for b in leaves} == spatial_action_alphabet(6)
    assert spatial_action_alphabet(2) != macros
    for n in range(2, 7):
        for m in range(2, 7):
            assert {
                a.then(b)
                for a in spatial_action_alphabet(n)
                for b in spatial_action_alphabet(m)
            } == spatial_action_alphabet(n + m)
    assert {a.then(b) for a in macros for b in macros} == macros
    states = tuple(sorted(macros))
    # Complete two-sided spatial context graph, using the central minimizer.
    rows = tuple(
        tuple(states.index(a.then(b)) for b in states)
        + tuple(states.index(b.then(a)) for b in states)
        for a in states
    )
    observations = tuple((DOMAIN_ACTIONS[a.carry_action], a.phase) for a in states)
    result = minimize_finite_observer(rows, observations)
    assert result.classes == 17 and len(set(result.class_ids)) == 17


def test_length_phase_cannot_be_dropped_from_macro_admission() -> None:
    from number_compiler.arithmetic.carry.collatz_f5_quotient import (
        RADIX64_F5_SPATIAL_LEAVES,
        spatial_action_alphabet,
    )

    # The same boundary generator repeated twice and five times has different
    # additive phases even though both length alphabets have cardinality 17.
    boundary = RADIX64_F5_SPATIAL_LEAVES[21]
    assert boundary.repeat(2).phase == 2
    assert boundary.repeat(5).phase == 0
    assert boundary.repeat(2) not in spatial_action_alphabet(5)
    all_lengths = frozenset().union(*(spatial_action_alphabet(n) for n in range(2, 7)))
    assert len(all_lengths) == 21
    assert {a.then(b) for a in all_lengths for b in all_lengths} == all_lengths


def test_macro_repeat_eliminates_composition_without_merging_occurrences(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.carry.collatz_f5_quotient import (
        F5_SPATIAL_MACRO_ALPHABET,
        CollatzF5SpatialAction,
        spatial_action_alphabet,
    )

    for action in F5_SPATIAL_MACRO_ALPHABET:
        literal = action
        for n in range(1, 13):
            assert action.repeat(n) == literal
            literal = literal.then(action)

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("closed spatial macro expanded a composition")

    monkeypatch.setattr(CollatzF5SpatialAction, "then", forbidden)
    for n in (5**64, 1 << 4096):
        assert len(spatial_action_alphabet(n)) == 17
        for action in F5_SPATIAL_MACRO_ALPHABET:
            result = action.repeat(n)
            assert result.carry_action == action.carry_action
            assert result.phase == n * action.phase % 5
    for bad in (0, -1, True):
        with pytest.raises(ValueError):
            spatial_action_alphabet(bad)
        with pytest.raises(ValueError):
            CollatzF5SpatialAction(0, 0).repeat(bad)


def test_corrected_generator_birth_emission_census() -> None:
    from collections import defaultdict

    from number_compiler.arithmetic.carry.collatz_binary_forcing import (
        binary_carry_birth,
    )
    from number_compiler.arithmetic.carry.collatz_f5_quotient import (
        RADIX64_F5_SPATIAL_LEAVES,
        CollatzF5SpatialAction,
    )

    by_rule: dict[CollatzF5SpatialAction, set[tuple[tuple[int, ...], ...]]] = (
        defaultdict(set)
    )
    for digit, rule in enumerate(RADIX64_F5_SPATIAL_LEAVES):
        by_rule[rule].add(
            tuple(binary_carry_birth(digit, incoming=c) for c in range(3))
        )
    responses = set.union(*by_rule.values())
    assert len(by_rule) == 15
    assert len(responses) == 33
    assert len({jet for row in responses for jet in row}) == 55
    assert sum(len(rows) > 1 for rows in by_rule.values()) == 9
    assert max(map(len, by_rule.values())) == 5
    # Births are occurrence emissions, not extra coordinates of these rules.
    assert set(CollatzF5SpatialAction.__slots__) == {"carry_action", "phase"}
