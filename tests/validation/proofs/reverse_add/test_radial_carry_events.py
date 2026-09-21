"""Sparse sign consumers and exact limits of an unqualified finite jet."""

from math import comb
from random import Random

from devtools.experiments.reverse_add.radial_carry_events import (
    common_growth_carry_events,
)
from devtools.experiments.reverse_add.radial_modular_sign import ModularSignOracle
from devtools.experiments.reverse_add.radial_sign_runs import ShiftTerm, SignWork
from number_compiler.arithmetic.fields.symbolic_innovation import (
    SymbolicInnovationArena,
)
from number_compiler.arithmetic.polynomials.binomial_pow2 import binomial_mod_pow2
from number_compiler.resources.ledger import ResourceLedger
from tests.arithmetic.fields.test_centered_carry import _evaluate


def test_sign_intervals_feed_the_existing_carry_event_algebra() -> None:
    random = Random(20260920)
    for _ in range(200):
        row, extent, incoming = (
            random.randrange(15),
            random.randrange(30),
            random.randrange(2),
        )
        terms = tuple(
            ShiftTerm(random.randrange(-5, 9), random.randrange(-4, 5))
            for _ in range(random.randrange(6))
        )
        arena = SymbolicInnovationArena(ResourceLedger())
        result = common_growth_carry_events(
            arena, row, terms, extent=extent, incoming=incoming, work=SignWork()
        )
        carry = incoming
        expected: dict[int, int] = {}
        for k in range(extent):
            delta = sum(
                term.coefficient * comb(row, k - term.shift)
                for term in terms
                if 0 <= k - term.shift <= row
            )
            updated = 1 if delta > 0 else 0 if delta < 0 else carry
            if updated != carry:
                expected[k] = updated - carry
            carry = updated
        if carry:
            expected[extent] = -carry
        assert result.terminal == carry
        assert _evaluate(arena, result.jump) == expected
        expected[0] = expected.get(0, 0) + incoming
        assert _evaluate(arena, result.coboundary) == {
            k: v for k, v in expected.items() if v
        }


def test_huge_neutral_and_same_reset_spans_keep_only_boundary_events() -> None:
    width = 10**200
    for terms, incoming, expected in (
        ((), 1, {width: -1}),
        ((ShiftTerm(0, 1),), 1, {width: -1}),
        ((ShiftTerm(0, 1),), 0, {0: 1, width: -1}),
    ):
        arena = SymbolicInnovationArena(ResourceLedger())
        work = SignWork()
        result = common_growth_carry_events(
            arena, width, terms, extent=width, incoming=incoming, work=work
        )
        assert _evaluate(arena, result.jump) == expected
        assert result.sign_intervals == work.sign_queries == 1
        assert work.ratio_factors == 0
        assert arena.ledger.counters["radial_sign_carry_intervals"] == 1


def _centered_pair(seed: int) -> tuple[int, ...]:
    digits = tuple(int(digit) for digit in str(seed)[::-1])
    return tuple(a + b - 9 for a, b in zip(digits, reversed(digits)))


def _jet(delta: tuple[int, ...], order: int) -> tuple[int, ...]:
    # Exact Hasse jet at -1, stronger than equality modulo 16.
    return tuple(
        sum(comb(i, j) * (-1) ** (i - j) * delta[i] for i in range(j, len(delta)))
        for j in range(order + 1)
    )


def _carry_word(delta: tuple[int, ...]) -> tuple[int, ...]:
    carry = 0
    word = []
    for coefficient in delta:
        carry = 1 if coefficient > 0 else 0 if coefficient < 0 else carry
        word.append(carry)
    return tuple(word)


def test_residual_jet_and_growth_do_not_identify_internal_carry_crossings() -> None:
    # Admitted decimal seeds, not an arbitrary array or a future-reachability claim.
    first, second = _centered_pair(555555), _centered_pair(542245)
    assert first == (1, 1, 1, 1, 1, 1)
    assert second == (1, -1, -5, -5, -1, 1)
    # Difference = 2*z*(1+z)^3. Equality is exact, hence holds modulo 16 too.
    assert _jet(first, 2) == _jet(second, 2)
    assert _carry_word(first) == (1, 1, 1, 1, 1, 1)
    assert _carry_word(second) == (1, 0, 0, 0, 0, 1)
    assert _carry_word(first)[-1] == _carry_word(second)[-1] == 1
    # This does not assert a collision in Q's jet or in the full source cylinder.
    assert _jet(_carry_word(first), 1) != _jet(_carry_word(second), 1)


def test_existing_five_bit_binomial_residues_agree_with_crt_sign_recovery() -> None:
    row = 10**200
    k = row // 2
    for delta in range(-9, 10):
        oracle = ModularSignOracle()
        # The first two enormous binomial values cancel exactly. The last
        # packet contributes delta*choose(row,0), proving the magnitude bound.
        terms = ((0, 17), (0, -17), (k, delta))
        residue = sum(c * binomial_mod_pow2(row, k - s, 5) for s, c in terms) % 32
        recovered = residue if residue <= 15 else residue - 32
        assert recovered == delta
        assert oracle.sign(row, terms, k, bound=9) == (delta > 0) - (delta < 0)
        oracle.close()
        assert oracle.work.retained_items == 0
