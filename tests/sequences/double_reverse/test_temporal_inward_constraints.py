"""Independent oracles for recursive two-sided 2rev10 carry safety."""

from __future__ import annotations

import random

import pytest

from number_compiler.sequences.double_reverse.temporal_inward_constraints import (
    InconsistentDigitConstraints,
    InwardCarryConstraints,
)


def _iterate(seed: int, duration: int) -> tuple[int, ...]:
    result = [seed]
    for _ in range(duration):
        result.append(2 * int(str(result[-1])[::-1]))
    return tuple(result)


def _checked_solver(
    trajectory: tuple[int, ...], boundary: int, *, residue: int | None = 99
) -> InwardCarryConstraints:
    words = tuple(str(x) for x in trajectory)
    solver = InwardCarryConstraints(tuple(len(w) for w in words))
    for time, word in enumerate(words):
        solver.constrain_prefix(time, word[:boundary])
        solver.constrain_suffix(time, word[-boundary:])
        if residue is not None:
            solver.constrain_residue(time, residue, trajectory[time] % residue)
    return solver


def _assert_sound(trajectory: tuple[int, ...], solver: InwardCarryConstraints) -> None:
    for t, number in enumerate(trajectory):
        word = str(number)
        for i, char in enumerate(word):
            digit = int(char)
            assert digit in solver.digits(t, i)
            assert int(digit >= 5) in solver.carry(t, i)
        if t + 1 == len(trajectory):
            continue
        nxt = str(trajectory[t + 1])
        bit = 0
        for i in range(max(len(word), len(nxt))):
            a = int(nxt[i]) if i < len(nxt) else 0
            b = int(word[i]) if i < len(word) else 0
            bit = int(a < b + bit)
            assert bit in solver.borrow(t, i + 1)


def _assert_single_step_reversal_is_exact(x: int) -> None:
    nxt = 2 * int(str(x)[::-1])
    grammar = InwardCarryConstraints((len(str(x)), len(str(nxt))))
    grammar.constrain_prefix(0, str(x))
    answer = grammar.propagate()
    assert answer.known_digit_counts[-1] == len(str(nxt))
    assert "".join(str(grammar.digits(1, i)[0]) for i in range(len(str(nxt)))) == str(
        nxt
    )
    _assert_sound((x, nxt), grammar)


@pytest.mark.algebra
def test_exact_reversal_cell_arithmetic_growth_and_contraction() -> None:
    for x in (196, 173488, 174388, 1768742, 123400, 50000, 900):
        _assert_single_step_reversal_is_exact(x)


@pytest.mark.algebra
@pytest.mark.validation  # Seeded 200-source differential fuzz grid.
def test_randomized_reversal_cell_arithmetic_growth_and_contraction() -> None:
    rng = random.Random(20261016)
    for _ in range(200):
        x = rng.randrange(1, 10**7)
        _assert_single_step_reversal_is_exact(x)


@pytest.mark.algebra
def test_future_digits_restrict_past_digits_bidirectionally() -> None:
    for x in (173488, 174388, 123400, 1700042, 900, 555):
        y = 2 * int(str(x)[::-1])
        grammar = InwardCarryConstraints((len(str(x)), len(str(y))))
        grammar.constrain_prefix(1, str(y))
        grammar.propagate()
        assert all(grammar.digits(0, i) == (int(d),) for i, d in enumerate(str(x)))


@pytest.mark.algebra
def test_source_derived_high_to_low_carry_conflict_is_rejected() -> None:
    grammar = InwardCarryConstraints((6, 7))
    grammar.constrain_prefix(0, "173")
    grammar.constrain_suffix(0, "488")
    grammar.constrain_prefix(1, "16")  # actual next prefix is 17
    with pytest.raises(InconsistentDigitConstraints):
        grammar.propagate()


@pytest.mark.algebra
def test_authenticated_two_sided_orbits_prune_beyond_forward_only() -> None:
    seed = 17781675275941694822050964043040742  # user generation 73
    trajectory = _iterate(seed, 24)
    forward = _checked_solver(trajectory, 2)
    backward = _checked_solver(trajectory, 2)
    a = forward.propagate(direction="forward")
    b = backward.propagate(direction="both")
    assert sum(b.known_digit_counts) >= sum(a.known_digit_counts) + 20
    # Future border constraints eliminate digit and carry possibilities on
    # BOTH source sides, without adding any interior observation by hand.
    first_w = len(str(seed))
    assert len(backward.digits(0, 2)) < len(forward.digits(0, 2))
    assert len(backward.digits(0, first_w - 3)) < len(forward.digits(0, first_w - 3))
    _assert_sound(trajectory, backward)


@pytest.mark.algebra
def test_mod99_joint_constraints_can_close_a_small_inner_halo() -> None:
    trajectory = _iterate(173488, 12)
    grammar = _checked_solver(trajectory, 2, residue=99)
    report = grammar.propagate()
    assert report.conditional_digit_counts == (0,) * len(trajectory)
    _assert_sound(trajectory, grammar)


@pytest.mark.algebra
@pytest.mark.validation  # Seeded multi-trajectory carry-domain fuzz grid.
def test_random_sources_remain_admissible_with_conditional_raw_borrows() -> None:
    rng = random.Random(198303)
    # Deterministic randomized smoke coverage remains broad while bounding the
    # expensive whole-trajectory oracle to representative source histories.
    for _ in range(24):
        seed = rng.randrange(10**5, 10**10)
        steps = rng.randrange(1, 7)
        trajectory = _iterate(seed, steps)
        grammar = _checked_solver(trajectory, 2, residue=99)
        grammar.propagate()
        _assert_sound(trajectory, grammar)


@pytest.mark.algebra
def test_raw_borrow_constraint_rejects_false_alternative() -> None:
    source, target = _iterate(173488, 1)
    grammar = InwardCarryConstraints((len(str(source)), len(str(target))))
    grammar.constrain_prefix(0, str(source))
    grammar.constrain_prefix(1, str(target))
    grammar.propagate()
    true_borrow = grammar.borrow(0, 3)
    assert len(true_borrow) == 1
    false = 1 - true_borrow[0]
    with pytest.raises(InconsistentDigitConstraints):
        grammar.constrain_borrow(0, 3, false)


@pytest.mark.algebra
def test_width_trace_not_inferred_from_modular_cursor() -> None:
    with pytest.raises(ValueError, match="successor widths"):
        InwardCarryConstraints((6, 9))
    with pytest.raises(InconsistentDigitConstraints):
        grammar = InwardCarryConstraints((6, 7))
        grammar.constrain_suffix(0, "488")
        grammar.constrain_prefix(1, "19")
        grammar.propagate()


@pytest.mark.algebra
def test_existing_carry_safety_wrapper_reuses_recursive_network() -> None:
    from number_compiler.sequences.double_reverse.boundary_cycles import (
        edge_from_digits,
    )
    from number_compiler.sequences.double_reverse.temporal_carry_safety import (
        lift_from_digits,
        recursive_carry_trace,
    )

    trajectory = _iterate(17781675275941694822050964043040742, 12)
    edges = tuple(edge_from_digits(str(x)) for x in trajectory)
    widths = tuple(len(str(x)) for x in trajectory)
    summary = recursive_carry_trace(
        lift_from_digits(str(trajectory[0])),
        edges,
        widths,
        residues99=tuple(x % 99 for x in trajectory),
    )
    assert sum(summary.known_digit_counts) > 2 * len(trajectory) * 2
    assert len(summary.raw_reverse_borrow_vectors) == len(trajectory) - 1
    bad = list(edges)
    bad[1] = (1, 6, bad[1][2], bad[1][3])  # incompatible future head
    with pytest.raises(ValueError):
        recursive_carry_trace(
            lift_from_digits(str(trajectory[0])),
            tuple(bad),
            widths,
        )


@pytest.mark.algebra
def test_joint_gt_eq_lt_and_xor_guards_feed_digit_domains() -> None:
    # Pair-sum 15..18 means GT-high; XOR zero forces BOTH digits >=5,
    # because two low digits cannot sum to 15. The guards are declarative,
    # not inferred from a guessed trajectory.
    grammar = InwardCarryConstraints((8,))
    grammar.constrain_pair_band(0, 1, "gt_high")
    grammar.constrain_reflected_xor(0, 1, 0)
    output = grammar.propagate()
    assert grammar.carry(0, 1) == (1,)
    assert grammar.carry(0, 6) == (1,)
    assert output.pair_domains[0][1] == ("gt_high",)

    impossible = InwardCarryConstraints((8,))
    impossible.constrain_pair_band(0, 1, "gt_high")
    impossible.constrain_reflected_xor(0, 1, 1)
    with pytest.raises(InconsistentDigitConstraints):
        impossible.propagate()


@pytest.mark.algebra
def test_odd_center_pair_domain_uses_one_digit_not_two() -> None:
    grammar = InwardCarryConstraints((5,))
    grammar.constrain(0, 2, (4, 5))
    assert grammar.summary().pair_domains[0][2] == ("lt_high", "gt_low")
    grammar.constrain_pair_band(0, 2, "eq")
    with pytest.raises(InconsistentDigitConstraints):
        grammar.propagate()
