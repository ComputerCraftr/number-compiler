"""Exact weighted comma actions; branch admission is a separate proof."""

from __future__ import annotations

import pytest

from number_compiler.sequences.comma import weighted_return
from number_compiler.sequences.comma.boundary_quotient import (
    AffineWeight,
    BoundaryState,
    construct_macro,
)
from number_compiler.sequences.comma.weighted_return import WeightedBoundaryAction


def test_chronological_weight_transport_and_associativity() -> None:
    q0 = BoundaryState("N", 2, 10)
    q1 = BoundaryState("Z", 4, 11)
    q2 = BoundaryState("N", 7, 13)
    q3 = BoundaryState("Z", 8, 16)
    a = WeightedBoundaryAction(q0, q1, 1, AffineWeight(3, 5, 1))
    b = WeightedBoundaryAction(q1, q2, 2, AffineWeight(7, 11, 1))
    c = WeightedBoundaryAction(q2, q3, 3, AffineWeight(13, 17, 1))
    joined = a.then(b).then(c)
    assert joined == a.then(b.then(c))
    assert joined.weight.evaluate(10) == (
        a.weight.evaluate(10) + b.weight.evaluate(11) + c.weight.evaluate(13)
    )
    assert joined.exponent_delta == 6
    assert a.then(WeightedBoundaryAction.identity(q1)) == a
    assert WeightedBoundaryAction.identity(q0).then(a) == a


def test_selected_fork_adds_exactly_one_transition_without_claiming_survival() -> None:
    macro = construct_macro(BoundaryState("N", 2, 10))
    assert len(macro.ordered_children) == 2
    for child in macro.ordered_children:
        action = WeightedBoundaryAction.from_selected_fork(macro, child)
        assert action.start == macro.source
        assert action.end == child
        assert action.weight.evaluate(10) == macro.weight.evaluate(10) + 1
    with pytest.raises(ValueError, match="not an exact fork alternative"):
        WeightedBoundaryAction.from_selected_fork(macro, BoundaryState("N", 2, 10))


def test_two_exact_fork_macros_transport_weight_at_shifted_exponents() -> None:
    first_macro = construct_macro(BoundaryState("N", 2, 10))
    first = WeightedBoundaryAction.from_selected_fork(
        first_macro, first_macro.ordered_children[0]
    )
    second_macro = construct_macro(first.end)
    second = WeightedBoundaryAction.from_selected_fork(
        second_macro, second_macro.ordered_children[0]
    )
    combined = first.then(second)
    for exponent in (10, 10 + 924):
        assert combined.weight.evaluate(exponent) == (
            first_macro.weight.evaluate(exponent)
            + 1
            + second_macro.weight.evaluate(exponent + first.exponent_delta)
            + 1
        )


def test_repeated_return_geometric_weight_matches_bounded_chronology() -> None:
    q = BoundaryState("N", 2, 10)
    base = WeightedBoundaryAction(q, q, 924, AffineWeight(3, 7, 1))
    for count in range(7):
        repeated = base.repeat(count)
        chronological = WeightedBoundaryAction.identity(q)
        for _ in range(count):
            chronological = chronological.then(base)
        exact = chronological.weight.evaluate(10)
        assert repeated.weight_at(10) == exact
        for cap in (0, 1, 10**6, exact):
            assert repeated.weight_at(10, cap=cap) == min(exact, cap + 1)
        assert repeated.exponent_delta == 924 * count


def test_large_repetition_cap_uses_logarithmic_binary_work(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    q = BoundaryState("N", 2, 10)
    base = WeightedBoundaryAction(q, q, 924, AffineWeight(1, 1, 1))
    charges: list[int] = []
    bit_work: list[int] = []
    actual_pow = pow

    def bounded_pow(radix: int, exponent: int) -> int:
        assert exponent < 10_000
        return int(actual_pow(radix, exponent))

    monkeypatch.setattr(weighted_return, "pow", bounded_pow, raising=False)
    assert (
        base.repeat(10**12).weight_at(
            10, cap=10**9, charge=charges.append, charge_bits=bit_work.append
        )
        == 10**9 + 1
    )
    assert base.repeat(10**12).weight_at(10 + 924 * 1000, cap=10**9) == 10**9 + 1
    assert sum(charges) < 100
    assert sum(bit_work) > 0


def test_capped_shared_skew_power_matches_small_geometric_sums() -> None:
    for base in (1, 2, 3, 10):
        for count in range(10):
            exact = sum(base**i for i in range(count))
            for cap in (0, 1, 2, 9, 100):
                assert weighted_return._capped_geometric(
                    base, count, cap, None, None
                ) == min(exact, cap)


def test_constant_weight_and_unused_clock_factors_do_not_allocate_huge_powers(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    q = BoundaryState("N", 2, 10)
    constant = WeightedBoundaryAction(q, q, 924, AffineWeight(0, 7, 1))
    huge_delta = WeightedBoundaryAction(q, q, 924 * 10**8, AffineWeight(0, 1, 1))
    actual_pow = pow

    def bounded_pow(base: int, exponent: int) -> int:
        assert exponent < 10_000
        return int(actual_pow(base, exponent))

    monkeypatch.setattr(weighted_return, "pow", bounded_pow, raising=False)
    assert constant.repeat(10**12).weight_at(10 + 924 * 10**8) == 7 * 10**12
    assert huge_delta.then(constant).weight == AffineWeight(0, 8, 1)
    live = WeightedBoundaryAction(q, q, 924, AffineWeight(1, 0, 1))
    assert live.then(huge_delta).weight.evaluate(10) == 10**10 + 1


def test_uncapped_geometric_allocation_is_charged_before_power(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    q = BoundaryState("N", 2, 10)
    action = WeightedBoundaryAction(q, q, 924, AffineWeight(1, 1, 1))
    actual_pow = pow

    def bounded_pow(base: int, exponent: int) -> int:
        assert exponent < 1000
        return int(actual_pow(base, exponent))

    def admit_small_bits(bits: int) -> None:
        if bits > 100_000:
            raise ValueError("bit budget")

    monkeypatch.setattr(weighted_return, "pow", bounded_pow, raising=False)
    with pytest.raises(ValueError, match="bit budget"):
        action.repeat(1000).weight_at(10, charge_bits=admit_small_bits)


def test_wrong_source_or_exponent_transport_is_rejected() -> None:
    q0 = BoundaryState("N", 2, 10)
    q1 = BoundaryState("Z", 4, 11)
    q2 = BoundaryState("N", 7, 13)
    with pytest.raises(ValueError, match="inconsistent exponent residue"):
        WeightedBoundaryAction(q0, q1, 2, AffineWeight(1, 0, 1))
    a = WeightedBoundaryAction(q0, q1, 1, AffineWeight(1, 0, 1))
    b = WeightedBoundaryAction(q2, q2, 924, AffineWeight(1, 0, 1))
    with pytest.raises(ValueError, match="different boundary bindings"):
        a.then(b)
    with pytest.raises(ValueError, match="complete Q-to-Q"):
        a.repeat(2)
    with pytest.raises(ValueError, match="another source exponent"):
        b.repeat(1).weight_at(10)


@pytest.mark.parametrize(
    "weight", [AffineWeight(1, 1, 1), AffineWeight(1, -(10**10) + 1, 1)]
)
def test_partial_repeated_return_matches_bounded_literal_weights(
    weight: AffineWeight,
) -> None:
    q = BoundaryState("N", 2, 10)
    action = WeightedBoundaryAction(q, q, 924, weight)
    repeated = action.repeat(5)
    prefix = [0]
    for i in range(5):
        prefix.append(prefix[-1] + weight.evaluate(10 + i * 924))
    checkpoints = {0, 1, prefix[-1] // 2, prefix[-1]}
    for boundary in prefix:
        checkpoints.add(boundary)
        if boundary:
            checkpoints.add(boundary - 1)
        if boundary < prefix[-1]:
            checkpoints.add(boundary + 1)
    for offset in sorted(checkpoints):
        expected_count = max(i for i, elapsed in enumerate(prefix) if elapsed <= offset)
        assert repeated.split_at(10, offset) == (
            expected_count,
            offset - prefix[expected_count],
        )
    with pytest.raises(ValueError, match="exceeds repeated return"):
        repeated.split_at(10, prefix[-1] + 1)


def test_huge_partial_repetition_uses_capped_binary_descent(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    q = BoundaryState("N", 2, 10)
    action = WeightedBoundaryAction(q, q, 924, AffineWeight(1, 1, 1))
    repeated = action.repeat(10**12)
    first = action.weight.evaluate(10)
    actual_pow = pow

    def bounded_pow(base: int, exponent: int) -> int:
        assert exponent < 10_000
        return int(actual_pow(base, exponent))

    monkeypatch.setattr(weighted_return, "pow", bounded_pow, raising=False)
    charges: list[int] = []
    bit_work: list[int] = []
    assert repeated.split_at(
        10, first + 17, charge=charges.append, charge_bits=bit_work.append
    ) == (1, 17)
    assert sum(charges) < 100
    assert sum(bit_work) > 0


def test_zero_identity_repetition_has_exact_endpoint() -> None:
    q = BoundaryState("N", 2, 10)
    repeated = WeightedBoundaryAction.identity(q).repeat(10**12)
    assert repeated.split_at(10, 0) == (10**12, 0)
    with pytest.raises(ValueError, match="exceeds repeated return"):
        repeated.split_at(10, 1)


def test_identity_composition_reuses_action_after_binding_and_budget_checks(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    q = BoundaryState("N", 2, 10)
    live = WeightedBoundaryAction(q, q, 924, AffineWeight(1, 1, 1))
    identity = WeightedBoundaryAction.identity(q)
    foreign = WeightedBoundaryAction.identity(BoundaryState("Z", 2, 10))

    def forbidden_pow(*_args: int) -> int:
        raise AssertionError("identity composition allocated a decimal power")

    monkeypatch.setattr(weighted_return, "pow", forbidden_pow, raising=False)
    work: list[int] = []
    bits: list[int] = []
    assert identity.then(live, charge=work.append, charge_bits=bits.append) is live
    assert live.then(identity, charge=work.append, charge_bits=bits.append) is live
    assert sum(work) == 2 and sum(bits) > 0
    with pytest.raises(ValueError, match="different boundary bindings"):
        foreign.then(live)

    def refused(_bits: int) -> None:
        raise ValueError("bit budget")

    with pytest.raises(ValueError, match="bit budget"):
        identity.then(live, charge_bits=refused)
    with pytest.raises(ValueError, match="bit budget"):
        live.then(identity, charge_bits=refused)
    with pytest.raises(ValueError, match="bit budget"):
        identity.then(live, charge=refused)
    with pytest.raises(ValueError, match="bit budget"):
        live.then(identity, charge=refused)


def test_zero_offset_and_zero_cap_do_not_construct_exponent_powers(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    q = BoundaryState("N", 2, 10)
    live = WeightedBoundaryAction(q, q, 924, AffineWeight(1, -(10**10) + 1, 1))
    identity = WeightedBoundaryAction.identity(q)
    exponent = 10 + 924 * 10**6

    def forbidden_pow(*_args: int) -> int:
        raise AssertionError("zero-threshold selection allocated a decimal power")

    monkeypatch.setattr(weighted_return, "pow", forbidden_pow, raising=False)
    assert live.repeat(10**12).split_at(exponent, 0) == (0, 0)
    assert live.repeat(10**12).weight_at(exponent, cap=0) == 1
    assert identity.repeat(10**12).split_at(exponent, 0) == (10**12, 0)
    assert identity.repeat(10**12).weight_at(exponent, cap=0) == 0


def test_forged_negative_fractional_and_zero_progress_returns_are_rejected() -> None:
    q = BoundaryState("N", 2, 10)
    with pytest.raises(ValueError, match="natural literal count"):
        WeightedBoundaryAction(q, q, 0, AffineWeight(0, -1, 1))
    with pytest.raises(ValueError, match="natural literal count"):
        WeightedBoundaryAction(q, q, 0, AffineWeight(0, 1, 2))
    with pytest.raises(ValueError, match="integral on its residue ray"):
        WeightedBoundaryAction(q, q, 924, AffineWeight(1, -(10**10 % 17), 17))
    with pytest.raises(ValueError, match="no literal progress"):
        WeightedBoundaryAction(q, q, 924, AffineWeight(0, 0, 1))
    with pytest.raises(ValueError, match="natural literal count"):
        WeightedBoundaryAction(q, q, 924, AffineWeight(1, -(10**10), 1))
    with pytest.raises(ValueError, match="cannot revisit a fixed value"):
        WeightedBoundaryAction(q, q, 0, AffineWeight(0, 1, 1))
