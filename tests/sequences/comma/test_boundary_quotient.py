"""Independent bounded checks for symbolic comma boundary macros."""

from __future__ import annotations

import math
from typing import Literal

import pytest

from number_compiler.sequences.comma import boundary_quotient
from number_compiler.sequences.comma.arithmetic import (
    comma_children,
    cycle_transfer,
    decimal_sector,
    safe_complete_cycles,
)
from number_compiler.sequences.comma.boundary_quotient import (
    AffineWeight,
    BoundaryState,
    construct_macro,
)


def _literal_children(value: int) -> tuple[int, ...]:
    """Small independent nine-candidate oracle, never used by production."""
    digit = value % 10
    children: list[int] = []
    for child_digit in range(1, 10):
        candidate = value + 10 * digit + child_digit
        if int(str(candidate)[0]) == child_digit:
            children.append(candidate)
    return tuple(children)


def _literal_phase_jump(value: int) -> tuple[int, int]:
    """Derive an admitted whole phase using only literal child enumeration."""
    sector = decimal_sector(value)
    period = 10 // math.gcd(sector.leading, 10)
    cursor = value
    maximum = 0
    for _ in range(period):
        children = _literal_children(cursor)
        if len(children) != 1 or decimal_sector(children[0]).leading != sector.leading:
            return value, 0
        cursor = children[0]
        maximum = max(maximum, cursor - value)
    displacement = cursor - value
    # A second full phase has exactly the same literal offset because the
    # last digit returned to its entering value.  Strict admission is tested
    # at the last visited term of each repeated phase.
    headroom = sector.boundary - value
    count = (headroom - 1 - maximum) // displacement + 1
    if count <= 0:
        return value, 0
    return value + count * displacement, count * period


def _reference_macro(value: int) -> tuple[int, int, tuple[int, ...]]:
    steps = 0
    for _ in range(4096):
        children = _literal_children(value)
        if len(children) != 1:
            return value, steps, children
        jumped, count = _literal_phase_jump(value)
        if count:
            value = jumped
            steps += count
        else:
            value = children[0]
            steps += 1
    raise AssertionError("reference comma macro did not reach a boundary event")


def _reference_point(value: int, transitions: int) -> int:
    elapsed = 0
    for _ in range(4096):
        if elapsed == transitions:
            return value
        jumped, skipped = _literal_phase_jump(value)
        if skipped:
            sector = decimal_sector(value)
            period = 10 // math.gcd(sector.leading, 10)
            complete = min(skipped // period, (transitions - elapsed) // period)
            displacement = (jumped - value) // (skipped // period)
            if complete:
                value += complete * displacement
                elapsed += complete * period
                continue
        children = _literal_children(value)
        assert len(children) == 1
        value = children[0]
        elapsed += 1
    raise AssertionError("reference comma point did not reach its offset")


@pytest.mark.parametrize(
    ("kind", "a", "exponent"),
    [
        ("N", 2, 5),
        ("Z", 2, 5),
        ("N", 3, 5),
        ("N", 2, 10),
        ("Z", 2, 10),
        ("N", 9, 6),
        ("Z", 8, 7),
    ],
)
def test_symbolic_macro_matches_independent_literal_phase_reference(
    kind: Literal["N", "Z"], a: int, exponent: int
) -> None:
    state = BoundaryState(kind, a, exponent)
    macro = construct_macro(state)
    endpoint, steps, children = _reference_macro(state.value(exponent))
    assert macro.weight.evaluate(exponent) == steps
    assert macro.endpoint.evaluate(exponent) == endpoint
    assert (macro.outcome == "fork") == (len(children) == 2)
    if children:
        assert macro.destination_a is not None
        assert children == tuple(
            child.value(exponent + macro.exponent_delta)
            for child in macro.ordered_children
        )
        assert endpoint < children[0]
    else:
        assert macro.ordered_children == ()


def test_affine_weight_refuses_nonintegral_or_forged_components() -> None:
    assert AffineWeight(2, 2, 2) == AffineWeight(1, 1, 1)
    with pytest.raises(ValueError, match="not integral"):
        AffineWeight(1, 0, 3).evaluate(1)
    with pytest.raises(ValueError, match="invalid comma affine"):
        AffineWeight(1, 0, 0)


def test_boundary_state_rejects_wrong_residue_and_range() -> None:
    state = BoundaryState("N", 2, 10)
    assert state.value(10) == 19_999_999_999
    with pytest.raises(ValueError, match="exponent does not belong"):
        state.value(11)
    with pytest.raises(ValueError, match="invalid comma boundary"):
        BoundaryState("N", 10, 10)


def test_tropical_sector_rule_agrees_with_literal_nine_child_search() -> None:
    for value in range(100, 10_001):
        assert comma_children(value) == _literal_children(value)
    for scale in (100, 1000, 10000):
        for leading in range(1, 10):
            for headroom in range(1, 102):
                value = (leading + 1) * scale - headroom
                if value // scale != leading:
                    continue
                assert comma_children(value) == _literal_children(value)


def test_large_sector_children_do_not_search_candidate_leading_digits(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.comma import arithmetic

    values = (100, 107, 199, 999, 1000, 1999, 9999, 10_000, 99_999)
    expected = {value: _literal_children(value) for value in values}

    def forbidden(_: int) -> int:
        raise AssertionError("large-sector path enumerated candidate leading digits")

    monkeypatch.setattr(arithmetic, "leading_digit", forbidden)
    for value in values:
        assert comma_children(value) == expected[value]


@pytest.mark.parametrize(
    ("kind", "a", "exponent"),
    [("N", 2, 10), ("Z", 2, 10), ("N", 3, 5), ("N", 2, 934)],
)
def test_weighted_partial_descent_matches_independent_reference(
    kind: Literal["N", "Z"], a: int, exponent: int
) -> None:
    state = BoundaryState(kind, a, exponent % 924)
    macro = construct_macro(state)
    total = macro.weight.evaluate(exponent)
    checkpoints = {0, 1, 3, 10, total // 2, total - 1, total}
    for fragment_prefix in macro.prefix_weights[:5]:
        boundary = fragment_prefix.evaluate(exponent)
        checkpoints.add(boundary)
        if boundary < total:
            checkpoints.add(boundary + 1)
    for offset in sorted(checkpoints):
        assert macro.point(exponent, offset) == _reference_point(
            state.value(exponent), offset
        )
    with pytest.raises(ValueError, match="exceeds endpoint"):
        macro.point(exponent, total + 1)


def test_partial_selection_charges_logarithmic_fragment_search() -> None:
    construction: list[int] = []
    state = BoundaryState("N", 3, 5)
    macro = construct_macro(state, charge=construction.append)
    assert sum(construction) >= len(macro.sector_fragments)
    demand: list[int] = []
    midpoint = macro.weight.evaluate(5) // 2
    assert macro.point(5, midpoint, charge=demand.append) == _reference_point(
        state.value(5), midpoint
    )
    assert 0 < sum(demand) <= math.ceil(math.log2(len(macro.sector_fragments))) + 12


def test_partial_selection_reuses_one_power_and_rejects_invalid_before_it(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    macro = construct_macro(BoundaryState("N", 2, 10))
    midpoint = macro.weight.evaluate(10) // 2
    powers: list[int] = []
    actual_pow = pow

    def counted_pow(base: int, exponent: int) -> int:
        powers.append(exponent)
        return int(actual_pow(base, exponent))

    monkeypatch.setattr(boundary_quotient, "pow", counted_pow, raising=False)
    with pytest.raises(ValueError, match="offset must be nonnegative"):
        macro.point(10, -1)
    with pytest.raises(ValueError, match="does not belong"):
        macro.point(11, 1)
    assert powers == []
    bit_work: list[int] = []
    macro.point(10, midpoint, charge_bits=bit_work.append)
    assert powers == [10]
    assert sum(bit_work) > 0


def test_macro_constructor_pins_sample_scale_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    powers: list[int] = []
    actual_pow = pow

    def counted_pow(base: int, exponent: int) -> int:
        powers.append(exponent)
        return int(actual_pow(base, exponent))

    monkeypatch.setattr(boundary_quotient, "pow", counted_pow, raising=False)
    macro = construct_macro(BoundaryState("N", 3, 5))
    assert macro.outcome == "landmine"
    assert powers == [5]


def test_bit_budget_rejects_before_boundary_power_allocations(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    macro = construct_macro(BoundaryState("N", 2, 10))

    def forbidden_pow(*_args: int) -> int:
        raise AssertionError("large power allocated before bit admission")

    def refuse(_bits: int) -> None:
        raise ValueError("bit budget")

    monkeypatch.setattr(boundary_quotient, "pow", forbidden_pow, raising=False)
    with pytest.raises(ValueError, match="bit budget"):
        macro.source.value(934, charge_bits=refuse)
    with pytest.raises(ValueError, match="bit budget"):
        macro.weight.evaluate(934, charge_bits=refuse)
    with pytest.raises(ValueError, match="bit budget"):
        macro.point(934, 1, charge_bits=refuse)
    with pytest.raises(ValueError, match="bit budget"):
        construct_macro(BoundaryState("N", 3, 5), charge_bits=refuse)


@pytest.mark.parametrize(
    ("kind", "a", "base_exponent"),
    [("N", 2, 10), ("Z", 2, 10), ("N", 3, 5), ("Z", 8, 7)],
)
def test_macro_fragments_transport_over_one_exponent_period(
    kind: Literal["N", "Z"], a: int, base_exponent: int
) -> None:
    state = BoundaryState(kind, a, base_exponent)
    macro = construct_macro(state)
    exponent = base_exponent + 924
    value = state.value(exponent)
    steps = 0
    for fragment in macro.sector_fragments:
        sector = decimal_sector(value)
        assert (sector.leading, sector.digit) == (
            fragment.leading,
            fragment.entering_digit,
        )
        if fragment.displacement:
            transfer = cycle_transfer(sector.leading, sector.digit)
            count = fragment.complete_cycles.evaluate(exponent)
            assert (transfer.period, transfer.displacement, transfer.maximum_guard) == (
                fragment.period,
                fragment.displacement,
                fragment.maximum_guard,
            )
            assert (
                safe_complete_cycles(value, transfer, (count + 1) * transfer.period)
                == count
            )
            value += count * transfer.displacement
            steps += count * transfer.period
        else:
            assert fragment.literal_steps == 1
            children = _literal_children(value)
            assert len(children) == 1
            assert fragment.literal_increment == children[0] - value
            value = children[0]
            steps += 1
    assert steps == macro.weight.evaluate(exponent)
    assert value == macro.endpoint.evaluate(exponent)
    assert len(_literal_children(value)) == (2 if macro.outcome == "fork" else 0)
