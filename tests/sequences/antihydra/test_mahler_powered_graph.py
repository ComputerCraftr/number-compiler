"""Independent physical checks for pointed Mahler graph repetition."""

from __future__ import annotations

from fractions import Fraction
from inspect import getattr_static
from random import Random

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.consumer_pullback import ExactRational
from number_compiler.sequences.antihydra.mahler_joint_future import (
    MahlerJointFutureAction,
)
from number_compiler.sequences.antihydra.mahler_powered_graph import (
    certify_graph_row,
    powered_graph,
)
from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm


def _port(source: int, tail: Fraction) -> tuple[int, int]:
    return (
        10 * (source % 10) + (10 * tail.numerator // tail.denominator),
        source // 10 % 2,
    )


def _literal(
    source: int, tail: Fraction, steps: int
) -> tuple[int, Fraction, tuple[tuple[int, int], ...]]:
    ports = [_port(source, tail)]
    for _ in range(steps):
        parity = source & 1
        source = (3 * source + parity) // 2
        tail = (3 * tail - parity) / 2
        ports.append(_port(source, tail))
    return source, tail, tuple(ports)


def test_selected_source_two_copy_graph_row_and_guard() -> None:
    term = AntihydraArithmeticTerm(254, shared_cache=False)
    result = term.result()
    before_nodes = result.ledger.nodes
    outcome = powered_graph(result, Fraction(1, 57), 2)
    assert outcome["status"] == "available"
    assert outcome["source"] == result.h - 1
    assert outcome["port"] == (60, 1)
    assert outcome["physical_ticks"] == 4
    assert outcome["row_ticks"] == 2
    assert outcome["final_fraction"] == "27/304"
    target, tail, ports = _literal(result.h - 1, Fraction(1, 57), 4)
    assert outcome["endpoint"] == target
    assert str(tail) == outcome["final_fraction"]
    assert ports[:3] == ports[2:]
    assert result.ledger.nodes == before_nodes


@pytest.mark.parametrize("source_residue", (16, 64))
def test_catalogue_matches_pointed_ports_through_bounded_repetitions(
    source_residue: int,
) -> None:
    rng = Random(81032)
    for _ in range(200):
        source = source_residue + 80 * rng.randrange(1, 1 << 20)
        tail = Fraction(rng.randrange(0, 12), 1000)
        exact = ExactRational(tail.numerator, tail.denominator)
        for copies in (1, 2, 3, 4):
            endpoint, final, ports = _literal(source, tail, 2 * copies)
            admitted = all(
                ports[index * 2 : index * 2 + 3] == ports[:3] for index in range(copies)
            )
            applied = certify_graph_row(
                source, exact, copies, reserve_bits=lambda _: None
            )
            assert (applied is not None) is admitted
            if applied is not None:
                _, action, actual, actual_tail = applied
                assert action.extent == 2 * copies
                assert actual == endpoint
                assert Fraction(actual_tail.numerator, actual_tail.denominator) == final


def test_stale_source_and_budget_are_rejected() -> None:
    term = AntihydraArithmeticTerm(254, shared_cache=False)
    result = term.result()
    original = result.h
    try:
        object.__setattr__(result, "h", original + 1)
        with pytest.raises(ValueError):
            powered_graph(result, Fraction(1, 57), 2)
    finally:
        object.__setattr__(result, "h", original)
    result.ledger.max_nodes = result.ledger.nodes
    with pytest.raises(BlockContextBudgetExceeded):
        powered_graph(result, Fraction(1, 57), 2)


def test_failure_during_power_releases_scratch(monkeypatch: pytest.MonkeyPatch) -> None:
    result = AntihydraArithmeticTerm(254, shared_cache=False).result()
    before = result.ledger.nodes

    def refuse(*_args: object, **_kwargs: object) -> MahlerJointFutureAction:
        raise RuntimeError("failed publication")

    monkeypatch.setattr(MahlerJointFutureAction, "zero_run", refuse)
    with pytest.raises(RuntimeError, match="failed publication"):
        powered_graph(result, Fraction(1, 57), 2)
    assert result.ledger.nodes == before


def test_invalid_fraction_or_copy_bound_does_not_issue_graph() -> None:
    result = AntihydraArithmeticTerm(0, shared_cache=False).result()
    assert powered_graph(result, Fraction(1, 2), 1)["status"] == "unavailable"
    for copies in (0, 2049, 4097):
        with pytest.raises(ValueError):
            powered_graph(result, Fraction(1, 4), copies)


def test_long_source_row_uses_zero_run_without_occurrence_joins(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    copies = 128
    source = 1 << 260
    tail = Fraction(1, 1 << 261)
    q = ExactRational(tail.numerator, tail.denominator)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("source occurrence discovery was called")

    monkeypatch.setattr(MahlerJointFutureAction, "then", forbidden)
    monkeypatch.setattr(MahlerJointFutureAction, "from_source_prefix", forbidden)
    applied = certify_graph_row(source, q, copies, reserve_bits=lambda _: None)
    assert applied is not None
    _, powered, endpoint, final = applied
    actual, fraction, ports = _literal(source, tail, 2 * copies)
    assert endpoint == actual
    assert Fraction(final.numerator, final.denominator) == fraction
    assert powered.extent == 2 * copies
    for index in range(copies):
        assert ports[index * 2 : index * 2 + 3] == ports[:3]


def test_returned_port_does_not_admit_an_unchecked_adjoining_copy() -> None:
    tail = ExactRational(0)
    first = certify_graph_row(16, tail, 1, reserve_bits=lambda _: None)
    assert first is not None
    _, _, endpoint, final = first
    assert endpoint == 36
    assert _port(endpoint, Fraction(0)) == _port(16, Fraction(0))
    assert certify_graph_row(16, tail, 2, reserve_bits=lambda _: None) is None
    assert certify_graph_row(endpoint, final, 1, reserve_bits=lambda _: None) is None


def test_zero_run_graph_action_equals_ordered_two_tick_power() -> None:
    tail = ExactRational(0)
    first = certify_graph_row(16, tail, 1, reserve_bits=lambda _: None)
    assert first is not None
    for copies in range(1, 17):
        source = 1 << (2 * copies + 4)
        applied = certify_graph_row(source, tail, copies, reserve_bits=lambda _: None)
        assert applied is not None
        assert applied[1] == first[1].power(copies)


def test_rotated_port_requires_its_own_source_and_fraction() -> None:
    even_row = certify_graph_row(
        1 << 12, ExactRational(1, 100000), 2, reserve_bits=lambda _: None
    )
    assert even_row is not None and even_row[0].entry == (60, 1)
    source = 1 << 12
    following = source * 3 // 2
    tail = ExactRational(3, 200000)
    rotated = certify_graph_row(following, tail, 1, reserve_bits=lambda _: None)
    assert rotated is not None and rotated[0].entry == (40, 0)
    assert (
        certify_graph_row(source, ExactRational(1, 5), 2, reserve_bits=lambda _: None)
        is None
    )
    assert (
        certify_graph_row(
            source + 40, ExactRational(1, 100000), 2, reserve_bits=lambda _: None
        )
        is None
    )


def test_mutated_catalogue_operator_is_rejected_and_scratch_released() -> None:
    result = AntihydraArithmeticTerm(254, shared_cache=False).result()
    from number_compiler.sequences.antihydra import mahler_powered_graph

    action: object = getattr_static(mahler_powered_graph, "_ROW_ACTION")
    assert isinstance(action, MahlerJointFutureAction)
    original_gain = action.gain
    before = result.ledger.nodes
    try:
        object.__setattr__(action, "_gain", original_gain + 2)
        with pytest.raises(ValueError, match="catalogue operator has changed"):
            powered_graph(result, Fraction(1, 57), 2)
        assert result.ledger.nodes == before
    finally:
        object.__setattr__(action, "_gain", original_gain)
