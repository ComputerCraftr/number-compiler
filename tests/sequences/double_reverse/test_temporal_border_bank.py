"""Temporal (not spatial-digit) GT-high/carry/borrow Moore certificates."""

from __future__ import annotations

from itertools import product
from typing import Literal, TypeAlias

import pytest

from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.sequences.double_reverse.boundary_cycles import (
    edge_from_digits,
)
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.temporal_border_bank import (
    EDGE_STATES,
    OBSERVERS,
    TemporalObserver,
    _output,
    _step,
    minimize_temporal_border,
    power_temporal_border,
    pumped_border_word,
)

ScalarTemporalObserver: TypeAlias = Literal[
    "gt_high",
    "carry_edge",
    "reflected_xor",
    "raw_borrow",
    "innovation_xor",
    "growth",
]
PumpedTemporalObserver: TypeAlias = Literal["growth", "carry_edge", "reflected_xor"]
SCALAR_OBSERVERS: tuple[ScalarTemporalObserver, ...] = (
    "gt_high",
    "carry_edge",
    "reflected_xor",
    "raw_borrow",
    "innovation_xor",
    "growth",
)
PUMPED_OBSERVERS: tuple[PumpedTemporalObserver, ...] = (
    "growth",
    "carry_edge",
    "reflected_xor",
)


def _literal_step(source: int) -> int:
    return 2 * int(str(source)[::-1])


def _literal_ports(source: int, successor: int) -> dict[ScalarTemporalObserver, int]:
    original, new = str(source), str(successor)
    a, b, y, z = map(int, (original[0], original[1], original[-2], original[-1]))
    carry = sum(int(digit >= 5) << index for index, digit in enumerate((a, b, y, z)))
    borrows = int(int(new[0]) < a) + 2 * int(
        int(new[:2][::-1]) < int(original[:2][::-1])
    )
    return {
        "gt_high": int(a + z >= 15) + 2 * int(b + y >= 15),
        "carry_edge": carry,
        "reflected_xor": int((a >= 5) != (z >= 5)) + 2 * int((b >= 5) != (y >= 5)),
        "raw_borrow": borrows,
        "innovation_xor": (carry & 3) ^ borrows,
        "growth": len(new) - len(original),
    }


@pytest.mark.validation
def test_temporal_moore_is_future_closed_for_both_inward_carries() -> None:
    counts: dict[TemporalObserver, tuple[int, int]] = {
        "gt_high": (2, 8),
        "carry_edge": (2, 4),
        "reflected_xor": (2, 4),
        "raw_borrow": (3, 5),
        "innovation_xor": (3, 5),
        "growth": (2, 4),
        "joint": (6, 8),
    }
    for observer in OBSERVERS:
        moore = minimize_temporal_border(observer)
        assert (moore.initial_class_count, moore.state_count) == counts[observer]
        assert moore.state_count < 10
        # Independent exhaustive bounded-continuation check: distinguish
        # quotient states using actual temporal *emission traces*, not a
        # comparison of initial digits or spatial stencil inputs.
        for i, source in enumerate(EDGE_STATES):
            for j, other in enumerate(EDGE_STATES):
                same = moore.classes[i] == moore.classes[j]
                witness = False
                for n in range(5):
                    for word in product((0, 1), repeat=n):
                        left, right = source, other
                        outputs_left: list[tuple[int, ...]] = []
                        outputs_right: list[tuple[int, ...]] = []
                        for ingress in word:
                            outputs_left.append(_output(left, ingress, observer))
                            outputs_right.append(_output(right, ingress, observer))
                            left = _step(left, ingress)[0]
                            right = _step(right, ingress)[0]
                        if outputs_left != outputs_right:
                            witness = True
                            break
                    if witness:
                        break
                assert witness != same, (observer, source, other)


@pytest.mark.validation
def test_binary_squared_moore_ranges_match_independent_branch_enumeration() -> None:
    for edge in EDGE_STATES:
        for observer in OBSERVERS:
            if observer == "joint":
                continue
            for depth in range(8):
                paths = {(edge, 0)}
                for _ in range(depth):
                    paths = {
                        (_step(state, bit)[0], cost + _output(state, bit, observer)[0])
                        for state, cost in paths
                        for bit in (0, 1)
                    }
                expected_values = {
                    _output(state, bit, observer)
                    for state, _ in paths
                    for bit in (0, 1)
                }
                report = power_temporal_border(edge, depth, observer)
                assert report.minimum_emission_sum == min(cost for _, cost in paths)
                assert report.maximum_emission_sum == max(cost for _, cost in paths)
                assert set(report.possible_next_outputs) == expected_values


@pytest.mark.parametrize("seed", (173488, 174388, 1768742, 4957342, 4875188))
@pytest.mark.validation
def test_real_trajectories_are_within_certified_temporal_ports(seed: int) -> None:
    edge = edge_from_digits(str(seed))
    assert edge in EDGE_STATES
    totals = dict.fromkeys(SCALAR_OBSERVERS, 0)
    source = seed
    for step in range(64):
        successor = _literal_step(source)
        ports = _literal_ports(source, successor)
        for pumped_observer in PUMPED_OBSERVERS:
            assert (
                pumped_border_word(edge, 64, pumped_observer).at(step)
                == (ports[pumped_observer])
            )
        for observer, value in ports.items():
            totals[observer] += value
            report = power_temporal_border(edge, step + 1, observer)
            assert report.minimum_emission_sum <= totals[observer]
            assert totals[observer] <= report.maximum_emission_sum
            next_outputs = power_temporal_border(
                edge, step, observer
            ).possible_next_outputs
            assert (value,) in next_outputs
        assert edge_from_digits(str(successor)) in EDGE_STATES
        source = successor


def test_same_present_gt_bank_requires_real_interior_carry() -> None:
    a, b = 1700042, 1700542
    assert edge_from_digits(str(a)) == edge_from_digits(str(b))
    for _ in range(2):
        a, b = _literal_step(a), _literal_step(b)
    # Two physical successors share the original *border*, but their
    # future GT-high word is already different. No guessed 2-cell reset
    # selector may erase the inward F5/threshold port.
    assert _literal_ports(a, _literal_step(a))["gt_high"] == 0
    assert _literal_ports(b, _literal_step(b))["gt_high"] == 2
    envelope = power_temporal_border((1, 7, 4, 2), 2, "gt_high")
    assert (0,) in envelope.possible_next_outputs
    assert (2,) in envelope.possible_next_outputs


def test_growth_carry_and_reflected_xor_are_pumped_exactly() -> None:
    for edge in EDGE_STATES:
        for depth in (0, 1, 2, 3, 4, 5, 15, 256, 10**30 + 3):
            for observer in ("growth", "carry_edge", "reflected_xor"):
                program = pumped_border_word(edge, depth, observer)
                envelope = power_temporal_border(edge, depth, observer)
                assert envelope.exact_sum == program.emission_sum
                assert program.steps == depth
                if depth:
                    assert program.at(depth - 1) == program.motif[(depth - 1) % 4]
    with pytest.raises(ValueError, match="conditional"):
        pumped_border_word((1, 7, 8, 8), 12, "gt_high")


def test_term_publishes_temporal_bank_without_endpoint(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbid_endpoint(_term: DoubleReverseTerm) -> None:
        raise AssertionError("temporal border demand constructed the endpoint")

    monkeypatch.setattr(DoubleReverseTerm, "prepare_endpoint", forbid_endpoint)
    with DoubleReverseTerm(196, 64) as term:
        prefix, envelopes = term.temporal_border_bank()
        rows = {row.observer: row for row in envelopes}
        assert prefix == 16
        assert rows["carry_edge"].steps == 48
        assert rows["carry_edge"].moore_classes == 4
        assert rows["carry_edge"].exact_sum == 384
        assert rows["reflected_xor"].exact_sum == 72
        assert rows["gt_high"].exact_sum is None
        assert term._image is None
        metrics = term.metrics()
        assert metrics["double_reverse_temporal_bank_moore_constructions"] == 6
        assert (
            metrics["double_reverse_temporal_bank_moore_transition_evaluations"] == 108
        )
        assert metrics["double_reverse_temporal_bank_moore_output_evaluations"] == 108
        assert metrics["double_reverse_temporal_bank_moore_state_visits"] > 0
        assert metrics["double_reverse_temporal_bank_moore_refinement_sweeps"] >= 6
        assert metrics["double_reverse_temporal_bank_moore_refinement_rounds"] > 0
        assert collect_ledger_metrics(term._ledger).resource_audit_complete == 1


def test_unverified_cylinder_cannot_be_powered() -> None:
    with pytest.raises(ValueError, match="certified"):
        power_temporal_border((9, 9, 9, 9), 20)
    with DoubleReverseTerm(0, 64) as term, pytest.raises(ValueError, match="certified"):
        term.temporal_border_bank()
