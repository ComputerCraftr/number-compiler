from __future__ import annotations

from typing import Literal

import pytest

from devtools.verification.comma_semantic_quotients import (
    CommaFutureGraph,
    CommaFutureMooreQuotient,
    CommaPortMooreQuotient,
    boundary_production_port,
    build_future_graph,
    build_future_production_macro_quotient,
    build_future_temporal_quotient,
    build_q15_nonzero_ports,
    build_q19_production_ports,
    future_homogeneous_run_audit,
    future_rank_refinement_audit,
)
from number_compiler.arithmetic.carry.carry_monoid import apply_carry_fn
from number_compiler.arithmetic.formula.decimal_pair_coordinates import (
    decimal_pair_carry_action,
)
from number_compiler.sequences.comma.arithmetic import (
    comma_port_next,
    comma_port_previous,
    cycle_transfer,
)
from number_compiler.sequences.comma.boundary_chart import PERIOD, chart_moves
from number_compiler.sequences.comma.boundary_quotient import BoundaryState


@pytest.fixture(scope="module")
def future_graph() -> CommaFutureGraph:
    return build_future_graph()


@pytest.fixture(scope="module")
def temporal_quotient(future_graph: CommaFutureGraph) -> CommaFutureMooreQuotient:
    return build_future_temporal_quotient(future_graph)


@pytest.fixture(scope="module")
def q15() -> CommaPortMooreQuotient:
    return build_q15_nonzero_ports()


@pytest.fixture(scope="module")
def q19() -> CommaPortMooreQuotient:
    return build_q19_production_ports()


@pytest.mark.parametrize("leading", range(1, 10))
@pytest.mark.parametrize("digit", range(10))
def test_port_arithmetic_exactly_punctures_zero_once(leading: int, digit: int) -> None:
    previous = (digit + 10 - leading) % 10
    assert comma_port_previous(leading, digit) == previous
    expected_next = previous if previous else (-leading) % 10
    assert comma_port_next(leading, digit) == expected_next


@pytest.mark.parametrize(("leading", "digit"), ((True, 2), (1, False), (0, 2), (1, 10)))
def test_port_arithmetic_rejects_noncanonical_inputs(leading: int, digit: int) -> None:
    with pytest.raises(ValueError, match="invalid comma port"):
        comma_port_previous(leading, digit)


def test_q15_and_q19_are_fixed_point_observers_with_distinct_zero_scope(
    q15: CommaPortMooreQuotient, q19: CommaPortMooreQuotient
) -> None:
    assert len(q15.ports) == 81
    assert q15.classes == q15.fixed_classes == 15
    assert len(q19.ports) == 90
    assert q19.classes == q19.fixed_classes == 19
    for leading in range(1, 10):
        assert q19.class_for_port(leading, 0) >= 0
        with pytest.raises(ValueError, match="outside this Moore alphabet"):
            q15.class_for_port(leading, 0)
    # A shared finite class is not a weighted transfer: these source ports
    # agree under Q19 while their exact radial displacements differ.
    assert q19.class_for_port(1, 0) == q19.class_for_port(3, 0)
    assert cycle_transfer(1, 0).displacement != cycle_transfer(3, 0).displacement


def test_complement_reset_germ_is_conjugacy_not_fixed_port_equality() -> None:
    # These are real f=1 ports: (d,p)=(1,0) and (9,8). Their
    # complement-normalized defects agree, but their carry functions do not.
    # The full proposal retains occurrence transport; this tests its necessity,
    # not a counterexample to a complete transported action.
    sums = tuple(d + comma_port_previous(1, d) for d in (1, 9))
    assert sums == (1, 17)
    assert (sums[0] - 9) % 5 == -(sums[1] - 9) % 5 == 2
    lower, upper = (decimal_pair_carry_action(symbol) for symbol in sums)
    for incoming in (0, 1):
        assert apply_carry_fn(lower, incoming) != apply_carry_fn(upper, incoming)
        assert apply_carry_fn(upper, 1 - incoming) == (
            1 - apply_carry_fn(lower, incoming)
        )


def test_fork_q15_sharing_requires_occurrence_rebase_for_q19_timing(
    q15: CommaPortMooreQuotient, q19: CommaPortMooreQuotient
) -> None:
    # Use the production N-cylinder ports for exact fork coefficients 3 and 6.
    # Q15 shares the puncture response; the receiving coefficient must still
    # recover the distinct physical periods. This is not a failure of a
    # complete action which retains that coefficient outside its semantic ID.
    left, right = (
        boundary_production_port(BoundaryState("N", coefficient, 10))
        for coefficient in (3, 6)
    )
    assert q15.class_for_port(*left) == q15.class_for_port(*right)
    assert q19.class_for_port(*left) != q19.class_for_port(*right)
    assert cycle_transfer(*left).period != cycle_transfer(*right).period


def _terminal(
    kind: Literal["N", "Z"], a: int, residue: int, *, grouped: bool
) -> tuple[str, int | None, int]:
    for chart, move in chart_moves(kind, a, residue, grouped_near=grouped):
        if move.next_chart is None:
            return (
                "landmine" if move.fork_a is None else "fork",
                move.fork_a,
                chart.delta,
            )
    raise AssertionError("comma chart has no terminal event")


@pytest.mark.validation
def test_future_graph_grouped_arithmetic_matches_literal_chart_for_every_state(
    future_graph: CommaFutureGraph,
) -> None:
    assert len(future_graph.states) == 2 * 8 * PERIOD == 14_784
    for state in future_graph.states:
        assert _terminal(
            state.kind, state.a, state.exponent_residue, grouped=True
        ) == _terminal(state.kind, state.a, state.exponent_residue, grouped=False)


@pytest.mark.validation
def test_future_temporal_and_zero_inclusive_spatial_quotients_are_fixed(
    future_graph: CommaFutureGraph,
    temporal_quotient: CommaFutureMooreQuotient,
) -> None:
    assert temporal_quotient.raw_states == 14_784
    assert temporal_quotient.classes == temporal_quotient.fixed_classes == 3_279

    production = build_future_production_macro_quotient(future_graph)
    assert production.raw_states == 14_784
    assert production.classes == production.fixed_classes == 4_986
    assert boundary_production_port(BoundaryState("N", 5, 0)) == (4, 9)
    assert boundary_production_port(BoundaryState("Z", 5, 0)) == (5, 0)


@pytest.mark.validation
def test_moore_fibers_preserve_ranks_and_zero_inclusive_survivor_cycle(
    future_graph: CommaFutureGraph,
    temporal_quotient: CommaFutureMooreQuotient,
) -> None:
    audit = future_rank_refinement_audit(future_graph, temporal_quotient)
    assert audit.losing_states == 14_470
    assert audit.survivor_states == 314
    assert audit.maximum_rank == 136
    assert audit.temporal_classes == 3_279
    assert audit.mixed_rank_classes == 0
    assert audit.cycle_length == 314
    assert audit.cycle_exponent_gain == 924
    assert audit.zero_symbols == 171
    assert audit.one_symbols == 143
    assert audit.cyclic_runs == 140
    assert audit.all_five_bit_words


@pytest.mark.validation
def test_future_homogeneous_run_actions_retain_zero_until_saturation(
    temporal_quotient: CommaFutureMooreQuotient,
) -> None:
    audit = future_homogeneous_run_audit(temporal_quotient)
    assert audit.actions == 31
    assert audit.zero_saturates_at == 13
    assert audit.one_saturates_at == 18
    assert audit.common_dead_action
