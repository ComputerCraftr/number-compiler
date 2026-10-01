"""Reverse/add primitive work remains bounded beneath temporal diamonds."""

import pytest

from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


@pytest.mark.validation  # Cold N=32/64 primitive-work doubling envelope.
def test_reverse_primitive_work_does_not_follow_temporal_square_area() -> None:
    counts = []
    for steps in (32, 64):
        term = ReverseAddPoweredTerm(196, steps)
        term.digit(0)
        counts.append(term.metrics().bounded_application_nonlinear_branch_evaluations)
    # A new temporal square may expose a few new primitive truth-table cells;
    # it cannot replay every occurrence in the recursively composed state.
    assert counts[1] <= counts[0] + 160


@pytest.mark.validation  # N=64 production temporal-prefix poison/counter gate.
def test_reverse_parent_observation_does_not_replay_temporal_prefixes() -> None:
    """A published temporal parent is consumed as one composed action.

    This counter used to equal ``steps - 1`` because the coordinate observer
    expanded both temporal children after the recursive image executor had
    already published the parent diamond.
    """
    term = ReverseAddPoweredTerm(196, 64)
    assert term.digit(0) == 8
    counters = term.metrics().resource_work_counters
    assert counters.get("reverse_temporal_prefix_image_observations", 0) == 0
    assert counters.get("reverse_temporal_published_prefix_uses", 0) == 0
