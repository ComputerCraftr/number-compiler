"""Reverse/add source-image output and work accounting regressions."""

import pytest

from number_compiler.arithmetic.carry.event_memory import event_memory_horizon
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from tests.support.source_image_assertions import assert_source_image_behavior


@pytest.mark.validation  # N=64 exact reverse output and source-image accounting.
def test_reverse_source_image_reports_exact_output_and_publications() -> None:
    expected = 196
    for _ in range(64):
        expected += int(str(expected)[::-1])
    term = ReverseAddPoweredTerm(196, 64)
    assert term.digits() == tuple(map(int, reversed(str(expected))))
    _, after = assert_source_image_behavior(term)
    assert after.temporal_quotient_family == "reverse-add-source-cylinder"
    assert event_memory_horizon(10) == 20
    assert after.temporal_quotient_state_class_bound == 0
    assert after.temporal_quotient_action_class_bound == 0
    assert after.field_action_nodes == 0
    assert after.higher_concrete_operation_evaluations == 0
