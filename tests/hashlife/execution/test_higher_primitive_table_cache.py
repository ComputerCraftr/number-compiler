"""Shared HashLife primitive-cache behavior across sequence families."""

from collections.abc import Callable

import pytest

from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


@pytest.mark.parametrize(
    ("term", "coordinate"),
    (
        (lambda: ReverseAddPoweredTerm(196, 32), 3),
        (lambda: PoweredCollatzTerm(27, 32), 0),
    ),
    ids=("reverse-add", "collatz"),
)
def test_query_eviction_does_not_replay_bounded_primitive_kernel(
    term: Callable[[], PoweredCollatzTerm | ReverseAddPoweredTerm],
    coordinate: int,
) -> None:
    powered = term()
    expected = powered.digit(coordinate)
    before = powered.metrics()
    powered._ledger.evict_query_memos()
    assert powered.digit(coordinate) == expected
    after = powered.metrics()
    assert (
        after.bounded_application_nonlinear_branch_evaluations
        == before.bounded_application_nonlinear_branch_evaluations
    )
    assert after.temporal_parent_compositions == before.temporal_parent_compositions
