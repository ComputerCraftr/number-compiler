"""Output-fiber minimization and Boolean source projection contracts."""

from collections.abc import Hashable, Iterable, Sequence
from typing import cast

import pytest

from number_compiler.projection.output_quotient import (
    BinaryOutputCoordinate,
    SpecialOutputMode,
    audit_binary_source_factor,
    canonical_partition_labels,
    minimize_projection_machine,
    output_fiber_quotient,
)


def test_output_fibers_are_minimal_for_one_shot_projection_but_not_assumed_temporal_state() -> (
    None
):
    quotient = output_fiber_quotient((3, 3, 7, 3, 7))
    assert quotient.state_count == 2
    assert quotient.fibers == ((0, 1, 3), (2, 4))

    # State 0 and 1 emit the same value now, but their successors emit different
    # values.  Successor refinement must split them before powering.
    machine = minimize_projection_machine((1, 1, 1, 0), (2, 3, 2, 3))
    assert machine.initial_state_count == 2
    assert machine.state_count == 3
    assert machine.refinements == 1
    assert not machine.output_fibers_successor_closed


def test_partition_labels_are_stable_for_first_seen_signatures() -> None:
    assert canonical_partition_labels(("same", ("nested", 1), "same")) == (
        0,
        1,
        0,
    )
    labels: dict[Hashable, int] = {"first": 0}
    assert canonical_partition_labels(("next", "first", "next"), labels=labels) == (
        1,
        0,
        1,
    )
    assert labels == {"first": 0, "next": 1}


def test_boolean_output_coordinate_requires_factor_through_proof_and_has_three_modes() -> (
    None
):
    separating = audit_binary_source_factor((False, False, True, True), (3, 3, 7, 7))
    coordinate = BinaryOutputCoordinate.from_factor_audit(separating)
    assert coordinate.mode is SpecialOutputMode.GUARDED
    assert coordinate.derivative == 4
    assert coordinate.quotient_states == 2
    assert coordinate.recover_source_bit(3) is False
    assert coordinate.recover_source_bit(7) is True
    assert coordinate.resolve(True).mode is SpecialOutputMode.RESOLVED
    assert coordinate.resolve(True).value == 7
    with pytest.raises(ValueError, match="no concrete value"):
        _ = coordinate.value

    collapsed = BinaryOutputCoordinate.from_factor_audit(
        audit_binary_source_factor((False, True), (5, 5))
    )
    assert collapsed.mode is SpecialOutputMode.CONCRETE
    assert collapsed.quotient_states == 1
    assert collapsed.derivative == 0
    assert collapsed.value == 5

    insufficient = audit_binary_source_factor((False, False, True), (3, 4, 7))
    assert not insufficient.factors_through_source_bit
    with pytest.raises(ValueError, match="not proved to factor"):
        BinaryOutputCoordinate.from_factor_audit(insufficient)

    # Keep arbitrary CRT idempotents out of the global Boolean sheet API.
    with pytest.raises(TypeError, match="literal bool"):
        audit_binary_source_factor(
            cast("Sequence[bool] | Iterable[bool]", (False, 6)), (3, 7)
        )
    with pytest.raises(TypeError, match="failure_bit"):
        from number_compiler.projection.output_quotient import SpecialSourceGuard

        SpecialSourceGuard(
            "mersenne", 11, cast("bool | None", 6), "invalid-crt-as-boolean"
        )
    with pytest.raises(TypeError, match="resolved_bit"):
        BinaryOutputCoordinate(3, 7, cast("bool | None", 6))
    with pytest.raises(TypeError, match="source_bit"):
        coordinate.resolve(cast("bool", 6))
