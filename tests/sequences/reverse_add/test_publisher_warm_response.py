"""Bounded warm-response evidence for the canonical 196 image runtime."""

from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def test_public_196_point_reuses_authenticated_scalar_without_replaying_image() -> None:
    term = ReverseAddPoweredTerm(196, 8)
    position = term.maximum_width // 3
    expected = term.digit(position)
    before = dict(term._ledger.counters)
    assert term.digit(position) == expected
    after = term._ledger.counters

    assert (
        after.get("source_image_projection_requests", 0)
        - before.get("source_image_projection_requests", 0)
        == 0
    )
    assert (
        after.get("source_image_projection_hits", 0)
        - before.get("source_image_projection_hits", 0)
        == 1
    )
    assert (
        after.get("source_image_projection_evaluations", 0)
        - before.get("source_image_projection_evaluations", 0)
        == 0
    )
    for counter in (
        "higher_action_continuation_requests",
        "higher_concrete_operation_evaluations",
        "reverse_source_bound_image_first_demands",
        "reverse_source_bound_publisher_point_observations",
    ):
        assert after.get(counter, 0) - before.get(counter, 0) == 0


def test_cold_196_point_reports_the_canonical_powered_image_cutover() -> None:
    term = ReverseAddPoweredTerm(196, 8)
    term.digit(0)
    metrics = term.metrics()
    behavior = term.behavior_metrics()

    assert metrics.higher_action_continuation_requests == 0
    assert metrics.higher_concrete_operation_evaluations == 0
    assert metrics.primitive_transition_evaluations > 0
    assert metrics.powered_absorption_successes > 0
    assert behavior.bounded_temporal_runtime_cutover_complete == 1
    assert behavior.bounded_temporal_runtime_cutover_blocker == ""
