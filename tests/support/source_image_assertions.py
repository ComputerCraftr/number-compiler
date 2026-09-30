"""Canonical work taxonomy assertions for source-image release evidence."""

from collections.abc import Mapping


def assert_physical_source_work(counters: Mapping[str, int]) -> None:
    assert_physical_publications(counters)
    # A checked 1→4→2 cycle may replace primitive/composite application work.
    assert (
        counters.get("source_image_composite_applications", 0)
        + counters.get("source_image_demanded_composite_applications", 0)
        + counters.get("source_image_primitive_applications", 0)
        + counters.get("collatz_physical_cycle_compressions", 0)
        > 0
    )


def assert_physical_publications(counters: Mapping[str, int]) -> None:
    assert counters.get("collatz_physical_action_publications", 0) > 0
    assert counters.get("source_image_publications", 0) > 0
    assert counters.get("source_image_projection_publications", 0) > 0


def assert_source_image_replay_stable(
    before: Mapping[str, int], after: Mapping[str, int]
) -> None:
    """A repeated query reuses both image and projection publications."""
    for counter in (
        "source_image_publications",
        "source_image_projection_publications",
    ):
        assert before.get(counter, 0) > 0
        assert after.get(counter, 0) == before[counter]
    assert after.get("higher_action_continuation_requests", 0) == 0
    assert after.get("higher_concrete_operation_evaluations", 0) == 0
