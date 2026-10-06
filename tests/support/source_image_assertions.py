"""Canonical work taxonomy assertions for source-image release evidence."""

from collections.abc import Iterator, Mapping
from typing import Protocol

from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.metric_records import HashLifeBehaviorMetrics
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

SourceImageTerm = PoweredCollatzTerm | ReverseAddPoweredTerm


class DigitObservers(Protocol):
    def iter_digits(self) -> Iterator[int]: ...

    def width(self) -> int: ...

    def digit(self, position: int) -> int: ...


def assert_exact_digit_observers(
    result: DigitObservers, expected: tuple[int, ...]
) -> None:
    """Check streaming, authenticated extent and every point against one oracle."""
    assert tuple(result.iter_digits()) == expected
    assert result.width() == len(expected)
    assert tuple(result.digit(i) for i in range(len(expected))) == expected


def assert_source_image_runtime_bridge(term: SourceImageTerm, family: str) -> None:
    """Check the shared source-image bridge and its family-owned counters."""
    first = term.digit(0)
    metrics = term.metrics()
    behavior = term.behavior_metrics()
    audit = collect_ledger_metrics(term._ledger)
    assert metrics.metrics_schema_version == 8
    counters = metrics.resource_work_counters
    if isinstance(term, PoweredCollatzTerm):
        assert metrics.temporal_parent_requests == 0
        assert metrics.temporal_parent_compositions == 0
        assert metrics.tile_temporal_action_publications == 0
        assert metrics.field_action_nodes == 0
        assert_collatz_source_work(counters)
        assert term._power is None
    else:
        assert counters.get("source_image_publications", 0) > 0
        assert counters.get("source_image_projection_publications", 0) > 0
    assert metrics.whole_word_sweeps == metrics.whole_word_symbol_visits == 0
    assert metrics.proof_machine_applications == 0
    assert metrics.sequential_generation_advances == 0
    assert metrics.exact_endpoint_nodes == 0
    assert audit.forbidden_future_payloads == 0
    assert audit.representation_boundary_complete == 1
    assert behavior.temporal_quotient_family == family
    assert behavior.temporal_quotient_state_class_bound == 0
    assert behavior.temporal_quotient_action_class_bound == 0
    assert behavior.seed_application_temporal_action_nodes > 0
    before = dict(term._ledger.counters)
    assert term.digit(0) == first
    after = term._ledger.counters
    assert counters.get("source_image_publications", 0) > 0
    assert counters.get("source_image_projection_publications", 0) > 0
    for counter in (
        "source_image_publications",
        "source_image_projection_publications",
    ):
        assert after.get(counter, 0) == before.get(counter, 0)
    assert audit.resource_audit_complete == 1
    assert metrics.resource_accounting_mismatch == 0


def assert_source_image_behavior(
    term: SourceImageTerm,
) -> tuple[HashLifeBehaviorMetrics, HashLifeBehaviorMetrics]:
    """Exercise and audit the family-owned source image after a cold snapshot."""
    assert not hasattr(term, "_diamond_runtime")
    before = term.behavior_metrics()
    before_audit = collect_ledger_metrics(term._ledger)
    collatz = isinstance(term, PoweredCollatzTerm)
    family = "collatz-dyadic-source-image" if collatz else "reverse-add-source-cylinder"
    assert before.field_action_nodes == 0
    assert before.temporal_quotient_family == family
    assert before_audit.resource_audit_complete == 1
    assert before.resource_accounting_mismatch == 0
    assert before.unquotiented_recursive_application_description_nodes == 0
    assert before_audit.representation_boundary_complete == 1
    assert before.seed_payload_tile_nodes == 0
    term.digit(0)
    after = term.behavior_metrics()
    runtime = term.metrics()
    after_audit = collect_ledger_metrics(term._ledger)
    assert after_audit.resource_audit_complete == 1
    assert after.resource_accounting_mismatch == 0
    assert after.field_action_nodes == 0
    assert after.temporal_quotient_family == family
    assert (
        after_audit.forbidden_future_payloads
        == after_audit.retained_unbounded_future_integers
        == 0
    )
    assert after.unquotiented_recursive_application_description_nodes == 0
    counters = runtime.resource_work_counters
    if collatz:
        assert isinstance(term, PoweredCollatzTerm)
        assert after.seed_application_temporal_action_nodes > 0
        assert term._power is None
        assert_collatz_source_publications(counters)
        assert runtime.temporal_parent_requests == 0
        assert runtime.temporal_parent_compositions == 0
    else:
        assert after.seed_application_temporal_action_nodes > 0
        assert counters.get("source_image_publications", 0) > 0
        assert counters.get("source_image_projection_publications", 0) > 0
    assert runtime.sequential_generation_advances == 0
    assert runtime.higher_concrete_operation_evaluations == 0
    assert runtime.higher_action_continuation_requests == 0
    assert runtime.temporal_parent_requests == (
        runtime.temporal_parent_early_hits + runtime.temporal_parent_compositions
    )
    return before, after


def assert_collatz_source_work(counters: Mapping[str, int]) -> None:
    assert_collatz_source_publications(counters)
    # A checked 1→4→2 cycle may replace primitive/composite application work.
    assert (
        counters.get("source_image_composite_applications", 0)
        + counters.get("source_image_demanded_composite_applications", 0)
        + counters.get("source_image_primitive_applications", 0)
        + counters.get("collatz_physical_cycle_compressions", 0)
        > 0
    )


def assert_collatz_source_publications(counters: Mapping[str, int]) -> None:
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
