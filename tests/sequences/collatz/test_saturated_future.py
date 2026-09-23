"""Independent finite checks of admitted saturated Collatz safety actions."""

from __future__ import annotations

from dataclasses import fields

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.sequences.collatz.radix64_transducer import compose_radix64_events
from number_compiler.sequences.collatz.saturated_future import (
    SourceFreeSaturatedCollatzProgram,
    SaturatedCollatzOccurrence,
    compose_occurrences,
    from_published_prefix,
    publish_valuation_block,
    saturated_dyadic_power_from_source,
)
from number_compiler.sequences.collatz.source_publisher import CollatzSourcePublisher


def _literal(source: int, events: int) -> tuple[int, bool]:
    value = source
    below = False
    for _ in range(events):
        numerator = 3 * value + 1
        q = (numerator & -numerator).bit_length() - 1
        value = numerator >> q
        below |= value < source
    return value, below


@pytest.mark.parametrize("source", [1, 3, 7, 27, 31, 59, 97, 127])
@pytest.mark.parametrize("events", [1, 2, 3, 4, 6, 8, 12])
def test_source_free_selector_publishes_exact_finite_action(
    source: int, events: int
) -> None:
    result = SourceFreeSaturatedCollatzProgram(events).bind(source)
    endpoint, below = _literal(source, events)
    occurrence = result.occurrence
    assert occurrence.apply_exact(source) == endpoint
    assert occurrence.descends(source) is below
    assert result.compositions == result.leaves - 1
    assert {field.name for field in fields(result)} == {
        "occurrence",
        "leaves",
        "compositions",
    }
    assert {field.name for field in fields(occurrence)} == {
        "action",
        "domain",
        "events",
    }


def test_source_free_power_is_only_a_descriptor() -> None:
    atom = SourceFreeSaturatedCollatzProgram(6)
    assert atom.square().square().events == 24
    assert atom.power(8).events == 48
    assert atom.power(8).operator_nodes == 1
    assert atom.power(8).description_bits == 6


def test_safety_and_source_fiber_do_not_evaluate_endpoint(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    occurrence = SourceFreeSaturatedCollatzProgram(8).bind(27).occurrence
    expected_descent = occurrence.descends(27)
    expected_fiber = occurrence.source_high_fiber(27)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("safety-only demand evaluated the endpoint")

    monkeypatch.setattr(SaturatedCollatzOccurrence, "apply_exact", forbidden)
    assert occurrence.descends(27) is expected_descent
    assert occurrence.source_high_fiber(27) == expected_fiber
    with pytest.raises(ValueError, match="admitted cylinder"):
        occurrence.descends(29)


def test_temporal_composition_preserves_full_threshold_and_domain() -> None:
    first = publish_valuation_block((1, 2))
    second = publish_valuation_block((1, 1))
    combined = compose_occurrences(first, second)
    direct = publish_valuation_block((1, 2, 1, 1))
    assert combined.canonical_key == direct.canonical_key
    assert combined.events == 4


def test_equal_f5_views_do_not_authorize_a_shared_future_source() -> None:
    """The complete occurrence transports its source, not an observer class.

    Sources 67 and 75 have the same two-cell carry/F5 observation and the
    same first accelerated gap. Their next Hensel gaps are 4 and 2, so a
    temporal square keyed only by the finite observer would publish the
    wrong right half for one of them.
    """
    from number_compiler.arithmetic.carry.collatz_f5_quotient import (
        radix64_f5_class,
    )

    left, right = 67, 75
    assert (
        radix64_f5_class(left % 64),
        radix64_f5_class(left // 64),
    ) == (
        radix64_f5_class(right % 64),
        radix64_f5_class(right // 64),
    )
    first = publish_valuation_block((1,))
    assert first.domain.contains(left) and first.domain.contains(right)
    assert (first.apply_exact(left), first.apply_exact(right)) == (101, 113)

    left_two = SourceFreeSaturatedCollatzProgram(2).bind(left).occurrence
    right_two = SourceFreeSaturatedCollatzProgram(2).bind(right).occurrence
    assert left_two.domain.contains(left) and not left_two.domain.contains(right)
    assert right_two.domain.contains(right) and not right_two.domain.contains(left)
    assert (left_two.apply_exact(left), right_two.apply_exact(right)) == (19, 85)


@pytest.mark.parametrize("source", [3, 7, 27, 97])
def test_cli_source_prefix_reuses_admitted_event_root(
    source: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    publisher = CollatzSourcePublisher(source, 8, max_events=8, max_digits=128)
    published = publisher.publish()

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("saturated demand must not rediscover source branches")

    monkeypatch.setattr(
        "number_compiler.sequences.collatz.saturated_future.compose_radix64_events",
        forbidden,
    )
    result = from_published_prefix(published)
    assert result is not None
    endpoint, below = _literal(source, published.discovered_events)
    assert result.occurrence.apply_exact(source) == endpoint
    assert result.occurrence.descends(source) is below
    assert (
        publisher.ledger.counters["collatz_saturated_event_reads"]
        == published.discovered_events
    )


def test_empty_published_prefix_has_no_first_passage() -> None:
    published = CollatzSourcePublisher(1, 8, max_events=8, max_digits=64).publish()
    assert from_published_prefix(published) is None


def test_output_free_selector_retains_no_endpoint_digit_tuple() -> None:
    digits = (27,)
    valuations: list[int] = []
    result = compose_radix64_events(
        digits, 6, valuation_sink=valuations.append, collect_output=False
    )
    retained = compose_radix64_events(digits, 6)
    assert result.target_digits == ()
    assert result.exit_frame == retained.exit_frame
    assert len(valuations) == 6
    assert result.valuation == sum(valuations)


def test_publication_precision_is_refused_before_huge_shift() -> None:
    with pytest.raises(BlockContextBudgetExceeded, match="Hensel precision"):
        publish_valuation_block((20000,))
    with pytest.raises(BlockContextBudgetExceeded, match="64 events"):
        publish_valuation_block(1 for _ in range(1000000))


def test_temporary_publication_reservation_releases_after_success_and_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    publisher = CollatzSourcePublisher(27, 6, max_events=6, max_digits=128)
    published = publisher.publish()
    before = publisher.ledger.nodes, publisher.ledger.entries
    from_published_prefix(published)
    assert (publisher.ledger.nodes, publisher.ledger.entries) == before

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("forced publication failure")

    monkeypatch.setattr(
        "number_compiler.sequences.collatz.saturated_future.publish_valuation_block",
        forbidden,
    )
    with pytest.raises(AssertionError, match="forced publication failure"):
        from_published_prefix(published)
    assert (publisher.ledger.nodes, publisher.ledger.entries) == before
    assert publisher.ledger.counters["collatz_saturated_failed_constructions"] == 1


def test_source_free_budget_refuses_before_stage_construction(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("selector stage constructed before budget refusal")

    monkeypatch.setattr(
        "number_compiler.sequences.collatz.radix64_transducer.Radix64CollatzStage",
        forbidden,
    )
    with pytest.raises(BlockContextBudgetExceeded, match="selector event budget"):
        SourceFreeSaturatedCollatzProgram(4097).bind(27, selector_event_budget=4097)
    with pytest.raises(BlockContextBudgetExceeded, match="selector event budget"):
        saturated_dyadic_power_from_source(27, 200000)


def test_failed_temporary_reservation_is_charged() -> None:
    publisher = CollatzSourcePublisher(27, 6, max_events=6, max_digits=128)
    published = publisher.publish()
    ledger = publisher.ledger
    before = ledger.nodes, ledger.entries
    ledger.max_nodes = ledger.nodes
    with pytest.raises(BlockContextBudgetExceeded, match="node budget"):
        from_published_prefix(published)
    assert (ledger.nodes, ledger.entries) == before
    assert ledger.counters["collatz_saturated_attempts"] == 1
    assert ledger.counters["collatz_saturated_failed_constructions"] == 1
