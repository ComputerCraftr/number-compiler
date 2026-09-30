"""Adversarial checks for the source-bound Collatz prefix publisher."""

from __future__ import annotations

from dataclasses import replace
from typing import Never

import pytest

from number_compiler.arithmetic.automata.program_word import CanonicalWord
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.physical_support_payload_audit import (
    audit_physical_support_payloads,
)
from number_compiler.resources.stores import LedgerList
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.collatz.clock_observers import CollatzClockObservers
from number_compiler.sequences.collatz.germ_cache import CollatzGermTransitionCache
from number_compiler.sequences.collatz.source_publisher import CollatzSourcePublisher


def test_canonical_event_validation_rejects_foreign_child_with_equal_id() -> None:
    from number_compiler.sequences.collatz.power import CollatzEventArena

    arena, foreign = CollatzEventArena(), CollatzEventArena()
    first, second = arena.event(1), arena.event(2)
    root = arena.concat(first, second)
    impostor = foreign.event(1)
    assert first.node_id == impostor.node_id
    object.__setattr__(root, "left", impostor)
    with pytest.raises(ValueError, match="another arena"):
        arena.validate_node(root)


def test_ledger_cache_cannot_enable_unaccounted_power_stores() -> None:
    from number_compiler.resources.ledger import ResourceLedger

    with pytest.raises(ValueError, match="allow_power=False"):
        CollatzGermTransitionCache(ledger=ResourceLedger())


def _accelerated_reference(seed: int, events: int) -> tuple[int, tuple[int, ...]]:
    value = seed
    valuations: list[int] = []
    while len(valuations) < events and value != 1:
        numerator = 3 * value + 1
        valuation = (numerator & -numerator).bit_length() - 1
        valuations.append(valuation)
        value = numerator >> valuation
    return value, tuple(valuations)


@pytest.mark.parametrize("seed", (1, 3, 5, 27, 85))
@pytest.mark.parametrize("events", (0, 1, 3, 8))
def test_published_event_and_physical_roots_are_one_source_action(
    seed: int, events: int
) -> None:
    publisher = CollatzSourcePublisher(seed, events, max_events=8, max_digits=64)
    published = publisher.publish()
    target, valuations = _accelerated_reference(seed, events)
    assert publisher.publish() is published
    assert published.discovered_events == len(valuations)
    assert published.reached_one is (target == 1)
    assert publisher.events.apply_exact(published.event_root, seed) == target
    expected_word = tuple(
        parity
        for valuation in valuations
        for parity in (True, *(False for _ in range(valuation)))
    )
    assert published.physical_support.ticks == len(expected_word)
    assert (
        tuple(
            published.physical_support.tick(index)
            for index in range(published.physical_support.ticks)
        )
        == expected_word
    )
    observer = CollatzClockObservers(publisher.events)
    assert observer.clock(published.event_root).physical_ticks == len(expected_word)
    transfer = observer.modular(published.event_root, 257)
    assert (transfer.upper * seed + transfer.offset) % 257 == (
        transfer.lower * target
    ) % 257


def test_event_zero_does_not_discover_a_source_transition(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    publisher = CollatzSourcePublisher(27, 0, max_events=0, max_digits=64)

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("zero events attempted source discovery")

    monkeypatch.setattr(CollatzGermTransitionCache, "advance", forbidden)
    published = publisher.publish()
    assert published.discovered_events == 0
    assert published.physical_support.ticks == 0
    assert published.event_root.effect.events == 0


@pytest.mark.parametrize("seed", (2, 8, 16))
def test_even_seed_remains_a_physical_tick_source(seed: int) -> None:
    with pytest.raises(ValueError, match="odd seed"):
        CollatzSourcePublisher(seed, 1, max_events=1, max_digits=64)
    term = PoweredCollatzTerm(seed, 1)
    workspace = term._source_image()
    summary = workspace.summary()
    assert summary.width == 1 and summary.odd_steps == 0
    assert tuple(workspace.segments()) == ((0, 1, 0),)


def test_source_authority_rejects_foreign_and_forged_publications() -> None:
    first = CollatzSourcePublisher(27, 3, max_events=8, max_digits=64)
    second = CollatzSourcePublisher(27, 3, max_events=8, max_digits=64)
    published = first.publish()
    second.publish()
    with pytest.raises(ValueError, match="another source publisher"):
        second.validate(published)
    forged = replace(published, discovered_events=2)
    with pytest.raises(ValueError, match="not the published"):
        first.validate(forged)


def test_issued_snapshot_rejects_same_arena_substitutions_and_field_mutation() -> None:
    publisher = CollatzSourcePublisher(27, 3, max_events=8, max_digits=64)
    published = publisher.publish()
    original_root = published.event_root
    alternate = publisher.events.from_valuations((2, 1, 1))
    assert alternate.effect == original_root.effect
    object.__setattr__(published, "event_root", alternate)
    with pytest.raises(ValueError, match="issued source authority"):
        published.validate()
    object.__setattr__(published, "event_root", original_root)

    original_target = published.target
    object.__setattr__(
        published, "target", publisher.transitions.advance(original_target).target
    )
    with pytest.raises(ValueError, match="issued source authority"):
        published.validate()
    object.__setattr__(published, "target", original_target)

    for name, value in (
        ("reached_one", not published.reached_one),
        ("discovery_digit_work", published.discovery_digit_work + 1),
        (
            "admission_digit_comparisons",
            published.admission_digit_comparisons + 1,
        ),
    ):
        original = getattr(published, name)
        object.__setattr__(published, name, value)
        with pytest.raises(ValueError, match="issued source authority"):
            published.validate()
        object.__setattr__(published, name, original)
    published.validate()


def test_event_and_transition_retention_share_request_caps() -> None:
    publisher = CollatzSourcePublisher(27, 3, max_events=8, max_digits=64)
    published = publisher.publish()
    inventory = publisher.ledger.inventory()
    assert inventory and all(row.accounting_delta == 0 for row in inventory)
    assert any(
        row.name.startswith("collatz-event-") and row.name.endswith("-nodes")
        for row in inventory
    )
    assert any(
        row.name.startswith("collatz-germ-") and row.name.endswith("-canonical-states")
        for row in inventory
    )
    publisher.ledger.tighten_limits(publisher.ledger.nodes, publisher.ledger.entries)
    event_sizes = (
        publisher.events.node_count,
        len(publisher.events._by_key),
        len(publisher.events._events),
    )
    with pytest.raises(BlockContextBudgetExceeded, match="budget exceeded"):
        publisher.events.event(97)
    assert event_sizes == (
        publisher.events.node_count,
        len(publisher.events._by_key),
        len(publisher.events._events),
    )
    before_states = (
        publisher.transitions.raw_state_count,
        publisher.transitions.canonical_state_count,
    )
    with pytest.raises(BlockContextBudgetExceeded, match="budget exceeded"):
        publisher.transitions.advance(published.target)
    assert before_states == (
        publisher.transitions.raw_state_count,
        publisher.transitions.canonical_state_count,
    )


def test_publisher_does_not_call_the_retired_digit_successor(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.collatz import raw_field

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("publisher replayed successor digit words")

    monkeypatch.setattr(
        raw_field, "accelerated_collatz_sentinel_step_digits", forbidden
    )
    published = CollatzSourcePublisher(27, 8, max_events=8, max_digits=64).publish()
    assert published.discovered_events == 8
    assert published.discovery_digit_work > 0
    retained = published.owner.separately_retained
    assert retained["collatz_event_arena_nodes"] > 0
    assert retained["collatz_transition_canonical_states"] > 0
    assert not audit_physical_support_payloads(published.owner.ledger).invalid
    assert all(
        row.entries == row.observed_entries
        for row in published.owner.ledger.inventory()
    )


def test_symbolic_width_admission_matches_exact_bounded_endpoints() -> None:
    from number_compiler.arithmetic.automata.program_word import from_values
    from number_compiler.arithmetic.fields.radix import digits_lsd
    from number_compiler.sequences.collatz.frame import CollatzAffineSuffixGerm
    from number_compiler.sequences.collatz.germ_cache import CollatzGermTransitionCache

    for seed in range(1, 128, 2):
        germ = CollatzAffineSuffixGerm.from_word(from_values(digits_lsd(seed, 4)))
        value = seed
        cache = CollatzGermTransitionCache()
        for _ in range(8):
            width, comparisons = CollatzSourcePublisher._germ_radix4_width(germ)
            assert width == len(tuple(digits_lsd(value, 4)))
            assert comparisons >= 0
            for boundary in (max(1, width - 1), width, width + 1):
                fits, _ = CollatzSourcePublisher._germ_fits_digits(germ, boundary)
                assert fits is (len(tuple(digits_lsd(value, 4))) <= boundary)
            advance = cache.advance(germ)
            numerator = 3 * value + 1
            valuation = (numerator & -numerator).bit_length() - 1
            value = numerator >> valuation
            germ = advance.target


@pytest.mark.parametrize(
    "runs",
    (
        ((0, 1),),
        ((3, 1), (0, 2), (2, 1)),
        ((1, 5), (2, 3), (0, 4), (3, 2)),
    ),
)
def test_reverse_run_comparison_matches_bounded_integer_reference(
    runs: tuple[tuple[int, int], ...],
) -> None:
    from number_compiler.arithmetic.automata.program_word import from_runs
    from number_compiler.resources.ledger import ResourceLedger

    word = from_runs(runs)
    digits = tuple(symbol for symbol, count in runs for _ in range(count))
    value = sum(symbol << (2 * position) for position, symbol in enumerate(digits))
    ledger = ResourceLedger()
    frontier_owner = ledger.register("test-word-frontier", "runtime_query_workspace")
    frontier: LedgerList[tuple[CanonicalWord, int, int]] = ledger.make_list(
        frontier_owner, append_only=False
    )
    boundaries = (
        0,
        max(0, value - 1),
        value,
        value + 1,
        (1 << (2 * len(digits))) - 1,
    )
    for boundary in boundaries:
        observed, comparisons = CollatzSourcePublisher._word_leq_integer(
            word,
            boundary,
            ledger=ledger,
            frontier_owner=frontier_owner,
            frontier=frontier,
        )
        assert observed is (value <= boundary)
        assert 0 <= comparisons <= word.length
    assert ledger.counters["collatz_source_admission_word_nodes_visited"] > 0
    frontier_peak = ledger.counters.get(
        "collatz_source_admission_word_frontier_peak", 0
    )
    assert (frontier_peak > 0) is (word.run_count > 1)
    assert ledger.entries == ledger.nodes == 0


def test_most_significant_mismatch_does_not_exhaust_reverse_run_tail() -> None:

    word, lowest, original = _word_with_low_tail()
    object.__setattr__(lowest, "symbol", None)
    try:
        # Both operands have three radix-4 digits, and 3 > 2 at the most
        # significant digit. Reaching the deliberately malformed low tail would
        # prove that comparison had first exhausted/materialized every run.
        observed, comparisons = CollatzSourcePublisher._word_leq_integer(word, 2 << 4)
        assert observed is False and comparisons == 1
    finally:
        object.__setattr__(lowest, "symbol", original)


def test_long_common_prefix_uses_balanced_block_work() -> None:
    from number_compiler.arithmetic.automata.program_word import from_runs
    from number_compiler.resources.ledger import ResourceLedger

    runs = tuple((position % 4, 1) for position in range(256))
    word = from_runs(runs)
    value = sum(symbol << (2 * position) for position, (symbol, _) in enumerate(runs))
    ledger = ResourceLedger()
    frontier_owner = ledger.register("test-long-frontier", "runtime_query_workspace")
    frontier: LedgerList[tuple[CanonicalWord, int, int]] = ledger.make_list(
        frontier_owner, append_only=False
    )
    observed, comparisons = CollatzSourcePublisher._word_leq_integer(
        word,
        value,
        ledger=ledger,
        frontier_owner=frontier_owner,
        frontier=frontier,
    )
    assert observed is True and comparisons == word.length
    assert ledger.counters["collatz_source_admission_word_nodes_visited"] <= (
        2 * word.run_count - 1
    )
    assert ledger.counters["collatz_source_admission_word_block_bits_visited"] < (
        8 * word.length * word.run_count.bit_length()
    )
    assert ledger.entries == ledger.nodes == 0


def test_reverse_block_failure_releases_admission_frontier() -> None:
    from number_compiler.resources.ledger import ResourceLedger

    word, lowest, original = _word_with_low_tail()
    ledger = ResourceLedger()
    frontier_owner = ledger.register("test-failing-frontier", "runtime_query_workspace")
    frontier: LedgerList[tuple[CanonicalWord, int, int]] = ledger.make_list(
        frontier_owner, append_only=False
    )
    object.__setattr__(lowest, "symbol", None)
    try:
        with pytest.raises(AssertionError):
            CollatzSourcePublisher._word_leq_integer(
                word,
                (3 << 4) | (1 << 2),
                ledger=ledger,
                frontier_owner=frontier_owner,
                frontier=frontier,
            )
        assert ledger.entries == ledger.nodes == 0
    finally:
        object.__setattr__(lowest, "symbol", original)


def test_publisher_preserves_exact_intermediate_digit_budget() -> None:
    for seed in range(1, 48, 2):
        for events in range(5):
            for max_digits in range(1, 5):
                value = seed
                admissible = seed.bit_length() <= 2 * max_digits
                if admissible:
                    for _ in range(events):
                        if value == 1:
                            break
                        if len(tuple(digits_lsd(value, 4))) > max_digits:
                            admissible = False
                            break
                        numerator = 3 * value + 1
                        valuation = (numerator & -numerator).bit_length() - 1
                        value = numerator >> valuation
                publisher = CollatzSourcePublisher
                if not admissible:
                    with pytest.raises(ValueError, match="budget exceeded"):
                        publisher(
                            seed,
                            events,
                            max_events=events,
                            max_digits=max_digits,
                        ).publish()
                else:
                    published = publisher(
                        seed,
                        events,
                        max_events=events,
                        max_digits=max_digits,
                    ).publish()
                    assert published.discovery_digit_work >= published.discovered_events
                    assert (
                        published.owner.ledger.counters.get(
                            "collatz_source_discovery_digit_work", 0
                        )
                        == published.discovery_digit_work
                    )


def _word_with_low_tail() -> tuple[CanonicalWord, CanonicalWord, int | None]:
    from number_compiler.arithmetic.automata.program_word import from_runs

    word = from_runs(((97, 1), (1, 1), (3, 1)))
    lowest = word
    while lowest.left is not None:
        lowest = lowest.left
    original = lowest.symbol
    return word, lowest, original
