"""Finite punctured carry blocks are published as exact production Q19 images."""

from collections.abc import Callable, Generator
from contextlib import contextmanager
from typing import NoReturn

import pytest

import number_compiler.sequences.reverse_add.punctured_temporal as punctured_temporal
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import reverse_add as metric_keys
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from number_compiler.sequences.reverse_add.q19_output import (
    ReversePairQ19OutputOwner,
)
from number_compiler.sequences.reverse_add.q19_punctured_producer import (
    admits_punctured_scheduler_block,
)
from number_compiler.sequences.reverse_add.source_images import (
    ReverseSourceImageAdapter,
)
from number_compiler.sequences.reverse_add.temporal_port_quotient import (
    MAX_EXACT_DECIMAL_BLOCK_WIDTH,
    native_decimal_string_transport,
)
from tests.support.reference_arithmetic import literal_reverse_add_digits


@pytest.mark.parametrize("seed", (99, 196))
def test_native_reservation_uses_the_normalized_source_width(
    monkeypatch: pytest.MonkeyPatch, seed: int
) -> None:
    owner = ReversePairQ19OutputOwner(
        ResourceLedger(), literal_reverse_add_digits(seed, 0), base=10
    )
    reserved: list[tuple[int, int]] = []
    original = ResourceLedger.reservation

    @contextmanager
    def recording(
        ledger: ResourceLedger, account: int, *, entries: int = 0, nodes: int = 0
    ) -> Generator[None]:
        if ledger is owner.ledger and account == owner.scratch_owner:
            reserved.append((entries, nodes))
        with original(ledger, account, entries=entries, nodes=nodes):
            yield

    try:
        source = owner.initial
        runs = owner.word_summary(source.root).runs
        expected = 2 * (source.output_width + 16) + 32 * (runs + 1)
        monkeypatch.setattr(ResourceLedger, "reservation", recording)
        result = owner.apply_punctured_pair_block(source, steps=16)
        assert (expected, expected) in reserved
        assert tuple(owner.iter_digits(result)) == literal_reverse_add_digits(seed, 17)
        available = MAX_EXACT_DECIMAL_BLOCK_WIDTH - 64
        assert admits_punctured_scheduler_block(64, available)
        assert not admits_punctured_scheduler_block(64, available + 1)
    finally:
        owner.dispose()


def test_punctured_scheduler_retains_the_certified_8192_action_bound() -> None:
    assert admits_punctured_scheduler_block(8192, 1000)
    assert not admits_punctured_scheduler_block(8193, 1000)
    assert not admits_punctured_scheduler_block(8192, 11_809)


def test_punctured_t2_advances_two_pair_transitions_from_term_one() -> None:
    seed = 196
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(
        ledger, literal_reverse_add_digits(seed, 0), base=10
    )
    try:
        # The Q19 initial pair tape is term 1. Its T2 action therefore lands
        # at term 3; it must not be mistaken for three transitions from seed.
        result = owner.apply_punctured_pair_block(owner.initial, steps=2)
        assert result.temporal_steps == 3
        assert result.output_width == len(literal_reverse_add_digits(seed, 3))
        assert tuple(owner.iter_digits(result)) == literal_reverse_add_digits(seed, 3)
        counters = ledger.counters
        assert counters["reverse_q19_punctured_t2_applications"] == 1
        assert counters["reverse_q19_punctured_event_regions"] == 0
        assert counters["reverse_q19_punctured_prefix_queries"] == 0
        assert counters["reverse_q19_punctured_half_tape_tick_transitions"] == 2
        assert counters["reverse_q19_punctured_emitted_grammar_nodes"] > 0
        assert counters.get("reverse_q19_primitive_pair_applications", 0) == 0
    finally:
        owner.dispose()


def test_punctured_t4_advances_four_pair_transitions_without_leaf_replay(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    seed = 196
    owner = ReversePairQ19OutputOwner(
        ResourceLedger(), literal_reverse_add_digits(seed, 0), base=10
    )

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("T4 pullback replayed a primitive pair step")

    monkeypatch.setattr(ReversePairQ19OutputOwner, "apply_pair_step", forbidden)
    try:
        result = owner.apply_punctured_pair_block(owner.initial, steps=4)
        expected = literal_reverse_add_digits(seed, 5)
        assert result.temporal_steps == 5
        assert result.output_width == len(expected)
        assert tuple(owner.iter_digits(result)) == expected
        counters = owner.ledger.counters
        assert counters["reverse_q19_punctured_t4_applications"] == 1
        assert counters.get("reverse_q19_punctured_t2_applications", 0) == 0
        assert counters.get("reverse_q19_primitive_pair_applications", 0) == 0
    finally:
        owner.dispose()


def test_carry_prefix_offsets_reuse_the_composed_run_effect(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.sequences.reverse_add.punctured_temporal as temporal

    runs = ((9, 2), (9, 3), (10, 2), (18, 4), (0, 3), (11, 2))
    work = temporal.PuncturedTemporalWork()
    prefix = temporal.CarryPrefix(runs, work)
    assert prefix.runs == ((9, 5), (10, 2), (18, 4), (0, 3), (11, 2))

    symbols = tuple(symbol for symbol, count in runs for _ in range(count))
    expected = [0]
    carry = 0
    for symbol in symbols:
        carry = (symbol + carry) // 10
        expected.append(carry)

    def forbidden_recomposition(*_args: object, **_kwargs: object) -> NoReturn:
        raise AssertionError("carry lookup reconstructed an admitted run effect")

    monkeypatch.setattr(temporal, "value_carry_fn", forbidden_recomposition)
    monkeypatch.setattr(temporal, "compose_carry_fn", forbidden_recomposition)
    assert tuple(prefix.carry_at(offset) for offset in range(len(expected))) == tuple(
        expected
    )


def test_singleton_event_interval_checks_its_only_endpoint_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.sequences.reverse_add.punctured_temporal as temporal

    symbol_reads: list[int] = []
    originalsymbol_at = temporal.CarryPrefix.symbol_at

    def record_symbol_read(prefix: temporal.CarryPrefix, index: int) -> int:
        symbol_reads.append(index)
        return originalsymbol_at(prefix, index)

    monkeypatch.setattr(temporal.CarryPrefix, "symbol_at", record_symbol_read)
    work = temporal.PuncturedTemporalWork()
    result, width = temporal.one_two_step_pair(((9, 1),), work)
    assert result
    assert width > 0
    assert work.event_regions == 1
    assert symbol_reads == [0]


def test_scheduler_publishes_punctured_t2_as_completed_output() -> None:
    seed = 196
    steps = 20
    term = ReverseAddPoweredTerm(seed, steps)
    workspace = term.source_workspace()
    try:
        assert term.digits() == literal_reverse_add_digits(seed, steps)
        counters = term.resource_ledger.counters
        assert counters.get("reverse_q19_punctured_t2_applications", 0) > 0
        assert counters.get("reverse_q19_root_bootstrap_publications", 0) > 0
        assert counters.get("reverse_q19_root_bootstrap_pair_steps", 0) > 0
    finally:
        workspace.dispose()


def test_larger_request_joins_punctured_children_without_source_primitive_descent(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    seed = 196
    steps = 8
    term = ReverseAddPoweredTerm(seed, steps)
    workspace = term.source_workspace()
    try:

        def forbidden(*_args: object, **_kwargs: object) -> None:
            raise AssertionError("T2/T4 composite descended to a source primitive")

        monkeypatch.setattr(ReverseSourceImageAdapter, "apply_primitive", forbidden)
        assert term.digits() == literal_reverse_add_digits(seed, steps)
        counters = term.resource_ledger.counters
        assert (
            counters.get("reverse_source_punctured_completed_child_publications", 0) > 0
        )
        assert counters.get("source_image_chronological_compositions", 0) > 0
        assert counters.get("reverse_q19_punctured_t2_applications", 0) > 0
        assert counters.get("reverse_q19_punctured_t4_applications", 0) > 0
    finally:
        workspace.dispose()


def test_failed_postpublication_accounting_rolls_back_issued_slp(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(
        ledger, literal_reverse_add_digits(196, 0), base=10
    )
    initial = owner.initial
    original_nodes = len(owner.arena.nodes)
    original_issued = dict(owner.audit_snapshot().issued.payload_view)
    original_bump = ledger.bump
    failed = False

    def fail_emitted_node_counter(name: str, amount: int = 1) -> None:
        nonlocal failed
        if name == "reverse_q19_punctured_emitted_grammar_nodes" and not failed:
            failed = True
            raise RuntimeError("injected metric failure after publication")
        original_bump(name, amount)

    monkeypatch.setattr(ledger, "bump", fail_emitted_node_counter)
    try:
        with pytest.raises(RuntimeError, match="injected metric failure"):
            owner.apply_punctured_pair_block(initial, steps=2)
        assert len(owner.arena.nodes) == original_nodes
        assert dict(owner.audit_snapshot().issued.payload_view) == original_issued
        owner.validate(initial)
        assert ledger.counters["reverse_q19_punctured_failed_applications"] == 1
    finally:
        monkeypatch.setattr(ledger, "bump", original_bump)
        owner.dispose()


def test_interrupted_native_block_charges_progress_and_rolls_back(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_transport = native_decimal_string_transport
    started_widths: list[int] = []
    block_start_width: list[int] = []

    def interrupt_after_three_ticks(
        source_text: str,
        steps: int,
        *,
        max_width: int = MAX_EXACT_DECIMAL_BLOCK_WIDTH,
        on_tick_start: Callable[[int], None] | None = None,
    ) -> tuple[str, int]:
        if on_tick_start is None:
            raise AssertionError("native finite block omitted work accounting")
        block_start_width.append(len(source_text))

        def interrupting_tick(width: int) -> None:
            on_tick_start(width)
            started_widths.append(width)
            if len(started_widths) == 3:
                raise RuntimeError("interrupted native decimal block")

        return original_transport(
            source_text,
            steps,
            max_width=max_width,
            on_tick_start=interrupting_tick,
        )

    monkeypatch.setattr(
        punctured_temporal,
        "native_decimal_string_transport",
        interrupt_after_three_ticks,
    )
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(
        ledger, literal_reverse_add_digits(196, 0), base=10
    )
    initial_nodes = len(owner.arena.nodes)
    initial_issues = dict(owner.audit_snapshot().issued.payload_view)
    try:
        with pytest.raises(RuntimeError, match="interrupted native decimal block"):
            owner.apply_punctured_pair_block(owner.initial, steps=17)

        counters = ledger.counters
        assert counters[metric_keys.REVERSE_Q19_PUNCTURED_NATIVE_DECIMAL_TICKS] == 3
        assert counters[
            metric_keys.REVERSE_Q19_PUNCTURED_NATIVE_DECIMAL_DIGIT_VISITS
        ] == block_start_width[0] + sum(started_widths)
        assert counters[metric_keys.REVERSE_Q19_PUNCTURED_FAILED_APPLICATIONS] == 1
        assert len(owner.arena.nodes) == initial_nodes
        assert dict(owner.audit_snapshot().issued.payload_view) == initial_issues
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_seed_196_8256_nth_uses_bounded_q19_publications() -> None:
    term = ReverseAddPoweredTerm(196, 8256)
    workspace = term.source_workspace()
    try:
        expected = literal_reverse_add_digits(196, 8256)
        assert term.digits() == expected
        counters = term.resource_ledger.counters
        assert (
            counters.get(
                metric_keys.REVERSE_SOURCE_PUNCTURED_COMPLETED_CHILD_PUBLICATIONS, 0
            )
            <= 32
        )
        assert counters.get(metric_keys.REVERSE_Q19_PUNCTURED_WIDE_APPLICATIONS, 0) > 0
        exact_transitions = (
            counters.get(metric_keys.REVERSE_Q19_PUNCTURED_NATIVE_DECIMAL_TICKS, 0)
            + counters.get(metric_keys.REVERSE_Q19_BROADWORD_SEMANTIC_STEPS, 0)
            + counters.get(metric_keys.REVERSE_Q19_BROADWORD_ENDPOINT_PUBLICATIONS, 0)
        )
        assert exact_transitions >= 8000
    finally:
        workspace.dispose()
