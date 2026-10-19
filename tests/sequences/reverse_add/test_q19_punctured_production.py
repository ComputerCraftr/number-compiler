"""Fixed-depth punctured T2/T4 are completed production Q19 images."""

from typing import NoReturn

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from number_compiler.sequences.reverse_add.q19_output import (
    ReversePairQ19OutputOwner,
)
from number_compiler.sequences.reverse_add.source_images import (
    ReverseSourceImageAdapter,
)
from tests.support.reference_arithmetic import literal_reverse_add_digits


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
        assert counters["reverse_q19_punctured_event_regions"] > 0
        assert counters["reverse_q19_punctured_prefix_queries"] > 0
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
    prefix = temporal._CarryPrefix(runs, work)
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
    original_symbol_at = temporal._CarryPrefix.symbol_at

    def record_symbol_read(prefix: temporal._CarryPrefix, index: int) -> int:
        symbol_reads.append(index)
        return original_symbol_at(prefix, index)

    monkeypatch.setattr(temporal._CarryPrefix, "symbol_at", record_symbol_read)
    work = temporal.PuncturedTemporalWork()
    result, width = temporal._one_two_step_pair(((9, 1),), work)
    assert result
    assert width > 0
    assert work.event_regions == 1
    assert symbol_reads == [0]


def test_scheduler_publishes_punctured_t2_as_completed_output() -> None:
    seed = 196
    steps = 20
    term = ReverseAddPoweredTerm(seed, steps)
    workspace = term._source_workspace()
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
    workspace = term._source_workspace()
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
    original_issued = dict(owner._issued)
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
        assert dict(owner._issued) == original_issued
        owner.validate(initial)
        assert ledger.counters["reverse_q19_punctured_failed_applications"] == 1
    finally:
        monkeypatch.setattr(ledger, "bump", original_bump)
        owner.dispose()
