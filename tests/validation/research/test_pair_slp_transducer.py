from typing import Never

import pytest

from devtools.experiments.reverse_add.pair_slp_transducer import (
    PairSLPTransducer,
)
from number_compiler.arithmetic.automata.slp import SLPArena
from number_compiler.resources.ledger import ResourceLedger


def _expand(grammar: PairSLPTransducer, root: int) -> tuple[int, ...]:
    output: list[int] = []
    stack = [(root, 1)]
    while stack:
        node_id, count = stack.pop()
        node = grammar.node(node_id)
        if node.kind == "EMPTY":
            continue
        if node.kind == "TERM":
            output.extend((node.symbol,) * count)
        elif node.kind == "CONCAT":
            for _ in range(count):
                stack.extend(((node.right, 1), (node.left, 1)))
        elif node.kind == "REPEAT":
            stack.append((node.child, count * node.count))
        else:
            raise AssertionError(node.kind)
    return tuple(output)


def _digits(value: int) -> tuple[int, ...]:
    return tuple(map(int, reversed(str(value))))


@pytest.mark.parametrize(("initial", "steps"), ((1, 20), (196, 12)))
def test_actual_pair_slp_successors_match_bounded_oracle(
    initial: int, steps: int
) -> None:
    ledger = ResourceLedger()
    grammar = PairSLPTransducer(ledger)
    value = initial
    digits = grammar.word(_digits(value))
    pair = grammar.pair_from_digits(digits)
    growth_events = 0
    for _ in range(steps):
        step = grammar.successor(pair)
        growth_events += step.growth
        value += int(str(value)[::-1])
        assert _expand(grammar, step.digit_root) == _digits(value)
        pair = step.pair_root
    assert growth_events > 0
    grammar.close()
    assert ledger.entries == ledger.nodes == 0


def test_huge_uniform_source_stays_structural_for_six_step_core_cycle(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("pair SLP successor expanded its represented word")

    monkeypatch.setattr(SLPArena, "materialize", forbidden)
    ledger = ResourceLedger()
    grammar = PairSLPTransducer(ledger)
    width = 1 << 30
    pair = grammar.repeat(grammar.terminal(2), width)
    growth = 0
    for _ in range(6):
        step = grammar.successor(pair)
        growth += step.growth
        pair = step.pair_root
    clause = grammar.uniform_two_six_step_clause(width)
    assert grammar.node(pair).length == width + growth
    assert clause.growth == growth == 2
    assert grammar.exact_equal(pair, clause.target_root)
    assert len(grammar.reachable(pair)) < 200
    assert ledger.counters.get("reverse_pair_slp_zip_splits", 0) < 200
    grammar.close()
    assert ledger.entries == ledger.nodes == 0


def test_same_carry_word_does_not_authorize_temporal_merge() -> None:
    ledger = ResourceLedger()
    grammar = PairSLPTransducer(ledger)
    left = grammar.word((1, 2, 1))
    right = grammar.word((2, 1, 2))
    left_step = grammar.successor(left)
    right_step = grammar.successor(right)
    # Both inputs have the identical all-zero carry behavior, but their exact
    # output and successor pair grammars differ.
    assert left_step.growth == right_step.growth == 0
    assert _expand(grammar, left_step.digit_root) == (1, 2, 1)
    assert _expand(grammar, right_step.digit_root) == (2, 1, 2)
    assert _expand(grammar, left_step.pair_root) == (2, 4, 2)
    assert _expand(grammar, right_step.pair_root) == (4, 2, 4)
    grammar.close()


def test_misaligned_repetitions_report_structural_zip_refinement() -> None:
    ledger = ResourceLedger()
    grammar = PairSLPTransducer(ledger)
    left = grammar.concat(grammar.repeat(grammar.word((1, 2)), 9), grammar.terminal(3))
    right = grammar.concat(grammar.terminal(4), grammar.repeat(grammar.word((5, 6)), 9))
    result = grammar.zip_sum(left, right)
    assert _expand(grammar, result) == tuple(
        a + b
        for a, b in zip(
            _expand(grammar, left),
            _expand(grammar, right),
            strict=True,
        )
    )
    assert ledger.counters["reverse_pair_slp_zip_splits"] > 0
    grammar.close()


def test_reversed_zip_request_reuses_the_exact_commutative_result() -> None:
    ledger = ResourceLedger()
    grammar = PairSLPTransducer(ledger)
    left = grammar.concat(grammar.repeat(grammar.word((1, 2)), 9), grammar.terminal(3))
    right = grammar.concat(grammar.terminal(4), grammar.repeat(grammar.word((5, 6)), 9))
    result = grammar.zip_sum(left, right)
    before = ledger.snapshot()
    node_count = grammar.node_count
    reversed_result = grammar.zip_sum(right, left)
    assert reversed_result == result
    assert grammar.node_count == node_count
    assert ledger.snapshot() == before
    grammar.close()


def test_double_reflection_preserves_the_exact_word() -> None:
    ledger = ResourceLedger()
    grammar = PairSLPTransducer(ledger)
    source = grammar.concat_many(
        (
            grammar.word((1, 7, 3)),
            grammar.repeat(grammar.word((4, 2)), 11),
            grammar.word((8, 5)),
        )
    )
    reflected = grammar.reverse(source)
    restored = grammar.reverse(reflected)
    assert _expand(grammar, restored) == _expand(grammar, source)
    grammar.close()


def test_pair_successor_rejects_unallocated_roots() -> None:
    grammar = PairSLPTransducer(ResourceLedger())
    assert not hasattr(grammar, "arena")
    with pytest.raises(ValueError, match="foreign or out of range"):
        grammar.successor(-1)
    with pytest.raises(ValueError, match="foreign or out of range"):
        grammar.successor(grammar.node_count)
    with pytest.raises(ValueError, match="foreign or out of range"):
        grammar.concat(-1, grammar.terminal(1))
    grammar.close()


def test_repeat_slice_matches_every_bounded_interval() -> None:
    grammar = PairSLPTransducer(ResourceLedger())
    child = grammar.word((3, 7, 1))
    repeated = grammar.repeat(child, 4)
    reference = (3, 7, 1) * 4
    for start in range(len(reference) + 1):
        for stop in range(start, len(reference) + 1):
            assert (
                _expand(grammar, grammar.slice(repeated, start, stop))
                == (reference[start:stop])
            )
    grammar.close()


def test_disposed_pair_grammar_rejects_empty_queries() -> None:
    grammar = PairSLPTransducer(ResourceLedger())
    grammar.close()
    with pytest.raises(ValueError, match="disposed"):
        grammar.word(())
    with pytest.raises(ValueError, match="disposed"):
        grammar.concat_many(())
