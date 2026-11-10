"""Keep pumped nonuniform Q19 operands compressed through finite actions."""

from __future__ import annotations

from typing import Never

import pytest

from number_compiler.arithmetic.automata.slp import (
    BimachineSLPProjector,
    SLPArena,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import reverse_add as keys
from number_compiler.sequences.reverse_add.q19_occurrence import (
    ReversePairOutputOccurrence,
)
from number_compiler.sequences.reverse_add.q19_output import (
    ReversePairQ19OutputOwner,
)
from number_compiler.sequences.reverse_add.q19_word_summary import pair_step_law


def _source(
    pairs: tuple[int, int], repeats: int, center: int | None
) -> tuple[ReversePairQ19OutputOwner, ReversePairOutputOccurrence]:
    values = pairs * repeats
    width = 2 * len(values) + int(center is not None)
    digits = [0] * width
    for index, coefficient in enumerate(values):
        low = min(9, coefficient)
        digits[index] = low
        digits[width - 1 - index] = coefficient - low
    if center is not None:
        digits[len(values)] = center

    owner = ReversePairQ19OutputOwner(ResourceLedger(), tuple(digits), base=10)
    arena = owner.arena
    repeated = arena.repeat(
        arena.concat(arena.terminal(pairs[0]), arena.terminal(pairs[1])), repeats
    )
    parts = [arena.terminal(20 if center is not None else 19), repeated]
    if center is not None:
        parts.append(arena.terminal(2 * center))
    parts.append(arena.terminal(21))
    issued = owner.publish(owner.candidate(arena.concat_many(parts), 1))
    assert tuple(owner.iter_digits(issued)) == tuple(owner.iter_digits(owner.initial))
    return owner, issued


def _literal_step(digits_lsd: tuple[int, ...]) -> tuple[int, ...]:
    source = "".join(str(digit) for digit in reversed(digits_lsd))
    target = str(int(source) + int(source[::-1]))
    return tuple(int(digit) for digit in reversed(target))


@pytest.mark.parametrize("pairs", ((0, 18), (9, 10), (18, 0), (6, 11), (10, 11)))
@pytest.mark.parametrize("center", (None, 0, 3, 5, 9))
def test_pumped_band_uses_q19_projector_without_expanding_runs(
    monkeypatch: pytest.MonkeyPatch,
    pairs: tuple[int, int],
    center: int | None,
) -> None:
    owner, source = _source(pairs, 32, center)
    try:
        expected = tuple(owner.iter_digits(source))
        for _ in range(4):
            expected = _literal_step(expected)

        def reject_run_expansion(_self: object, _root: int) -> Never:
            raise AssertionError("nonuniform Q19 repeat reached run expansion")

        monkeypatch.setattr(
            "number_compiler.sequences.reverse_add.q19_punctured_producer."
            "PuncturedPairProducer._coefficient_runs",
            reject_run_expansion,
        )
        result = owner.apply_punctured_pair_block(source, steps=4)
        assert tuple(owner.iter_digits(result)) == expected
        assert result.temporal_steps == source.temporal_steps + 4
        assert (
            owner.ledger.counters[keys.REVERSE_Q19_PUNCTURED_SPATIAL_PROJECTOR_STEPS]
            == 4
        )
        assert (
            owner.ledger.counters[keys.REVERSE_Q19_PUNCTURED_NATIVE_DECIMAL_TICKS] == 0
        )
        assert (
            owner.ledger.counters.get(
                keys.REVERSE_Q19_PUNCTURED_INPUT_GRAMMAR_NODES_VISITED, 0
            )
            == 0
        )
    finally:
        owner.dispose()
        assert owner.ledger.entries == owner.ledger.nodes == 0


@pytest.mark.parametrize("repeats", (100, 10**12))
def test_spatial_projector_powers_a_symbolic_repeat_exponent(repeats: int) -> None:
    arena = SLPArena()
    child = arena.concat(arena.terminal(10), arena.terminal(11))
    root = arena.concat_many(
        (arena.terminal(19), arena.repeat(child, repeats), arena.terminal(21))
    )
    projector = BimachineSLPProjector(pair_step_law(), arena)
    source_length = arena.nodes[root].length
    for _ in range(16):
        root = projector.apply(root)
    assert source_length <= arena.nodes[root].length <= source_length + 16
    assert projector.section_calls < 1200
    assert len(arena.nodes) < 1200


@pytest.mark.parametrize("steps", (4, 16))
def test_failed_pumped_action_rolls_back_and_next_action_recovers(
    monkeypatch: pytest.MonkeyPatch,
    steps: int,
) -> None:
    owner, source = _source((10, 11), 32, 3)
    try:
        before_nodes = len(owner.arena.nodes)
        before_issued = dict(owner.audit_snapshot().issued.payload_view)
        original_apply = BimachineSLPProjector.apply
        calls = 0

        def fail_after_first(self: BimachineSLPProjector, root: int) -> int:
            nonlocal calls
            result = original_apply(self, root)
            calls += 1
            if calls == 2:
                raise RuntimeError("injected projector failure")
            return result

        with monkeypatch.context() as patch:
            patch.setattr(BimachineSLPProjector, "apply", fail_after_first)
            with pytest.raises(RuntimeError, match="projector failure"):
                owner.apply_punctured_pair_block(source, steps=steps)
        assert len(owner.arena.nodes) == before_nodes
        assert dict(owner.audit_snapshot().issued.payload_view) == before_issued
        assert (
            owner.ledger.counters[keys.REVERSE_Q19_PUNCTURED_FAILED_APPLICATIONS] == 1
        )
        assert all(len(cache) == 0 for cache in owner.projector.audit_cache_stores)

        recovered = owner.apply_punctured_pair_block(source, steps=2)
        expected = _literal_step(_literal_step(tuple(owner.iter_digits(source))))
        assert tuple(owner.iter_digits(recovered)) == expected
    finally:
        owner.dispose()
        assert owner.ledger.entries == owner.ledger.nodes == 0


def test_uncompressed_source_keeps_existing_native_macro_path() -> None:
    owner = ReversePairQ19OutputOwner(ResourceLedger(), (6, 9, 1), base=10)
    try:
        result = owner.apply_punctured_pair_block(owner.initial, steps=16)
        assert tuple(owner.iter_digits(result))
        assert (
            owner.ledger.counters[keys.REVERSE_Q19_PUNCTURED_NATIVE_DECIMAL_TICKS] == 15
        )
        assert (
            owner.ledger.counters.get(
                keys.REVERSE_Q19_PUNCTURED_SPATIAL_PROJECTOR_STEPS, 0
            )
            == 0
        )
    finally:
        owner.dispose()
        assert owner.ledger.entries == owner.ledger.nodes == 0


@pytest.mark.parametrize("repeats,steps", ((2, 16), (3, 32), (15, 64), (32, 16)))
def test_long_action_keeps_small_nonuniform_repeats_compressed(
    monkeypatch: pytest.MonkeyPatch, repeats: int, steps: int
) -> None:
    owner, source = _source((10, 11), repeats, 3)
    try:
        expected = tuple(owner.iter_digits(source))
        for _ in range(steps):
            expected = _literal_step(expected)

        def reject_expansion(_self: object, _root: int) -> Never:
            raise AssertionError("nonuniform repeat was expanded")

        monkeypatch.setattr(
            "number_compiler.sequences.reverse_add.q19_punctured_producer."
            "PuncturedPairProducer._coefficient_runs",
            reject_expansion,
        )
        result = owner.apply_punctured_pair_block(source, steps=steps)
        assert tuple(owner.iter_digits(result)) == expected
        assert result.temporal_steps == source.temporal_steps + steps
        assert (
            owner.ledger.counters[keys.REVERSE_Q19_PUNCTURED_SPATIAL_PROJECTOR_STEPS]
            == steps
        )
        assert (
            owner.ledger.counters[keys.REVERSE_Q19_PUNCTURED_NATIVE_DECIMAL_TICKS] == 0
        )
        assert owner.ledger.counters[
            keys.REVERSE_Q19_PUNCTURED_REPEAT_GUARD_NODE_VISITS
        ] <= len(owner.arena.nodes)
    finally:
        owner.dispose()
        assert owner.ledger.entries == owner.ledger.nodes == 0
