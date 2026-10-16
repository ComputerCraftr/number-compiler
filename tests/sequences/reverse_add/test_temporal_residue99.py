"""Predictive mod-99 reverse/add quotient, distinct from its GT-bank selector."""

from __future__ import annotations

from random import Random

import pytest

from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from number_compiler.sequences.reverse_add.q19_output import ReversePairQ19OutputOwner
from number_compiler.sequences.reverse_add.temporal_residue99 import (
    from_issued_pair,
    from_seed,
    future_moore_class,
    input_step,
)
from tests.support.reverse_add_sources import periodic_reverse_add_source


def _reverse(value: int) -> int:
    result = 0
    while value:
        value, digit = divmod(value, 10)
        result = 10 * result + digit
    return result


def _trace(seed: int, duration: int) -> tuple[list[int], tuple[int, ...]]:
    values = [seed]
    growth = []
    for _ in range(duration):
        src = values[-1]
        nxt = src + _reverse(src)
        growth.append(int(len(str(nxt)) > len(str(src))))
        values.append(nxt)
    return values, tuple(growth)


def test_mod99_source_universal_six_tick_collapse_is_sharp() -> None:
    values, bits = _trace(100, 10)
    assert values[:7] == [100, 101, 202, 404, 808, 1616, 7777]
    assert bits[:5] == (0, 0, 0, 0, 1)
    assert values[5] % 11 != 0 and values[6] % 11 == 0
    for seed in (0, 1, 2, 8, 10, 11, 79, 100, 196, 10089, 10189):
        values, _ = _trace(seed, 80)
        for depth in range(81):
            observation = from_seed(seed, depth)
            assert observation.target_mod99 == values[depth] % 99
            assert observation.target_mod9 == values[depth] % 9
            if depth >= 6:
                assert observation.target_mod11 == 0
                assert not observation.control_needed


def test_random_source_global_closed_form_matches_independent_successors() -> None:
    rng = Random(19199)
    for _ in range(140):
        width = rng.randint(1, 55)
        seed = rng.randrange(10 ** (width - 1), 10**width)
        values, _ = _trace(seed, 50)
        for depth in (0, 1, 2, 3, 4, 5, 6, 7, 8, 14, 23, 50):
            assert from_seed(seed, depth).target_mod99 == values[depth] % 99
        assert from_seed(seed, 10**18).target_mod11 == 0


def test_growth_input_moore_has_189_exact_future_classes() -> None:
    groups: dict[int, list[tuple[int, int]]] = {}
    for parity in (0, 1):
        for residue in range(99):
            groups.setdefault(future_moore_class(parity, residue), []).append(
                (parity, residue)
            )
    assert len(groups) == 189
    assert sorted(len(group) for group in groups.values()) == [1] * 180 + [2] * 9
    for states in groups.values():
        for growth in (0, 1):
            transitions = {
                (next_r, future_moore_class(next_p, next_r))
                for parity, residue in states
                for next_r, next_p in (input_step(residue, parity, growth),)
            }
            assert len(transitions) == 1
    for residue in range(99):
        if residue % 11:
            assert future_moore_class(0, residue) != future_moore_class(1, residue)
        else:
            assert future_moore_class(0, residue) == future_moore_class(1, residue)


def test_same_residue_and_parity_can_have_different_next_gt_control() -> None:
    values, growth = _trace(196, 10)
    assert values[3] % 99 == values[9] % 99 == 11
    assert len(str(values[3])) % 2 == len(str(values[9])) % 2 == 0
    assert growth[3] == 1 and growth[9] == 0


def test_pair_cochain_predicts_future_without_issuing_q19_children() -> None:
    for seed in (0, 1, 10, 100, 121, 196, 7890, 10089, 10189, 3411111):
        ledger = ResourceLedger()
        owner = ReversePairQ19OutputOwner(ledger, digits_lsd(seed, 10), base=10)
        try:
            for duration in (1, 6, 7, 99, 10**18):
                got = from_issued_pair(owner, owner.initial, duration)
                expected = from_seed(seed, duration)
                assert got.target_mod99 == expected.target_mod99
                assert got.source_certified and not got.control_needed
            if len(str(seed)) % 2 == 0:
                with pytest.raises(ValueError, match="even-width"):
                    from_issued_pair(owner, owner.initial, 0)
            elif seed % 11 == 0:
                unconditioned = from_issued_pair(owner, owner.initial, 4)
                assert unconditioned.source_certified
                assert unconditioned.target_mod99 == from_seed(seed, 4).target_mod99
            else:
                with pytest.raises(ValueError, match="growth word"):
                    from_issued_pair(owner, owner.initial, 4)
                values, growth = _trace(seed, 4)
                conditional = from_issued_pair(
                    owner, owner.initial, 4, growth_word=growth
                )
                assert conditional.target_mod99 == values[4] % 99
                assert not conditional.source_certified
            assert ledger.counters.get("reverse_q19_punctured_t4_applications", 0) == 0
            assert (
                ledger.counters.get("reverse_q19_primitive_pair_applications", 0) == 0
            )
        finally:
            owner.dispose()
            assert ledger.entries == ledger.nodes == 0


def test_certified_gt_bank_can_consume_the_source_mod99_projection() -> None:
    seed = periodic_reverse_add_source((5, 16), seed=9323)
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(seed, 10), base=10)
    try:
        cert = owner.certify_border_growth(owner.initial, steps=16, window_digits=6)
        action = owner.authorize_controlled_gt_bank(
            owner.initial,
            steps=16,
            coordinate=200,
            period_size=2,
            growth_control=cert,
        )
        got = action.temporal_residue99()
        assert got.source_certified
        assert got.target_mod99 == from_seed(seed, 16).target_mod99
        assert not got.complete_integer_certified
        assert ledger.counters.get("reverse_q19_punctured_t4_applications", 0) == 0
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_q19_later_root_mod99_needs_no_chronological_successors() -> None:
    for seed in (100, 196, 10089, 10189, 90009):
        ledger = ResourceLedger()
        owner = ReversePairQ19OutputOwner(ledger, digits_lsd(seed, 10), base=10)
        try:
            later = owner.apply_pair_step(owner.initial)
            current = seed + _reverse(seed)
            before = ledger.counters.get("reverse_q19_primitive_pair_applications", 0)
            result = from_issued_pair(owner, later, 10**18)
            assert result.target_mod99 == from_seed(current, 10**18).target_mod99
            assert (
                ledger.counters.get("reverse_q19_primitive_pair_applications", 0)
                == before
            )
        finally:
            owner.dispose()
            assert ledger.entries == ledger.nodes == 0


def test_seed_term_mod99_does_not_construct_workspace(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("scalar congruence opened the physical Q19 publisher")

    monkeypatch.setattr(ReverseAddPoweredTerm, "_source_workspace", forbidden)
    term = ReverseAddPoweredTerm(196, 10**50)
    got = term.temporal_residue99()
    assert got.target_mod99 == 11 * pow(2, 10**50 - 3, 99) % 99
    assert term._workspace is None
    assert term._ledger.entries == term._ledger.nodes == 0
