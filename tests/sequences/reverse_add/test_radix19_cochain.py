"""Exact source-bound decimal cochains over the redundant Q19 alphabet."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import replace
from random import Random

import pytest

from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.arithmetic.fields.walsh import walsh64_mod5
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import reverse_add as reverse_add_keys
from number_compiler.sequences.reverse_add.q19_output import (
    ReversePairQ19OutputOwner,
)
from number_compiler.sequences.reverse_add.radix19_cochain import (
    Radix19CarryBlock,
)
from tests.support.reverse_add_sources import periodic_reverse_add_source


def _reverse(value: int) -> int:
    return int(str(value)[::-1])


def _pairs(value: int) -> tuple[int, ...]:
    digits = digits_lsd(value, 10)
    return tuple(digits[i] + digits[-1 - i] for i in range(len(digits)))


def _eval(values: tuple[int, ...], z: int, modulus: int) -> int:
    return sum(value * pow(z, i, modulus) for i, value in enumerate(values)) % modulus


def test_radix19_cochain_matches_decimal_step_over_nonunit_rings() -> None:
    rng = Random(20261015)
    sources: tuple[int, ...] = (
        1,
        9,
        10,
        196,
        887,
        10089,
        10189,
        12302,
        1110,
        99999,
    )
    sources += tuple(rng.randrange(1, 10 ** rng.randrange(1, 22)) for _ in range(48))
    rings = ((0, 5), (2, 5), (10, 10000), (19, 97), (-1, 16), (5, 8))
    for initial in sources:
        ledger = ResourceLedger()
        owner = ReversePairQ19OutputOwner(ledger, digits_lsd(initial, 10), base=10)
        try:
            source, value = owner.initial, initial
            for _ in range(2):
                next_value = value + _reverse(value)
                for z, modulus in rings:
                    port = owner.radix19_cochain(source, z=z, modulus=modulus)
                    assert port.length == len(_pairs(value))
                    assert port.pairs == _eval(_pairs(value), z, modulus)
                    assert port.normalized_polynomial() == _eval(
                        digits_lsd(next_value, 10), z, modulus
                    )
                    assert port.successor_pair_polynomial() == _eval(
                        _pairs(next_value), z, modulus
                    )
                    assert port.exits[0] == int(len(str(next_value)) > len(str(value)))
                source = owner.apply_pair_step(source)
                value = next_value
        finally:
            owner.dispose()
            assert ledger.entries == ledger.nodes == 0


def test_source_cochain_fold_records_visits_and_compositions() -> None:
    value = int("1234567890" * 24)
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(value, 10), base=10)
    try:
        before = ledger.snapshot().counters
        owner.radix19_cochain(owner.initial, z=7, modulus=10**9)
        after = ledger.snapshot().counters
        assert after[reverse_add_keys.REVERSE_RADIX19_COCHAIN_NODE_VISITS] > before.get(
            reverse_add_keys.REVERSE_RADIX19_COCHAIN_NODE_VISITS, 0
        )
        assert after[
            reverse_add_keys.REVERSE_RADIX19_COCHAIN_COMPOSITIONS
        ] > before.get(reverse_add_keys.REVERSE_RADIX19_COCHAIN_COMPOSITIONS, 0)
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_two_ingress_carry_composition_and_repeat_are_exact() -> None:
    rng = Random(777)
    for _ in range(180):
        z, modulus = rng.randrange(-10, 20), rng.randrange(2, 200)
        symbols = tuple(rng.randrange(19) for _ in range(rng.randrange(1, 32)))
        action = Radix19CarryBlock.identity(z, modulus)
        for symbol in symbols:
            action = action.then(Radix19CarryBlock.atom(symbol, z, modulus))
        for ingress in (0, 1):
            carry = ingress
            carries: list[int] = []
            for symbol in symbols:
                carry = int(symbol + carry >= 10)
                carries.append(carry)
            assert action.carry[ingress] == _eval(tuple(carries), z, modulus)
            assert action.reverse_carry[ingress] == _eval(
                tuple(reversed(carries)), z, modulus
            )
            assert action.reverse_tail[ingress] == _eval(
                tuple(reversed(carries[:-1])), z, modulus
            )
            assert action.exits[ingress] == carry
        child = Radix19CarryBlock.atom(symbols[0], z, modulus)
        assert child.repeat(10) == child.repeat(3).then(child.repeat(7))
    huge = Radix19CarryBlock.atom(9, 2, 5).repeat(10**18)
    assert huge.length == 10**18 and huge.exits == (0, 1)


def test_source_walsh64_uses_issued_root_without_a_pair_step(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    value = int("9" * 80)
    expected = _pairs(value)
    future = _pairs(value + _reverse(value))
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(value, 10), base=10)
    try:

        def forbidden(*_args: object, **_kwargs: object) -> object:
            raise AssertionError("spatial cochain requested a temporal Q19 step")

        monkeypatch.setattr(owner, "apply_pair_step", forbidden)
        monkeypatch.setattr(owner, "apply_punctured_pair_block", forbidden)
        channels: tuple[tuple[str, tuple[int, ...], Callable[[int], bool]], ...] = (
            ("eq", expected, lambda item: item == 9),
            ("gt_high", expected, lambda item: item >= 15),
            ("future_eq", future, lambda item: item == 9),
            ("future_gt_high", future, lambda item: item >= 15),
        )
        for channel, source, predicate in channels:
            mask = 0
            for index in range(64):
                if predicate(source[index]):
                    mask |= 1 << index
            assert owner.radix19_walsh64_mod5(
                owner.initial, channel=channel
            ) == walsh64_mod5(mask)
        with pytest.raises(ValueError, match="certified pair width"):
            owner.radix19_walsh64_mod5(
                owner.initial, channel="future_eq", start=len(future)
            )
        assert ledger.counters.get("reverse_q19_punctured_t4_applications", 0) == 0
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_cochain_and_walsh_reject_a_forged_occurrence_before_refolding(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    value = int("48" * 80)
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(value, 10), base=10)
    try:
        forged = replace(owner.initial)

        def forbidden(*_args: object, **_kwargs: object) -> object:
            raise AssertionError("unissued occurrence reached source refolding")

        monkeypatch.setattr(owner, "_full_summary", forbidden)
        with pytest.raises(ValueError, match="was not issued"):
            owner.radix19_cochain(forged, z=0, modulus=5)
        with pytest.raises(ValueError, match="was not issued"):
            owner.radix19_walsh64_mod5(forged, channel="eq")
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_guarded_bank_cochain_and_conditional_walsh_use_live_later_root() -> None:
    seed = periodic_reverse_add_source((5, 16), seed=9631)
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(seed, 10), base=10)
    try:
        source = owner.apply_pair_step(owner.initial)
        control = owner.certify_border_growth(source, steps=8, window_digits=6)
        action = owner.authorize_radix19_gt_bank(
            source,
            steps=8,
            coordinate=201,
            period_sizes=(1, 2),
            window_digits=6,
        )
        cochain = owner.radix19_cochain(source, z=2, modulus=5)
        assert action.source_radix19_cochain(z=2, modulus=5) == cochain
        assert action.border_certificate is not None
        assert action.source_radix19_cochain().exits[0] == control.growth_word[0]
        assert action.full_integer_certified is False

        value = seed + _reverse(seed)
        for tick in range(8):
            value += _reverse(value)
            actual = _pairs(value)
            channels: tuple[tuple[str, Callable[[int], bool]], ...] = (
                ("eq", lambda item: item == 9),
                ("gt_high", lambda item: item >= 15),
            )
            for channel, predicate in channels:
                start = 178
                mask = 0
                for lane in range(64):
                    if predicate(actual[start + lane]):
                        mask |= 1 << lane
                assert action.certified_walsh64_mod5(
                    tick, channel=channel, start=start
                ) == walsh64_mod5(mask)
        with pytest.raises(ValueError, match="halo"):
            action.certified_walsh64_mod5(0, channel="eq", start=0)
        with pytest.raises(ValueError, match="nongrowth"):
            action.certified_borrow_xor_walsh64_mod5(7, start=178)
        assert ledger.counters.get("reverse_q19_punctured_t4_applications", 0) == 0
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_following_nongrowth_borrow_walsh_keeps_both_ingresses() -> None:
    seed = periodic_reverse_add_source((5, 16), seed=9631)
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(seed, 10), base=10)
    try:
        source = owner.apply_pair_step(owner.initial)
        certificate = owner.certify_border_growth(source, steps=8, window_digits=6)
        action = owner.authorize_controlled_gt_bank(
            source,
            steps=8,
            coordinate=201,
            period_size=2,
            growth_control=certificate,
        )
        current = seed + _reverse(seed)
        checked = 0
        for tick in range(8):
            target = current + _reverse(current)
            if tick + 1 < 8 and certificate.growth_word[tick + 1] == 0:
                following = target + _reverse(target)
                source_digits = digits_lsd(target, 10)
                reverse_current = digits_lsd(_reverse(target), 10)
                reverse_following = digits_lsd(_reverse(following), 10)
                carry = 0
                carries: list[int] = []
                for index, digit in enumerate(source_digits):
                    carry = int(digit + source_digits[-1 - index] + carry >= 10)
                    carries.append(carry)
                expected: list[tuple[int, ...]] = []
                for entering in (0, 1):
                    borrow, mask = entering, 0
                    for index in range(178, 178 + 64):
                        borrow = int(
                            reverse_following[index] < reverse_current[index] + borrow
                        )
                        mask |= (borrow ^ carries[index]) << (index - 178)
                    expected.append(walsh64_mod5(mask))
                assert action.certified_borrow_xor_walsh64_mod5(
                    tick, start=178
                ) == tuple(expected)
                checked += 1
            else:
                with pytest.raises(ValueError):
                    action.certified_borrow_xor_walsh64_mod5(tick, start=178)
            current = target
        assert checked == 4
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0
