"""Two-ended reverse/add border ports and exact Q19 source transfer."""

from __future__ import annotations

from random import Random

import pytest

from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    compose_carry_fn,
    value_carry_fn,
)
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.border_carry_safety import (
    BorderTile,
    bilateral_cycle_letter,
    border_bilateral_port,
    conditional_window_return_from_trace,
    enumerate_one_digit_cycles,
)
from number_compiler.sequences.reverse_add.q19_output import ReversePairQ19OutputOwner


def _tile(value: int, k: int) -> BorderTile:
    word = str(value)
    return BorderTile(k, int(word[:k]), int(word[-k:]))


def _middle_transfer(value: int, k: int) -> CarryFn:
    digits = digits_lsd(value, 10)
    transfer = CarryFn.ID
    for i in range(k, len(digits) - k):
        transfer = compose_carry_fn(
            value_carry_fn(digits[i] + digits[-i - 1], 10), transfer
        )
    return transfer


def test_17_and_71_force_low_carry_and_middle_transfer() -> None:
    tile = BorderTile(2, 17, 71)
    port = border_bilateral_port(tile)
    assert (port.low_sum, port.low_digits, port.low_carry) == (142, 42, 1)
    assert port.for_middle(CarryFn.CONST0).target == BorderTile(2, 34, 42)
    assert port.for_middle(CarryFn.ID).target == BorderTile(2, 35, 42)
    assert port.for_middle(CarryFn.CONST1).target == BorderTile(2, 35, 42)
    assert port.require_target(BorderTile(2, 34, 42)) == (CarryFn.CONST0,)
    assert port.require_target(BorderTile(2, 35, 42)) == (
        CarryFn.ID,
        CarryFn.CONST1,
    )
    assert port.require_target(BorderTile(2, 36, 42)) == ()
    for src, transfer, target in (
        (17071, CarryFn.CONST0, 34142),
        (17971, CarryFn.CONST1, 35942),
        (174571, CarryFn.ID, 350042),
    ):
        assert _middle_transfer(src, 2) is transfer
        assert port.for_middle(transfer).target == _tile(target, 2)
        assert src + int(str(src)[::-1]) == target


def test_bilateral_port_matches_exact_addition_random() -> None:
    rng = Random(501715)
    for _ in range(3000):
        width = rng.randrange(3, 40)
        src = rng.randrange(10 ** (width - 1), 10**width)
        k = rng.randrange(1, (width - 1) // 2 + 1)
        bilateral = border_bilateral_port(_tile(src, k))
        truth = src + int(str(src)[::-1])
        middle = _middle_transfer(src, k)
        alternative = bilateral.for_middle(middle)
        assert alternative.target == _tile(truth, k)
        assert alternative.growth == int(len(str(truth)) > width)
        assert middle in bilateral.require_target(_tile(truth, k))
        assert bilateral.low_carry == (bilateral.low_sum // 10**k)


def test_all_one_digit_cycles_have_two_sided_middle_constraints() -> None:
    cycles = enumerate_one_digit_cycles()
    assert len(cycles) == 96
    assert sum(c.has_trailing_zero for c in cycles) == 83
    for cycle in cycles:
        letters = cycle.bilateral_ports()
        assert len(letters) == cycle.steps
        for letter in letters:
            assert letter.admitted_middle
            for transfer in letter.admitted_middle:
                assert (
                    border_bilateral_port(letter.source).for_middle(transfer).target
                    == letter.target
                )
    observed = (
        BorderTile(2, 12, 2),
        BorderTile(2, 32, 23),
        BorderTile(2, 65, 46),
        BorderTile(2, 12, 2),
    )
    window_return = conditional_window_return_from_trace(observed, (0, 0, 1))
    assert len(window_return.bilateral_ports()) == 3
    assert window_return.bilateral_ports()[0].admitted_middle == (
        CarryFn.CONST0,
        CarryFn.ID,
    )
    exit_port = bilateral_cycle_letter(observed[3], BorderTile(2, 33, 23), 0)
    assert exit_port.admitted_middle == (CarryFn.CONST1,)
    assert exit_port.low_carry == 0


def test_live_owner_certifies_initial_middle_transfer_and_releases() -> None:
    for value, k, expected in (
        (17071, 2, CarryFn.CONST0),
        (17971, 2, CarryFn.CONST1),
        (174571, 2, CarryFn.ID),
        (196, 1, CarryFn.CONST1),
    ):
        ledger = ResourceLedger()
        owner = ReversePairQ19OutputOwner(ledger, digits_lsd(value, 10), base=10)
        try:
            cert = owner.certify_border_growth(owner.initial, steps=1, window_digits=k)
            derived = cert.initial_two_sided_carry()
            assert derived is not None
            assert derived.middle_transfer is expected
            assert derived.target == _tile(value + int(str(value)[::-1]), k)
            ports = cert.bilateral_carry_ports()
            assert len(ports) == 1
            assert ports[0] is not None
            assert ports[0].admitted_middle == (_middle_transfer(value, 1),)
            window_ports = cert.bilateral_window_ports()
            assert len(window_ports) == 1
            assert window_ports[0] is not None
            assert window_ports[0].admitted_middle == (expected,)
        finally:
            owner.dispose()
            assert ledger.entries == ledger.nodes == 0


def test_full_k_tile_trace_never_invents_a_window() -> None:
    x = 196
    for _ in range(79):
        x += int(str(x)[::-1])
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(x, 10), base=10)
    try:
        cert = owner.certify_border_growth(owner.initial, steps=9, window_digits=3)
        assert len(cert.window_tiles) == 10
        assert cert.window_tiles[0] == _tile(x, 3)
        k_ports = cert.bilateral_window_ports()
        assert len(k_ports) == 9
        for edge in k_ports:
            if edge is None:
                continue
            assert edge.admitted_middle
            assert edge.source.k == edge.target.k == 3
        assert any(edge is not None for edge in k_ports)
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_bank_exposes_guarded_bilateral_constraints() -> None:
    from tests.support.reverse_add_banks import source_guarded_periodic_banks

    with source_guarded_periodic_banks() as (_ledger, owner, cert, bank, morph):
        assert len(cert.bilateral_window_ports()) == 8
        for i in range(8):
            expected = cert.bilateral_carry_ports()[i]
            assert bank.bilateral_carry_port(i) == expected
            assert morph.bilateral_carry_port(i) == expected
        conditional = owner.authorize_controlled_gt_bank(
            owner.initial,
            steps=8,
            coordinate=200,
            period_size=2,
            growth_control=cert.growth_word,
        )
        with pytest.raises(ValueError, match="live border certificate"):
            conditional.bilateral_carry_port(0)
