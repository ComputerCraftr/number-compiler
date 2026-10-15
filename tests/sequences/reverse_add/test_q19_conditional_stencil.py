"""Exact Q19 conditional pair/carry ports, including growth index shifts."""

from __future__ import annotations

from random import Random

import pytest

from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.q19_conditional_stencil import (
    GuardedPairStencil,
)
from number_compiler.sequences.reverse_add.q19_output import (
    ReversePairQ19OutputOwner,
)
from number_compiler.sequences.reverse_add.temporal_matrix import (
    ReverseInnovationBank,
)
from tests.support.reverse_pair_oracle import literal_decimal_borrow_tape


def _reverse(value: int) -> int:
    return int(str(value)[::-1])


def test_conditional_pair_stencil_all_positions_and_center() -> None:
    rng = Random(20261014)
    sources = [0, 9, 196, 999, 1110, 1818, 10089, 10189, 12302, 104, 107]
    sources += [rng.randrange(1, 10 ** rng.randrange(1, 13)) for _ in range(90)]
    for seed in sources:
        ledger = ResourceLedger()
        owner = ReversePairQ19OutputOwner(ledger, digits_lsd(seed, 10), base=10)
        try:
            source = owner.initial
            for _ in range(3):
                stencil = GuardedPairStencil.from_occurrence(owner, source)
                target = owner.apply_pair_step(source)
                assert stencil.target_pair_width == target.pair_width
                for i in range(target.pair_width):
                    cell = stencil.verify_target_at(owner, target, i)
                    assert 0 <= cell.coefficient <= 18
                    expected_band = (
                        "lt_low"
                        if cell.coefficient <= 4
                        else "lt_high"
                        if cell.coefficient <= 8
                        else "eq"
                        if cell.coefficient == 9
                        else "gt_low"
                        if cell.coefficient <= 14
                        else "gt_high"
                    )
                    assert cell.five_band == expected_band
                    assert cell.f5 == cell.coefficient % 5
                    if stencil.source_growth and i in (0, target.pair_width - 1):
                        assert cell.border_birth
                        assert cell.reflected_xor is None
                    else:
                        assert not cell.border_birth
                        assert cell.reflected_xor in (0, 1)
                source = target
        finally:
            owner.dispose()
            assert ledger.entries == ledger.nodes == 0


def test_reflected_f5_eq_and_zero_nine_borrow_gates() -> None:
    # Paired F5/carry EQ births and next-innovation signed borrows are
    # independently checked against real future arithmetic, not Q19 itself.
    rng = Random(983)
    for x in list(range(1, 1500)) + [rng.randrange(10**30, 10**31) for _ in range(250)]:
        bank = ReverseInnovationBank.observe(x, moduli=())
        y = x + _reverse(x)
        z = _reverse(y) - _reverse(x)
        assert bank.future_innovation_sign == (z > 0) - (z < 0)
        if not bank.growth:
            nd = [int(char) for char in str(y)[::-1]]
            eq = sum(int(d + nd[-1 - i] == 9) << i for i, d in enumerate(nd))
            assert bank.next_eq_nongrowth_mask == eq
            # The independent raw subtraction cannot borrow a sign from the
            # oriented absolute difference: check every bit and final sign.
            tape, debt = literal_decimal_borrow_tape(
                _reverse(y), _reverse(x), bank.width
            )
            assert bank.future_raw_borrow_mask == tape
            assert debt == int(bank.future_innovation_sign < 0)
        else:
            assert bank.next_eq_nongrowth_mask is None
            assert bank.borrow_identity_gate_mask is None


def test_signed_raw_borrow_differs_from_oriented_magnitude() -> None:
    x = 1067869
    prev = 1794102596
    bank = ReverseInnovationBank.observe(x, previous=prev, moduli=(7, 27))
    assert bank.innovation_sign == (
        (_reverse(x) > _reverse(prev)) - (_reverse(x) < _reverse(prev))
    )
    assert bank.raw_borrow_mask is not None
    assert bank.borrow_mask is not None
    assert bank.raw_xor_mask == bank.carry_mask ^ bank.raw_borrow_mask
    assert bank.xor_mask == bank.carry_mask ^ bank.borrow_mask
    assert bank.masks_partition()


def test_conditional_stencil_rejects_foreign_and_nonadjacent_targets() -> None:
    ledger, foreign_ledger = ResourceLedger(), ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(196, 10), base=10)
    foreign = ReversePairQ19OutputOwner(foreign_ledger, digits_lsd(196, 10), base=10)
    try:
        source = owner.initial
        stencil = GuardedPairStencil.from_occurrence(owner, source)
        first = owner.apply_pair_step(source)
        second = owner.apply_pair_step(first)
        with pytest.raises(ValueError, match="adjacent"):
            stencil.verify_target_at(owner, second, 0)
        with pytest.raises(ValueError):
            stencil.verify_target_at(foreign, foreign.initial, 0)
        with pytest.raises(IndexError):
            stencil.cell_at(owner, stencil.target_pair_width)
        with pytest.raises(IndexError):
            stencil.carry_at(owner, -1)
    finally:
        owner.dispose()
        foreign.dispose()
        assert ledger.entries == ledger.nodes == 0
        assert foreign_ledger.entries == foreign_ledger.nodes == 0
