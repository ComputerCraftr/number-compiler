"""Exact Q19 conditional pair/carry ports, including growth index shifts."""

from __future__ import annotations

from dataclasses import replace
from itertools import product
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
                    assert stencil.next_carry_domain_at(owner, i) == (
                        None if cell.coefficient == 9 else int(cell.coefficient > 9)
                    )
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
        with pytest.raises(IndexError):
            stencil.next_carry_domain_at(owner, stencil.target_pair_width)
        with pytest.raises(ValueError):
            stencil.next_carry_domain_at(foreign, 1)
        forged = replace(stencil, source_width=stencil.source_width + 1)
        with pytest.raises(ValueError, match="seam"):
            forged.next_carry_domain_at(owner, 1)
    finally:
        owner.dispose()
        foreign.dispose()
        assert ledger.entries == ledger.nodes == 0
        assert foreign_ledger.entries == foreign_ledger.nodes == 0


def test_growth_guard_constant_cofactor_skips_physical_inlets(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(9999, 10), base=10)
    try:
        stencil = GuardedPairStencil.from_occurrence(owner, owner.initial)
        assert stencil.source_growth == 1

        def forbidden(*_args: object, **_kwargs: object) -> int:
            pytest.fail("constant birth cofactor requested an irrelevant inlet")

        monkeypatch.setattr(GuardedPairStencil, "carry_at", forbidden)
        monkeypatch.setattr(GuardedPairStencil, "cell_at", forbidden)
        assert stencil.next_carry_domain_at(owner, 1) == 1
    finally:
        owner.dispose()
    assert ledger.entries == ledger.nodes == 0


def test_growth_guard_all_source_conditioned_cofactors(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(999999, 10), base=10)
    state = [0, 0, 0, 0]
    calls: list[int] = []
    try:
        stencil = GuardedPairStencil.from_occurrence(owner, owner.initial)
        assert stencil.source_width == 6 and stencil.source_growth == 1

        def pair_at(_self: object, _source: object, coordinate: int) -> int:
            assert coordinate in (1, 2)
            return state[0] if coordinate == 2 else state[1]

        def inlet(_self: object, _owner: object, boundary: int) -> int:
            calls.append(boundary)
            assert boundary in (1, 3)
            return state[2] if boundary == 1 else state[3]

        monkeypatch.setattr(ReversePairQ19OutputOwner, "pair_value_at", pair_at)
        monkeypatch.setattr(GuardedPairStencil, "carry_at", inlet)
        responses: set[tuple[int | None, ...]] = set()

        def literal(left: int, right: int, u: int, v: int) -> int | None:
            coefficient = (left + (right + u) // 10) % 10 + (
                right + (left + v) // 10
            ) % 10
            return None if coefficient == 9 else int(coefficient > 9)

        for left, right in product(range(19), repeat=2):
            row = tuple(
                literal(left, right, u, v) for u, v in product((0, 1), repeat=2)
            )
            responses.add(row)
            needs_u = row[0] != row[2] or row[1] != row[3]
            needs_v = row[0] != row[1] or row[2] != row[3]
            for u, v in product((0, 1), repeat=2):
                state[:] = [left, right, u, v]
                calls.clear()
                assert stencil.next_carry_domain_at(owner, 2) == literal(
                    left, right, u, v
                )
                assert calls == ([1] if needs_u else []) + ([3] if needs_v else [])
        assert len(responses) == 8
    finally:
        owner.dispose()
    assert ledger.entries == ledger.nodes == 0


def test_growth_eq_pair_does_not_assume_true_next_carry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.reverse_add.q19_broadword_publisher import PackedQ19

    ledger = ResourceLedger()
    digits = digits_lsd(190999, 10)
    owner = ReversePairQ19OutputOwner(ledger, digits, base=10)
    try:
        stencil = GuardedPairStencil.from_occurrence(owner, owner.initial)
        assert stencil.source_growth == 1
        assert owner.pair_value_at(owner.initial, 2) == 9
        assert owner.pair_value_at(owner.initial, 3) == 9
        cell = stencil.cell_at(owner, 3)
        assert cell.low_carry == cell.reflected_carry == 1
        assert cell.coefficient == 0
        carries: list[int] = []
        carry_at = GuardedPairStencil.carry_at

        def tracked(self: GuardedPairStencil, other: object, boundary: int) -> int:
            assert other is owner
            carries.append(boundary)
            return carry_at(self, owner, boundary)

        with monkeypatch.context() as patch:
            patch.setattr(GuardedPairStencil, "carry_at", tracked)
            assert stencil.next_carry_domain_at(owner, 3) == 0
        assert carries == [2]

        source = PackedQ19.from_digits(digits)
        target, _ = source.advance()
        _, _, ports = target.advance_with_ports()
        assert (ports.carry_in_lsd >> 3) & 1
        assert not (ports.carry_in_lsd >> 4) & 1
    finally:
        owner.dispose()
    assert ledger.entries == ledger.nodes == 0


def test_emitted_source_border_scan_consumes_domain_guard(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger, other_ledger = ResourceLedger(), ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(9999, 10), base=10)
    other_owner = ReversePairQ19OutputOwner(other_ledger, digits_lsd(9999, 10), base=10)
    try:
        source = owner.apply_pair_step(owner.initial)
        other_source = other_owner.apply_pair_step(other_owner.initial)
        assert source is not owner.initial
        stencil = GuardedPairStencil.from_occurrence(owner, source)
        assert stencil.source_growth == 1
        calls: list[int] = []
        original = GuardedPairStencil.next_carry_domain_at

        def tracked(self: GuardedPairStencil, other: object, index: int) -> int | None:
            assert other is owner
            calls.append(index)
            return original(self, owner, index)

        monkeypatch.setattr(GuardedPairStencil, "next_carry_domain_at", tracked)
        actual = owner.certify_border_growth(source, steps=2, window_digits=1)
        assert calls

        def exact(self: GuardedPairStencil, other: object, index: int) -> int | None:
            assert other is other_owner
            coefficient = self.cell_at(other_owner, index).coefficient
            return None if coefficient == 9 else int(coefficient > 9)

        monkeypatch.setattr(GuardedPairStencil, "next_carry_domain_at", exact)
        expected = other_owner.certify_border_growth(
            other_source, steps=2, window_digits=1
        )
        assert actual.growth_word == expected.growth_word
    finally:
        owner.dispose()
        other_owner.dispose()
    assert (
        ledger.entries
        == ledger.nodes
        == other_ledger.entries
        == other_ledger.nodes
        == 0
    )
