"""Group-ring/carry production cutover: exact source guards and finite macros."""

from __future__ import annotations

from itertools import groupby
from random import Random

import pytest

from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.punctured_temporal import (
    CarryPrefix,
    PuncturedTemporalWork,
    one_two_step_pair,
)
from number_compiler.sequences.reverse_add.q19_output import ReversePairQ19OutputOwner
from number_compiler.sequences.reverse_add.reverse_group_ring import (
    ReverseAddGroupRingCarry,
)


def _rev(x: int) -> int:
    return int(str(x)[::-1])


def _advance(x: int, n: int) -> int:
    for _ in range(n):
        x += _rev(x)
    return x


def _pairs(x: int) -> tuple[int, ...]:
    digits = digits_lsd(x, 10)
    return tuple(a + b for a, b in zip(digits, reversed(digits), strict=True))


def test_group_ring_stencil_recovers_every_raw_next_coefficient() -> None:
    rng = Random(20261026)
    for width in range(1, 16):
        for _ in range(90):
            first_half = [rng.randrange(19) for _ in range((width + 1) // 2)]
            first_half[0] = rng.randrange(1, 19)
            raw = tuple(
                first_half[i] if i < (width + 1) // 2 else first_half[width - 1 - i]
                for i in range(width)
            )
            prefix = CarryPrefix(tuple((s, 1) for s in raw), PuncturedTemporalWork())
            birth = prefix.carry_at(width)
            action = ReverseAddGroupRingCarry(width, birth)
            y = sum(s * 10**i for i, s in enumerate(raw))
            actual = _pairs(y)
            assert len(actual) == action.next_raw_width
            assert (
                tuple(
                    action.coefficient(
                        i, symbol_at=prefix.symbol_at, carry_at=prefix.carry_at
                    )
                    for i in range(action.next_raw_width)
                )
                == actual
            )
            runs = tuple((symbol, sum(1 for _ in run)) for symbol, run in groupby(raw))
            work = PuncturedTemporalWork()
            out, out_width = one_two_step_pair(tuple(runs), work)
            assert out_width == len(digits_lsd(y + _rev(y), 10))
            assert (
                tuple(v for v, count in out for _ in range(count))
                == _pairs(y + _rev(y))[: (out_width + 1) // 2]
            )
            assert work.two_step_actions == 1


def test_group_ring_carry_mod_no_inverses_even_when_99_divides_modulus() -> None:
    rng = Random(98192)
    for modulus in (2, 3, 99, 198, 9900, 9999):
        for _ in range(80):
            y = rng.randrange(1, 10 ** rng.randrange(1, 17))
            birth = rng.randrange(2)
            k = rng.randrange(10**8)
            raw_reflected = ((10 if birth else 1) * y - 99 * k) % (99 * modulus)
            assert (
                ReverseAddGroupRingCarry.carry_weight_mod(
                    y, raw_reflected, birth, modulus
                )
                == k % modulus
            )
            assert ReverseAddGroupRingCarry.reflected_correction_mod(
                y, raw_reflected, birth, 99 * modulus
            ) == -99 * k % (99 * modulus)
    with pytest.raises(ValueError, match="divisible"):
        ReverseAddGroupRingCarry.carry_weight_mod(5, 1, 0, 3)


def test_bounded_t16_t32_are_exact_without_intermediate_issued_occurrences() -> None:
    for seed in (1, 196, 10089, 999999):
        for steps in (16, 32):
            owner = ReversePairQ19OutputOwner(
                ResourceLedger(), digits_lsd(seed, 10), base=10
            )
            try:
                before = len(owner.audit_snapshot().issued.payload_view)
                target = owner.apply_punctured_pair_block(owner.initial, steps=steps)
                after = len(owner.audit_snapshot().issued.payload_view)
                assert target.temporal_steps == steps + 1
                assert tuple(owner.iter_digits(target)) == digits_lsd(
                    _advance(seed, steps + 1), 10
                )
                assert after == before + 1
                assert (
                    owner.ledger.counters["reverse_q19_punctured_physical_t2_actions"]
                    == steps // 2
                )
            finally:
                owner.dispose()
                assert owner.ledger.entries == owner.ledger.nodes == 0


def test_root_cli_group_ring_cocycle_equals_following_source() -> None:
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
    from number_compiler.sequences.reverse_add.temporal_seed_morphism import (
        certified_completed_reverse_add_seed_morphism,
    )

    for n in (16, 64, 128):
        term = ReverseAddPoweredTerm(196, n)
        try:
            packet = certified_completed_reverse_add_seed_morphism(term)
            last = packet.last
            y = _advance(196, n)
            z = y + _rev(y)
            assert last.residue198 == y % 198
            assert last.reverse_residue198 == _rev(y) % 198
            assert last.next_raw_residue198 == z % 198
            birth = last.leading_carry_digit
            k = ((10 if birth else 1) * y - _rev(y)) // 99
            assert last.reflected_carry_parity == k % 2
        finally:
            term.source_workspace().dispose()
