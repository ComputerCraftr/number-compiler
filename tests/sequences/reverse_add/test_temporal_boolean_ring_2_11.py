"""Independent proof obligations of fixed-precision 2^q11^g source stages."""

from __future__ import annotations

import random

import pytest

from number_compiler.sequences.reverse_add.q19_broadword_publisher import PackedQ19
from number_compiler.sequences.reverse_add.temporal_boolean_ring_2_11 import (
    BCDPlanes,
    Mixed211Phase,
    Powered211CarrySheets,
    log_16_of_11_mod_5_power,
    nand,
    ordered_child_matrices,
)


def _matmul(
    a: tuple[tuple[int, ...], ...], b: tuple[tuple[int, ...], ...]
) -> tuple[tuple[int, ...], ...]:
    return tuple(
        tuple(sum(a[i][p] * b[p][j] for p in range(2)) for j in range(2))
        for i in range(2)
    )


def _carry11_oracle(x: int, w: int) -> int:
    digs = [int(d) for d in str(x).zfill(w)[::-1]]
    c = 0
    out = 0
    for j in range(w + 2):
        d = digs[j] if j < w else 0
        previous = digs[j - 1] if 0 < j <= w else 0
        t = d + previous + c
        c = t // 10
        out |= c << j
    return out


def test_boolean_bcd_two_eleven_carries_exhaustive_small() -> None:
    for w in range(1, 4):
        for x in range(10**w):
            b = BCDPlanes.from_residue(x, w)
            t, carry2 = b.multiply_two()
            e, carry11 = b.multiply_eleven()
            assert t.residue() == x * 2
            assert e.residue() == x * 11
            expected2 = sum(
                (int(d) >= 5) << j for j, d in enumerate(str(x).zfill(w)[::-1])
            )
            assert carry2 == expected2
            assert carry11 == _carry11_oracle(x, w)
            assert nand(carry2, carry2, w) == ((1 << w) - 1) ^ carry2


def test_boolean_random_high_width_and_q19_bridge() -> None:
    rng = random.Random(211)
    for width in (1, 2, 3, 8, 13, 64, 127, 256):
        for _ in range(30):
            x = rng.randrange(10**width)
            b = BCDPlanes.from_residue(x, width)
            assert b.residue() == x
            q2, r5 = b.two_five_complementary_sheets()
            for j, d in enumerate(b.digits_lsd()):
                r = ((r5[0] >> j) & 1) + 2 * ((r5[1] >> j) & 1) + 4 * ((r5[2] >> j) & 1)
                assert 5 * ((q2 >> j) & 1) + r == d
            t, carry2 = b.multiply_two()
            e, carry11 = b.multiply_eleven()
            assert t.residue() == 2 * x
            assert e.residue() == 11 * x
            assert carry11 == _carry11_oracle(x, width)
            tree_out, tree_carry = b.multiply_eleven(linear_tower=True)
            assert tree_out == e
            assert tree_carry == carry11
            assert carry2 == sum(
                (int(d) >= 5) << j for j, d in enumerate(str(x).zfill(width)[::-1])
            )
            assert b.restrict(max(1, width // 2)).residue() == x % 10 ** max(
                1, width // 2
            )
            if x:
                z = PackedQ19.from_bcd_planes(b.planes, len(str(x)))
                zref = PackedQ19.from_digits(tuple(int(d) for d in str(x)[::-1]))
                assert z == zref
                assert PackedQ19.from_two_five_carry_planes(q2, r5, len(str(x))) == z
                _result, digits = z.advance(emit_digits=True)
                assert digits is not None
                assert sum(d * 10**j for j, d in enumerate(digits)) == x + int(
                    str(x)[::-1]
                )


def test_log16_hensel_higher_precision() -> None:
    for k in range(1, 22):
        eta = log_16_of_11_mod_5_power(k)
        assert pow(16, eta, 5**k) == 11 % (5**k)
        if k > 1:
            assert eta % (5 ** (k - 2)) == log_16_of_11_mod_5_power(k - 1)


def test_mixed_exact_crt_and_successors_without_eager_exponent() -> None:
    rng = random.Random(20261114)
    for k in range(1, 15):
        for q, g in (
            (0, 0),
            (1, 0),
            (k - 1, k),
            (k, k + 1),
            (k + 1, 0),
            (10 * k, 1000),
            (rng.randint(0, 3 * k), rng.randint(0, 2500)),
        ):
            phase = Mixed211Phase.from_exponents(q, g, k)
            modulus = int(10**k)
            residue = pow(2, q, modulus) * pow(11, g, modulus) % modulus
            assert phase.residue() == residue
            for dq, dg in ((1, 0), (0, 1), (1, 1), (11, 101), (10**6, 10**6 + 73)):
                target = phase.power(dq, dg)
                assert target == Mixed211Phase.from_exponents(q + dq, g + dg, k)
                assert (
                    target.residue()
                    == (residue * pow(2, dq, 10**k) * pow(11, dg, 10**k)) % 10**k
                )


def test_cross_width_child_lift_and_ordered_matrix_shear() -> None:
    rng = random.Random(21111)
    for k in range(1, 12):
        for q, g in (
            (0, 0),
            (k - 1, 100),
            (k, 10),
            (k + 1, 17),
            (k + 20, 100),
            (rng.randrange(4 * k + 1), rng.randrange(1000)),
        ):
            phase = Mixed211Phase.from_exponents(q, g, k)
            children = phase.children()
            assert len(children) in (5, 10)
            assert phase.source_child(q, g) in children
            assert all(c.residue() % 10**k == phase.residue() for c in children)
            B = ((2, 3), (5, 7))
            lifted = ordered_child_matrices(phase, B)
            assert len(lifted) == len(children)
            for child, d, mat in lifted:
                assert mat == _matmul(((d, 1), (1, 0)), B)
                assert d == (child.residue() // 10**k)
            for c in children:
                # Each child shares all previously certified decimal columns.
                pb = BCDPlanes.from_residue(phase.residue(), k)
                cb = BCDPlanes.from_residue(c.residue(), k + 1)
                assert cb.restrict(k) == pb
                two_p, _ = pb.multiply_two()
                two_c, _ = cb.multiply_two()
                assert two_p.restrict(k) == two_c.restrict(k)
                eleven_p, _ = pb.multiply_eleven()
                eleven_c, _ = cb.multiply_eleven()
                assert eleven_p.restrict(k) == eleven_c.restrict(k)


def test_huge_temporal_phase_return_unchanged_position_masks() -> None:
    for k in (2, 3, 4, 5, 6, 10):
        t = 4 * 5 ** (k - 1)
        for n in (k, 2 * k, 10**6):
            a = Mixed211Phase.from_exponents(n, n, k)
            b = Mixed211Phase.from_exponents(n + t, n + t, k)
            assert a == b
            x = Powered211CarrySheets.from_seed(196, n, n, k)
            y = Powered211CarrySheets.from_seed(196, n + t, n + t, k)
            assert x.source == y.source
            assert x.carry_two == y.carry_two
            assert x.carry_eleven == y.carry_eleven
            assert x.power(t, t) is x  # no physical or spatial row reconstruction
            assert a.phase_period_after_saturation() == t


def test_published_stage_matches_independent_powers_and_q19() -> None:
    for x in (0, 1, 9, 196, 1212, 90009, 10**32 - 1):
        for k in (3, 8, 19, 32):
            for q, g in ((0, 0), (2, 11), (8, 13), (k + 1, 10**6)):
                pkt = Powered211CarrySheets.from_seed(x, q, g, k)
                y = (x * pow(2, q, 10**k) * pow(11, g, 10**k)) % 10**k
                assert pkt.source.residue() == y
                assert pkt.next_two.residue() == 2 * y % 10**k
                assert pkt.next_eleven.residue() == 11 * y % 10**k
                if y:
                    rev = int(str(y)[::-1])
                    assert (
                        sum(d * 10**i for i, d in enumerate(pkt.q19_next())) == y + rev
                    )


def test_invalid_ports_rejected() -> None:
    with pytest.raises(ValueError):
        BCDPlanes(3, (0, 4, 0, 4))  # BCD 10 is forbidden
    with pytest.raises(ValueError):
        BCDPlanes.from_residue(1000, 3)
    with pytest.raises(ValueError):
        Mixed211Phase.from_exponents(-1, 2, 3)
    with pytest.raises(ValueError):
        Mixed211Phase.from_exponents(1, 2, 3).source_child(4, 2)
    with pytest.raises(ValueError):
        PackedQ19.from_bcd_planes((1, 0, 0, 0), 2)


def test_powered_source_stage_and_q19_successor() -> None:
    stage = Powered211CarrySheets.from_seed(196, 10**6, 10**6, 16)
    y = 196 * pow(22, 10**6, 10**16) % 10**16
    assert stage.source.residue() == y
    digits = stage.q19_next()
    assert sum(d * 10**i for i, d in enumerate(digits)) == y + int(str(y)[::-1])


def test_both_binary_inlet_guards_and_arbitrary_future_carry_tracks() -> None:
    rng = random.Random(20261114)
    for width in (1, 2, 3, 11, 32, 65):
        for _ in range(20):
            x = rng.randrange(10**width)
            b = BCDPlanes.from_residue(x, width)
            for inlet in (0, 1):
                t, forced = b.multiply_two(inlet)
                e, carry = b.multiply_eleven(inlet)
                linear, linear_carry = b.multiply_eleven(inlet, linear_tower=True)
                assert t.residue() == 2 * x + inlet
                assert e.residue() == 11 * x + inlet
                assert (linear, linear_carry) == (e, carry)
                assert forced == b.multiplier_two_carry_on()
    for width in (1, 4, 12, 30):
        for _ in range(35):
            q, g = rng.randrange(200), rng.randrange(2000)
            seed = rng.randrange(10**width)
            sheet = Powered211CarrySheets.from_seed(seed, q, g, width)
            for dq, dg in ((0, 0), (1, 0), (0, 1), (1, 1), (20, 97), (10**6, 10**6)):
                target = sheet.power(dq, dg)
                independent = Powered211CarrySheets.from_seed(
                    seed, q + dq, g + dg, width
                )
                assert target == independent
                assert target.next_two == independent.next_two
                assert target.next_eleven == independent.next_eleven
                assert target.carry_two == independent.carry_two
                assert target.carry_eleven == independent.carry_eleven


def test_two_sheet_q19_bridge_rejects_ambiguous_or_invalid_planes() -> None:
    for x in (196, 35322452, 100001, 12345, 987654321):
        b = BCDPlanes.from_residue(x, len(str(x)))
        q, r = b.two_five_complementary_sheets()
        source = PackedQ19.from_two_five_carry_planes(q, r, len(str(x)))
        assert source == PackedQ19.from_digits(tuple(int(d) for d in str(x)[::-1]))
    with pytest.raises(ValueError, match="illegal digit"):
        PackedQ19.from_two_five_carry_planes(0, (1, 0, 1), 1)
    with pytest.raises(ValueError, match="leading zero"):
        PackedQ19.from_two_five_carry_planes(0, (0, 0, 0), 1)
    with pytest.raises(ValueError, match="binary"):
        PackedQ19.from_two_five_carry_planes(2, (1, 0, 0), 1)


def test_carry_collision_at_seed196_generations_10_11_does_not_merge_sources() -> None:
    x, y = 18211171, 35322452
    a = BCDPlanes.from_residue(x, 8)
    b = BCDPlanes.from_residue(y, 8)
    qa, ra = a.two_five_complementary_sheets()
    qb, rb = b.two_five_complementary_sheets()
    assert qa == qb == 0b1000010  # old carry-only right-class collision
    assert ra != rb  # exact complementary carry quotient separates it
    pa = PackedQ19.from_two_five_carry_planes(qa, ra, 8)
    pb = PackedQ19.from_two_five_carry_planes(qb, rb, 8)
    assert pa != pb
    _, da = pa.advance(emit_digits=True)
    _, db = pb.advance(emit_digits=True)
    assert da is not None and db is not None
    assert da != db
    assert sum(v * 10**i for i, v in enumerate(da)) == x + int(str(x)[::-1])
    assert sum(v * 10**i for i, v in enumerate(db)) == y + int(str(y)[::-1])
    with pytest.raises(ValueError, match="illegal BCD"):
        # source digits LSD-first: [10,1] is not a decimal source
        PackedQ19.from_bcd_planes((0b10, 0b01, 0, 0b01), 2)
