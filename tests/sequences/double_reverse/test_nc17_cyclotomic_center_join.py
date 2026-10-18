"""Source-safe NC17 outer/inner 99/198 center and carry period join."""

from __future__ import annotations

from dataclasses import replace

import pytest

from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.source_bound_bank import (
    PointedBankSource,
    exact_temporal_bank_window,
)
from number_compiler.sequences.double_reverse.temporal_center_cyclotomic import (
    CertifiedCyclotomicCenter,
    _spatial_bank_residue,
    certified_cyclotomic_center,
    certified_cyclotomic_center_driver,
    certified_cyclotomic_center_four_return,
    certified_cyclotomic_center_program,
    cyclotomic_four_block_order,
)
from number_compiler.sequences.double_reverse.temporal_hashlife import growth_ports
from tests.support.reverse_add_source_data import double_reverse_orbit


def literal(seed: int, steps: int) -> tuple[str, ...]:
    return tuple(map(str, double_reverse_orbit(seed, steps)))


def middle(row: str) -> tuple[int, ...]:
    width = len(row)
    k = 2 if width % 2 == 0 else 1
    return tuple(int(d) for d in row[(width - k) // 2 : (width + k) // 2])


@pytest.mark.parametrize("generations", (2, 4, 6, 8))
def test_scalar_exterior_join_recovers_real_center_without_reading_it(
    generations: int,
) -> None:
    seed = int("17" + "48" * 10 + "88")
    expected = literal(seed, generations)[-1]
    exterior_pairs = (len(expected) - (1 if len(expected) % 2 else 2)) // 2
    with DoubleReverseTerm(seed, generations) as term:
        bank = term.exact_temporal_bank_window(0, exterior_pairs)
        witness = term.temporal_cyclotomic_center_join((bank,))
        assert witness.forced_center == middle(expected)
        assert witness.center_position == exterior_pairs
        assert witness.global_mod99 == int(expected) % 99
        assert witness.global_mod198 == int(expected) % 198
        assert witness.global_four_block_order == cyclotomic_four_block_order(
            int(expected) % 99, int(expected) % 198
        )
        witness.validate_source_authority()
    with pytest.raises(ValueError, match="authority"):
        witness.validate_source_authority()


@pytest.mark.parametrize("seed", (170688, 179488))
def test_mod198_does_not_invent_00_99_disambiguation(seed: int) -> None:
    actual = literal(seed, 4)[-1]
    assert middle(actual) in ((0, 0), (9, 9))
    with DoubleReverseTerm(seed, 4) as term:
        count = (len(actual) - 2) // 2
        witness = term.exact_temporal_bank_window(0, count)
        center = term.temporal_cyclotomic_center_join((witness,))
        assert set(center.candidates) == {(0, 0), (9, 9)}
        assert center.forced_center is None
        # Mod 198 sees no distinction because 99*10**count == 0 mod 198.
        assert count > 0 and 99 * pow(10, count, 198) % 198 == 0


def test_compressed_spatial_bank_joins_exact_edge_windows_without_expansion() -> None:
    seed = int("17" + "48" * 80 + "88")
    for generations in (4, 8):
        expected = literal(seed, generations)[-1]
        pair_count = (len(expected) - 2) // 2
        with DoubleReverseTerm(seed, generations, max_state_bits=8192) as term:
            first = term.exact_temporal_bank_window(0, 20)
            bank = term.temporal_bank_output_morphism(20, 40, period=2)
            last = term.exact_temporal_bank_window(60, pair_count - 60)
            assert bank.repeats == 20 and len(bank.motif) == 2
            for modulus in (99, 198):
                direct = (
                    sum(
                        (
                            bank.at(i).digits[0]
                            * pow(10, len(expected) - 1 - (20 + i), modulus)
                            + bank.at(i).digits[1] * pow(10, 20 + i, modulus)
                        )
                        for i in range(bank.pair_count)
                    )
                    % modulus
                )
                assert _spatial_bank_residue(bank, modulus) == direct
            center = term.temporal_cyclotomic_center_join((first, bank, last))
            assert center.witnessed_spans == ((0, 20), (20, 40), (60, pair_count - 60))
            assert center.forced_center == middle(expected)


def test_refuses_missing_overlap_time_mismatch_and_foreign_source() -> None:
    seed = int("17" + "48" * 12 + "88")
    with (
        DoubleReverseTerm(seed, 4) as term,
        DoubleReverseTerm(seed, 4) as other,
    ):
        left = term.exact_temporal_bank_window(0, 4)
        count = (left.width_out - 2) // 2
        right = term.exact_temporal_bank_window(4, count - 4)
        foreign = other.exact_temporal_bank_window(4, count - 4)
        assert term.temporal_cyclotomic_center_join((left, right)).forced_center
        with pytest.raises(ValueError, match="missing|over-covered|incomplete"):
            term.temporal_cyclotomic_center_join((left,))
        with pytest.raises(ValueError, match="missing|over-covered|incomplete"):
            term.temporal_cyclotomic_center_join((left, left, right))
        with pytest.raises(ValueError, match="another source"):
            term.temporal_cyclotomic_center_join((left, foreign))
        with pytest.raises(ValueError, match="authority"):
            term.temporal_cyclotomic_center_join((replace(left, phase_in=2), right))
        _entry, source = term._prepare_bank_source(max_prefix=0)
        with pytest.raises(ValueError, match="source/time"):
            certified_cyclotomic_center(
                replace(source, f_steps=1, width_out=source.width_in + 1),
                (left, right),
            )


@pytest.mark.parametrize("n", (4, 8, 12))
def test_pointed_driver_matches_literal_intermediate_centers_and_global_ring(
    n: int,
) -> None:
    seed = int("17" + "48" * 12 + "88")
    rows = literal(seed, n)
    with DoubleReverseTerm(seed, n) as term:
        block = term.temporal_cyclotomic_center_driver()
        start = block.physical_prefix + 2 * block.f_steps_start
        assert middle(rows[start]) == block.initial_pair
        assert tuple(middle(rows[start + k])[0] for k in (1, 2, 3)) == (
            block.odd_centers
        )
        assert middle(rows[start + 4]) == block.next_pair
        assert int(rows[start]) % 99 == block.source_mod99
        assert int(rows[start + 4]) % 99 == block.target_mod99
        assert int(rows[start]) % 198 == block.source_mod198
        assert int(rows[start + 4]) % 198 == block.target_mod198
        assert block.global_four_block_order == cyclotomic_four_block_order(
            block.source_mod99, block.source_mod198
        )
        assert block.band_moore_before in range(24)
        assert block.band_moore_after in range(24)
        assert not block.all_depth_period_claim
        block.validate_source_authority()


def test_four_step_join_selects_source_driver_among_all_40_letters() -> None:
    seed = int("17" + "48" * 12 + "88")
    with DoubleReverseTerm(seed, 8) as term:
        _, late = term._prepare_bank_source(max_prefix=4)
        early = replace(
            late,
            f_steps=late.f_steps - 2,
            width_out=late.width_in + sum(growth_ports(late.phase, late.f_steps - 2)),
        )

        def center(source: PointedBankSource) -> CertifiedCyclotomicCenter:
            # Explicit proof consumption; no target-integer construction.
            count = (source.width_out - 2) // 2
            bank = exact_temporal_bank_window(source, 0, count)
            return certified_cyclotomic_center(source, (bank,))

        first = center(early)
        last = center(late)
        action = certified_cyclotomic_center_four_return(first, last)
        exact = certified_cyclotomic_center_driver(late)
        assert len(action.drivers) == 1
        assert action.drivers == (exact.driver,)
        assert action.admissible[0].initial == exact.initial_pair
        assert action.admissible[0].next_pair == exact.next_pair
        assert not action.all_depth_period_claim
        action.validate_source_authority()
        with pytest.raises(ValueError, match="aligned"):
            certified_cyclotomic_center_four_return(last, first)


def test_misaligned_four_step_center_clock_refuses() -> None:
    seed = int("17" + "48" * 12 + "88")
    with (
        DoubleReverseTerm(seed, 6) as term,
        pytest.raises(ValueError, match="width clock"),
    ):
        term.temporal_cyclotomic_center_driver()


def test_certified_joint_program_composes_but_never_assumes_repeated_drivers() -> None:
    seed = int("17" + "48" * 12 + "88")
    rows = literal(seed, 12)
    with DoubleReverseTerm(seed, 12) as term:
        _, source = term._prepare_bank_source(max_prefix=8)
        assert source.phase == 0

        def at(steps: int) -> CertifiedCyclotomicCenter:
            width = source.width_in + sum(growth_ports(source.phase, steps))
            narrowed = replace(source, f_steps=steps, width_out=width)
            bank = exact_temporal_bank_window(narrowed, 0, (width - 2) // 2)
            return certified_cyclotomic_center(narrowed, (bank,))

        a, b, c = at(2), at(4), at(6)
        witness_b = certified_cyclotomic_center_driver(source, start_f_steps=2)
        witness_c = certified_cyclotomic_center_driver(source, start_f_steps=4)
        ab = certified_cyclotomic_center_four_return(a, b, driver_witness=witness_b)
        bc = certified_cyclotomic_center_four_return(b, c, driver_witness=witness_c)
        assert len(ab.admissible) == len(bc.admissible) == 1
        program = certified_cyclotomic_center_program(ab).then(
            certified_cyclotomic_center_program(bc)
        )
        program.validate_source_authority()
        initial = middle(rows[4])
        final = middle(rows[12])
        assert program.four_step_blocks == 2
        assert program.relation[10 * initial[0] + initial[1]] == 1 << (
            10 * final[0] + final[1]
        )
        assert program.global_start_mod99 == int(rows[4]) % 99
        assert program.necessary_global_return_blocks == cyclotomic_four_block_order(
            int(rows[4]) % 99, int(rows[4]) % 198
        )
        assert program.global_finish_mod99 == int(rows[12]) % 99
        assert program.power(1) is program
        with pytest.raises(ValueError, match="source-certified adjacency"):
            certified_cyclotomic_center_program(bc).then(
                certified_cyclotomic_center_program(ab)
            )
        with pytest.raises(ValueError, match="source proof"):
            program.power(100)
        assert not program.all_depth_period_claim


def test_exact_cyclotomic_orders_and_odd_198_transient() -> None:
    assert cyclotomic_four_block_order(0, 0) == 1
    assert cyclotomic_four_block_order(97, 196) == 30
    assert cyclotomic_four_block_order(1, 100) == 30
    assert cyclotomic_four_block_order(1, 1) is None
    for a in range(99):
        b = a if a % 2 == 0 else a + 99
        order = cyclotomic_four_block_order(a, b)
        assert order is not None and 30 % order == 0
        assert a * pow(61, order, 99) % 99 == a
        assert b * pow(160, order, 198) % 198 == b
        for k in range(1, order):
            assert (a * pow(61, k, 99)) % 99 != a or (b * pow(160, k, 198)) % 198 != b


@pytest.mark.parametrize("n", (20, 24, 28, 32, 64))
def test_real_seed_196_source_prefix_and_center_cyclotomic_join(n: int) -> None:
    rows = literal(196, n)
    width = len(rows[n])
    assert width % 2 == 0
    with DoubleReverseTerm(196, n) as term:
        prefix, residue = term.temporal_residue_quotient()
        assert prefix == 16 and residue.phase == 0
        assert residue.target_mod99 == int(rows[n]) % 99
        assert residue.target_mod198 == int(rows[n]) % 198
        bank = term.exact_temporal_bank_window(0, (width - 2) // 2)
        center = term.temporal_cyclotomic_center_join((bank,))
        driver = term.temporal_cyclotomic_center_driver()
        assert center.forced_center == middle(rows[n])
        assert driver.next_pair == center.forced_center
        assert driver.initial_pair == middle(rows[n - 4])
        assert not driver.all_depth_period_claim


def test_real_196_four_step_blocks_compose_without_guessing_future_1000() -> None:
    with DoubleReverseTerm(196, 32) as term:
        _, source = term._prepare_bank_source(max_prefix=28)
        assert source.physical_prefix == 16
        assert source.phase == 0
        assert source.f_steps == 8
        centers = []
        for steps in (2, 4, 6, 8):
            width = source.width_in + sum(growth_ports(source.phase, steps))
            pointed = replace(source, f_steps=steps, width_out=width)
            bank = exact_temporal_bank_window(pointed, 0, (width - 2) // 2)
            centers.append(certified_cyclotomic_center(pointed, (bank,)))
        words = []
        for i, start_steps in enumerate((2, 4, 6)):
            witness = certified_cyclotomic_center_driver(
                source, start_f_steps=start_steps
            )
            ret = certified_cyclotomic_center_four_return(
                centers[i], centers[i + 1], driver_witness=witness
            )
            assert len(ret.admissible) == 1
            words.append(certified_cyclotomic_center_program(ret))
        chained = words[0].then(words[1]).then(words[2])
        assert chained.four_step_blocks == 3
        assert chained.last.forced_center == (0, 7)
        assert chained.first.forced_center == (3, 1)
        assert chained.relation[31] == 1 << 7
        with pytest.raises(ValueError, match="source proof"):
            chained.power(2)
