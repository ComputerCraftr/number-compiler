"""Bounded NC12 radial and multiradix source ports; no prime fallback."""

from __future__ import annotations

from dataclasses import replace

import pytest

from number_compiler.arithmetic.fields.symbolic_extent import DyadicExtent
from number_compiler.sequences.power_numbers.fermat_pumped_radial_unit import (
    FermatPumpedRadialUnit,
    PumpedSourceBudgetExceeded,
)
from number_compiler.sequences.power_numbers.numbers import FermatNumberSpec
from number_compiler.sequences.power_numbers.source_matrix import (
    FermatMultiradixPort,
    ThreePowerRadixBoundary,
)
from tests.support.fermat_pumped_oracle import literal_pumped_fermat_remainder


def test_pumped_unit_keeps_symbolic_width_and_radial_unit_lanes() -> None:
    huge_index = FermatNumberSpec(1_000_000).demand_pumped_radial_unit(1_000_000)
    assert huge_index.width_extent == DyadicExtent(1_000_000)
    assert huge_index.radial_log2 == 0
    assert not huge_index.annihilated_at_precision(16)
    with pytest.raises(PumpedSourceBudgetExceeded):
        huge_index.seed_coefficient(1)
    assert not hasattr(huge_index, "unit_seed_modulus")
    assert not hasattr(huge_index, "evaluate_for_audit")

    terminal_f4 = FermatNumberSpec(4).demand_pumped_radial_unit(15)
    assert terminal_f4.is_terminal
    assert terminal_f4.radial_log2 == 11
    assert terminal_f4.scale_modulus_symbol() == ("ONE", 1)
    assert terminal_f4.annihilated_at_precision(16)
    assert terminal_f4.coefficient_mod_power_of_two(7, bits=16) == 0


def test_pumped_seed_and_validation_oracle_are_explicitly_bounded() -> None:
    source = FermatNumberSpec(3).demand_pumped_radial_unit(3)
    assert tuple(source.seed_coefficient(j) for j in range(8)) == (
        0,
        4,
        14,
        28,
        35,
        28,
        14,
        4,
    )
    audited = FermatNumberSpec(4).demand_pumped_radial_unit(15)
    assert literal_pumped_fermat_remainder(audited) == pow(3, 1 << 15, 65_537)
    with pytest.raises(PumpedSourceBudgetExceeded):
        literal_pumped_fermat_remainder(
            FermatNumberSpec(20).demand_pumped_radial_unit((1 << 20) - 1)
        )
    with pytest.raises(PumpedSourceBudgetExceeded):
        literal_pumped_fermat_remainder(audited, max_level=14)
    with pytest.raises(ValueError):
        FermatPumpedRadialUnit(True, 1)


def test_f4_and_f5_separate_at_the_full_decimal_tripling_trit() -> None:
    f4 = FermatNumberSpec(4).demand_three_power_multiradix_port(15, 10, 3)
    f5 = FermatNumberSpec(5).demand_three_power_multiradix_port(31, 10, 3)
    b4 = f4.boundaries[-1]
    b5 = f5.boundaries[-1]
    assert (f4.source_residue, f5.source_residue) == (761, 361)
    assert (b4.tripling_carry, b4.doubling_carry) == (2, 1)
    assert (b5.tripling_carry, b5.doubling_carry) == (1, 0)
    assert b4.tripling_add_carry == b5.tripling_add_carry == 1
    assert b4.tripling_sub_borrow == b5.tripling_sub_borrow == 1
    assert b4.innovation_carry == b4.innovation_borrow
    assert b5.innovation_carry == b5.innovation_borrow
    assert f4.carry_transition_steps == 6
    assert f4.carry_monoid_sizes[0] <= 27


def test_multiradix_ports_match_bounded_integer_source_and_shared_carries() -> None:
    for base, places in ((2, 12), (5, 6), (7, 5), (10, 4), (11, 4), (13, 4), (27, 4)):
        for level in (2, 3, 5):
            port = FermatNumberSpec(4).demand_three_power_multiradix_port(
                level, base, places
            )
            modulus = base**places
            assert port.source_residue == pow(3, 1 << level, modulus)
            assert port.previous_residue == pow(3, 1 << (level - 1), modulus)
            assert port.next_residue == pow(3, 1 << (level + 1), modulus)
            for boundary in port.boundaries:
                local_modulus = base**boundary.places
                residue = port.source_residue % local_modulus
                assert boundary.tripling_carry == (3 * residue) // local_modulus
                assert boundary.doubling_carry == (2 * residue) // local_modulus
                assert boundary.tripling_add_carry == (
                    boundary.tripling_carry - boundary.doubling_carry
                )
                assert boundary.tripling_add_carry == int(
                    (3 * residue) % local_modulus < residue
                )
                assert boundary.innovation_carry == boundary.innovation_borrow


def test_multiradix_budget_and_public_record_validation_precede_work() -> None:
    spec = FermatNumberSpec(4)
    with pytest.raises(ValueError, match="multiradix-place-budget"):
        spec.demand_three_power_multiradix_port(15, 27, 10**9)
    with pytest.raises(ValueError, match="source-level-work-budget"):
        spec.demand_three_power_multiradix_port(1 << 4096, 10, 3)
    with pytest.raises(ValueError, match="level-exceeds-Fermat-source"):
        spec.demand_three_power_multiradix_port(16, 10, 3)

    port = spec.demand_three_power_multiradix_port(15, 10, 3)
    altered = replace(port.boundaries[-1], tripling_carry=1)
    with pytest.raises(ValueError, match="fields do not match"):
        FermatMultiradixPort(
            port.index,
            port.level,
            port.base,
            port.places,
            port.modulus,
            port.source_residue,
            port.previous_residue,
            port.next_residue,
            port.boundaries[:-1] + (altered,),
            port.carry_transition_steps,
            port.carry_monoid_sizes,
            port.work,
        )
    with pytest.raises(ValueError):
        ThreePowerRadixBoundary(1, 1, 3, 0, 0, 0, 0, 0, 0)
