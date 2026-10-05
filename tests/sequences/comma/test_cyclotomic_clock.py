"""Independent CRT and physical-power checks for the external selector."""

from __future__ import annotations

import pytest

from number_compiler.sequences.comma.arithmetic import (
    CycleTransfer,
    cycle_power_residue,
    cycle_transfer,
    entry_headroom,
    entry_headroom_from_transfer,
)
from number_compiler.sequences.comma.cyclotomic_clock import CyclotomicClock


def test_clock_projects_every_phase_without_endpoint_rows() -> None:
    for phase in range(924):
        clock = CyclotomicClock.from_phase(phase)
        for period in (1, 2, 3, 6, 22, 28):
            for shift in (-929, -5, 0, 1, 919, 924, 1849):
                assert clock.phase(period, shift=shift) == (phase + shift) % period
        assert clock == CyclotomicClock.from_phase(phase + 924)


def test_clock_core_lift_matches_actual_decimal_power() -> None:
    displacements = {
        cycle_transfer(f, d).displacement for f in range(1, 10) for d in range(10)
    }
    assert len(displacements) == 17
    for phase in range(924):
        clock = CyclotomicClock.from_phase(phase)
        for displacement in displacements:
            assert cycle_power_residue(displacement, clock) == pow(
                10, phase + 924, displacement
            )


def test_same_local_character_does_not_erase_external_clock() -> None:
    first = CyclotomicClock.from_phase(0)
    other = CyclotomicClock.from_phase(22)
    assert first.phase(22) == other.phase(22)
    assert first.phase(28) != other.phase(28)
    assert first != other


def test_shifted_entry_clock_uses_receiving_exponent() -> None:
    for leading in range(1, 10):
        for offset in (0, 89 + leading):
            for phase in (0, 1, 22, 28, 923):
                for delta in (0, 1, 5, 924, 10**9):
                    transfer, headroom = entry_headroom(
                        leading,
                        offset,
                        CyclotomicClock.from_phase(phase),
                        exponent_delta=delta,
                    )
                    extra = int(leading < 9)
                    power = pow(10, phase + 924 + delta, transfer.displacement)
                    assert (
                        headroom
                        == 1
                        + extra
                        + (power - offset - 1 - extra) % transfer.displacement
                    )


def test_entry_headroom_reuses_only_a_matching_transfer() -> None:
    for leading in range(1, 10):
        coordinate = 89 + leading
        transfer = cycle_transfer(leading, coordinate % 10)
        for phase in (0, 1, 22, 28, 923):
            assert (
                entry_headroom_from_transfer(leading, coordinate, phase, transfer)
                == entry_headroom(leading, coordinate, phase)[1]
            )

    with pytest.raises(ValueError, match="another entering cylinder"):
        entry_headroom_from_transfer(2, 20, 0, cycle_transfer(2, 1))
    with pytest.raises(ValueError, match="phase arithmetic"):
        entry_headroom_from_transfer(2, 20, 0, CycleTransfer(2, 0, 5, 121, 122))


@pytest.mark.parametrize("characters", [(4, 0, 0, 0), (0, -1, 0, 0), (True, 0, 0, 0)])
def test_clock_rejects_noncanonical_characters(
    characters: tuple[int, int, int, int],
) -> None:
    with pytest.raises(ValueError):
        CyclotomicClock(*characters)


@pytest.mark.parametrize("period", [0, 4, 7, 11, 924, True])
def test_clock_rejects_unadmitted_core_projection(period: int) -> None:
    with pytest.raises(ValueError):
        CyclotomicClock.from_phase(0).phase(period)
