"""Exact source-joined center forcing: no external inlet or repeated-driver guess."""

from __future__ import annotations

from dataclasses import replace

import pytest

from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.temporal_center_cyclotomic import (
    certified_cyclotomic_center_driver,
)
from number_compiler.sequences.double_reverse.temporal_center_power import (
    CenterForcingPower,
    centered_half_combination_mod11,
    certified_cyclotomic_center_power,
)
from number_compiler.sequences.double_reverse.temporal_center_selector import (
    CenterDriver,
    center_return,
)
from tests.sequences.double_reverse.packet_helpers import (
    integer_field,
    object_list,
    object_mapping,
    string_field,
)
from tests.support.reverse_add_source_data import double_reverse_orbit


def midpair(value: int) -> tuple[int, int]:
    w = str(value)
    assert len(w) % 2 == 0
    return int(w[len(w) // 2 - 1]), int(w[len(w) // 2])


@pytest.mark.parametrize("pair", [(0, 0), (1, 9), (6, 8), (9, 9)])
@pytest.mark.parametrize("carry", [(0, 0, 0), (1, 0, 1), (1, 1, 1)])
def test_center_forcing_is_exact_existing_driver_projection(
    pair: tuple[int, int],
    carry: tuple[int, int, int],
) -> None:
    for f5 in range(5):
        r = center_return(pair, CenterDriver(*carry, f5))
        f = 8 * int(pair[0] >= 5) + 4 * carry[0] + 2 * carry[1] + carry[2]
        assert r.right_forcing == f
        one = CenterForcingPower.from_return(r)
        assert one.weighted_mod10 == f % 10
        assert one.sum_mod5 == f % 5
        assert one.last_forcing_parity == f % 2
        assert one.right_returns == one.harmonic_return


def test_arbitrary_center_power_is_successor_closed_arithmetic_not_period() -> None:
    # Exercise arbitrary nonperiodic forcing words and the exact composition
    # ring. The forcing words need not be assigned to seed-196 source states.
    for start in range(10):
        for digits in ((0, 1, 5, 3, 7, 9), (5, 6, 3, 1, 0, 2), (8, 1, 8, 1)):
            curr = start
            sections: list[CenterForcingPower] = []
            fs: list[int] = []
            for f in digits:
                nxt = (16 * curr + f) % 10
                sections.append(CenterForcingPower.from_endpoints(curr, nxt, 1))
                fs.append(f)
                curr = nxt
            total = sections[0]
            for section in sections[1:]:
                total = total.then(section)
            assert total.blocks == len(digits)
            assert total.last_right == curr
            assert (
                total.weighted_mod10
                == sum(pow(16, len(digits) - 1 - i, 10) * v for i, v in enumerate(fs))
                % 10
            )
            assert total.sum_mod5 == sum(fs) % 5
            assert total.last_forcing_parity == fs[-1] % 2
            assert total.harmonic_return == (curr == start)


def test_certified_powered_center_matches_actual_source_seed_196_and_clock() -> None:
    orbit = double_reverse_orbit(196, 40)
    with DoubleReverseTerm(196, 40) as term:
        _, source = term.prepare_bank_source(max_prefix=24)
        assert source.physical_prefix == 16 and source.phase == 0
        whole = certified_cyclotomic_center_power(
            source,
            start_f_steps=0,
            four_step_blocks=6,
        )
        assert whole.initial_pair == midpair(orbit[16])
        assert whole.final_pair == midpair(orbit[40])
        assert whole.source_mod198 == orbit[16] % 198
        assert whole.final_mod198 == orbit[40] % 198
        first = certified_cyclotomic_center_power(
            source,
            start_f_steps=0,
            four_step_blocks=2,
        )
        second = certified_cyclotomic_center_power(
            source,
            start_f_steps=4,
            four_step_blocks=4,
        )
        composed = first.then(second)
        assert composed.forcing == whole.forcing
        assert composed.initial_pair == whole.initial_pair
        assert composed.final_pair == whole.final_pair
        assert composed.source_mod99 == whole.source_mod99
        assert composed.final_mod198 == whole.final_mod198
        assert whole.centered_half_clock_mod11["mode"] == "difference"
        assert whole.centered_half_clock_mod11["center_forcing_mod11"] == 0
        with pytest.raises(ValueError, match="source/time/clock seam"):
            second.then(first)
        with pytest.raises(ValueError, match="issued source cursor"):
            certified_cyclotomic_center_power(
                source, start_f_steps=4, four_step_blocks=5
            )
        single = certified_cyclotomic_center_power(
            source,
            start_f_steps=0,
            four_step_blocks=1,
        )
        one = certified_cyclotomic_center_driver(source, start_f_steps=0)
        assert one.right_center_forcing == single.forcing
        with pytest.raises(ValueError, match="source authority"):
            first.then(replace(second, source_mod99=(second.source_mod99 + 1) % 99))
        whole.validate_source_authority()
    with pytest.raises(ValueError, match="authority"):
        whole.validate_source_authority()


def test_term_api_returns_one_power_without_chronological_driver_loop() -> None:
    orbit = double_reverse_orbit(196, 40)
    with DoubleReverseTerm(196, 40) as term:
        result = term.temporal_cyclotomic_center_power(four_step_blocks=3)
        assert result.initial_pair == midpair(orbit[28])
        assert result.final_pair == midpair(orbit[40])
        assert result.forcing.right_returns == result.forcing.harmonic_return
        with pytest.raises(ValueError, match="target physical horizon"):
            term.temporal_cyclotomic_center_power(four_step_blocks=11)


def test_cli_center_driver_scan_projects_same_existing_source_letters() -> None:
    from number_compiler.sequences.double_reverse.temporal_seed_cli import (
        seed_morphism_cli_packet,
    )

    with DoubleReverseTerm(196, 40) as term:
        packet = seed_morphism_cli_packet(
            term,
            period_samples=4,
            period_stride=1,
            period_depth=1,
            period_max_lag=3,
            period_drivers=True,
        )
        scan = object_mapping(packet["period_observations"])
        drivers = object_mapping(scan["drivers"])
        spatial_pascal = object_mapping(scan["spatial_pascal_moments"])
        assert drivers["status"] == "available"
        assert spatial_pascal["status"] == "available"
        assert spatial_pascal["source_generation"] == 16
        assert spatial_pascal["target_generation"] == 40
        assert spatial_pascal["orientation"] == "most-significant-digit-first"
        assert spatial_pascal["modulus"] == 11
        assert spatial_pascal["order"] == 1
        assert spatial_pascal["marker"] == "digit-at-least-five"
        assert spatial_pascal["scope"] == (
            "finite exact source-issued SLP bands; no temporal repetition authority"
        )
        assert object_list(spatial_pascal["bands"])
        letters = object_list(drivers["letters"])
        trace = object_list(scan["trace"])
        right = tuple(
            int(string_field(object_mapping(row), "center")[-1]) for row in trace
        )
        power = CenterForcingPower.from_endpoints(right[0], right[-1], 3)
        power_packet = object_mapping(drivers["center_forcing_power"])
        assert power_packet == {
            "scope": "finite source-authenticated endpoint action",
            "blocks": 3,
            "weighted_mod10": power.weighted_mod10,
            "forcing_sum_mod5": power.sum_mod5,
            "last_forcing_parity": power.last_forcing_parity,
            "right_center_return": power.harmonic_return,
            "complete_center_pair_return": False,
            "centered_half_mod11": {
                "mode": "difference",
                "source": object_mapping(trace[0])["centered_half_mod11"],
                "target": object_mapping(trace[-1])["centered_half_mod11"],
                "multiplier": pow(16, 3, 11),
                "center_forcing": 0,
            },
        }
        assert (
            sum(
                integer_field(object_mapping(letter), "right_center_forcing")
                for letter in letters
            )
            % 5
            == power.sum_mod5
        )


def test_center_driver_scan_uses_one_sample_and_one_intermediate_halo_per_block(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.double_reverse.temporal_hashlife import (
        DoubleReverseTemporalHashlife,
    )
    from number_compiler.sequences.double_reverse.temporal_seed_cli import (
        seed_morphism_cli_packet,
    )

    with DoubleReverseTerm(196, 40) as term:
        _, source = term.prepare_bank_source(max_prefix=24)
        original = DoubleReverseTemporalHashlife.pointed_window
        reads: list[tuple[int, int, int]] = []

        def counted_window(
            engine: DoubleReverseTemporalHashlife,
            root: int,
            f_steps: int,
            phase: int,
            start: int,
            count: int,
        ) -> tuple[int, ...]:
            reads.append((f_steps, start, count))
            return original(engine, root, f_steps, phase, start, count)

        monkeypatch.setattr(
            DoubleReverseTemporalHashlife, "pointed_window", counted_window
        )
        packet = seed_morphism_cli_packet(
            term,
            period_samples=4,
            period_stride=1,
            period_depth=0,
            period_max_lag=3,
            period_drivers=True,
        )
        scan = object_mapping(packet["period_observations"])
        scanned_reads = len(reads)
        trace = object_list(scan["trace"])
        drivers = object_mapping(scan["drivers"])
        assert drivers["status"] == "available"
        assert "spatial_pascal_moments" not in scan
        assert scanned_reads == 2 * len(trace) - 1
        assert all(count == 4 for _f_steps, _start, count in reads[:scanned_reads])
        for index, raw_letter in enumerate(object_list(drivers["letters"])):
            letter = object_mapping(raw_letter)
            sample_generation = integer_field(
                object_mapping(trace[index]), "generation"
            )
            start_f = (sample_generation - source.physical_prefix) // 2
            witness = certified_cyclotomic_center_driver(source, start_f_steps=start_f)
            assert letter["incoming_carries"] == [
                witness.driver.left_1,
                witness.driver.left_2,
                witness.driver.left_3,
            ]
            assert letter["right_f5"] == witness.driver.right_f5
            assert letter["right_center_forcing"] == (
                witness.right_center_forcing.weighted_mod10
            )
            assert letter["odd_center_digits"] == list(witness.odd_centers)


def test_odd_width_center_seed168_reuses_same_diagonal_forcing() -> None:
    orbit = double_reverse_orbit(168, 40)
    with DoubleReverseTerm(168, 40) as term:
        _, source = term.prepare_bank_source(max_prefix=24)
        assert source.phase == 0 and source.width_in % 2 == 1
        for start_f in range(0, source.f_steps - 1, 2):
            r = certified_cyclotomic_center_power(
                source,
                start_f_steps=start_f,
                four_step_blocks=1,
            )
            i = source.physical_prefix + 2 * start_f
            j = i + 4
            assert len(r.initial_pair) == len(r.final_pair) == 1
            assert r.initial_pair == (int(str(orbit[i])[len(str(orbit[i])) // 2]),)
            assert r.final_pair == (int(str(orbit[j])[len(str(orbit[j])) // 2]),)
            assert r.forcing.right_returns == r.forcing.harmonic_return
        powered = term.temporal_cyclotomic_center_power(four_step_blocks=3)
        assert powered.initial_pair == (int(str(orbit[28])[len(str(orbit[28])) // 2]),)
        assert powered.final_pair == (int(str(orbit[40])[len(str(orbit[40])) // 2]),)
        assert powered.centered_half_clock_mod11["mode"] == "sum"


def test_power_factory_refuses_unsourced_repetition_and_misaligned_phase() -> None:
    with DoubleReverseTerm(1, 40) as term:
        _, source = term.prepare_bank_source(max_prefix=24)
        with pytest.raises(ValueError, match="width clock"):
            certified_cyclotomic_center_power(
                source, start_f_steps=0, four_step_blocks=1
            )
    with pytest.raises(ValueError, match="exact affine endpoint cocycle"):
        CenterForcingPower(2, 1, 2, 0, 0, 0)


@pytest.mark.parametrize("seed", (168, 196))
def test_joined_centered_half_mod11_matches_user_overlapping_slices(seed: int) -> None:
    orbit = double_reverse_orbit(seed, 256)
    for x in orbit:
        s = str(x)
        width = len(s)
        if width < 2:
            continue
        first = int(s[: (width + 1) // 2])
        second = int(s[width // 2 :][::-1])
        center_width = 1 if width % 2 else 2
        center = tuple(
            int(d) for d in s[(width - center_width) // 2 : (width + center_width) // 2]
        )
        mode, projected = centered_half_combination_mod11(width, center, x % 99)
        assert mode == ("sum" if width % 2 else "difference")
        assert projected == ((first + second if width % 2 else first - second) % 11)
