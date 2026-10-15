"""No-replay prime-query demand: merged source ports are never proof labels."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import replace
from typing import cast

import pytest

from number_compiler.arithmetic.fields.homogeneous_growth import (
    GrowthArithmeticEvaluator,
)
from number_compiler.arithmetic.fields.walsh import WalshH5
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.power_numbers.certificate import (
    fermat_depth_certificate,
    mersenne_depth_certificate,
)
from number_compiler.sequences.power_numbers.terminal_source_demand import (
    FOLD_TO_THRESHOLD_GAP,
    SOURCE_TO_FOLD_GAP,
    SourceTerminalDemand,
    moving_walsh_h5,
)
from number_compiler.sequences.power_numbers.terminal_threshold import (
    terminal_threshold_probe,
)


def test_terminal_queries_receive_source_bound_demand_without_replay(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.power_numbers import source_matrix

    # Prime entry creates a lazy demand, not 8 or 40 eager residues.
    def fail_if_eager(*args: object, **kwargs: object) -> None:
        raise AssertionError(
            "production query is not allowed to materialize source ports"
        )

    monkeypatch.setattr(source_matrix, "_source_residue", fail_if_eager)
    for family, p in (("fermat", 4), ("fermat", 5), ("mersenne", 11), ("mersenne", 13)):
        result = terminal_threshold_probe(family, p)
        demand = result.source_demand
        assert result.status == "UNKNOWN"
        assert type(demand) is SourceTerminalDemand
        assert demand.family == family and demand.parameter == p
        assert len(demand.last_four_source_levels) == 5
        assert demand.missing_proofs == (SOURCE_TO_FOLD_GAP, FOLD_TO_THRESHOLD_GAP)
        assert result.raw_specialization_squarings == 0
    fermat = fermat_depth_certificate(4)
    mersenne = mersenne_depth_certificate(13)
    assert fermat.status == "unknown" and SOURCE_TO_FOLD_GAP in fermat.method
    assert mersenne.status == "unknown" and SOURCE_TO_FOLD_GAP in mersenne.method


def test_fermat_five_source_level_bridge_aligns_crt_pivots_and_harmonics() -> None:
    for n, terminal_mod1000 in ((4, 761), (5, 361)):
        demand = SourceTerminalDemand.for_candidate("fermat", n)
        obs = demand.observe_fermat_sources()
        assert obs.sources[-1].level == (1 << n) - 1
        assert obs.sources[-1].crt_source % 1000 == terminal_mod1000
        assert obs.sources[-1].pivot.action_id.startswith("Q0")
        assert obs.terminal_status == "UNKNOWN"
        assert not obs.source_to_global_fold_proven
        assert not obs.signed_fold_births_authenticated
        assert obs.absolute_moving_h5 == tuple(moving_walsh_h5(p) for p in obs.sources)
        assert all(
            p.source_power_evaluations == len(p.radix_ports) for p in obs.sources
        )
        assert all(p.candidate_modulus_squarings == 0 for p in obs.sources)
        for h5 in obs.absolute_moving_h5:
            assert type(h5) is WalshH5 and h5.length_mod6 == 0


def test_absolute_pivot_walsh_matches_independent_bit_positions() -> None:
    demand = SourceTerminalDemand.for_candidate("fermat", 4)
    obs = demand.observe_fermat_sources(((2, 12), (5, 7), (10, 5)), moving_width=12)
    for packet, h5 in zip(obs.sources, obs.absolute_moving_h5, strict=True):
        moving = packet.moving_unit_xor
        assert moving is not None and h5 is not None
        absolute = packet.level + 2 + moving.unit_offset
        # Explicit sparse-character evaluation independent of the shift API.
        phi2 = a = b = 0
        for i in range(moving.width):
            if not (moving.xor_mask >> i) & 1:
                continue
            pos = absolute + i
            phi2 += -1 if pos & 1 else 1
            if pos % 3 == 0:
                a += 1
            elif pos % 3 == 1:
                b += 1
            else:
                a -= 1
                b -= 1
        assert (h5.phi2, h5.phi3_a, h5.phi3_b) == (phi2 % 5, a % 5, b % 5)


def test_collatz_radial_clock_is_the_same_three_power_homogeneous_phase() -> None:
    # The Collatz (3/2)^k and the pure 3^k leading phase are identical.
    from number_compiler.arithmetic.fields.homogeneous_growth import (
        HomogeneousGrowthScale,
    )
    from number_compiler.arithmetic.fields.radial_sturmian import RadialSturmianClock

    demand = SourceTerminalDemand.for_candidate("fermat", 4)
    assert demand.collatz_radial_clock.scale.growths == 1 << 15
    assert demand.collatz_radial_clock.scale.halvings == 1 << 15
    with GrowthArithmeticEvaluator(ResourceLedger(), max_work_units=25_000_000) as eval:
        for k in (4, 8, 16, 32):
            a = RadialSturmianClock(HomogeneousGrowthScale(k, k)).leading_binary(
                eval, 8
            )
            b = RadialSturmianClock(HomogeneousGrowthScale(k, 0)).leading_binary(
                eval, 8
            )
            assert a.prefix_value == b.prefix_value
            assert a.prefix_value == int(bin(3**k)[2:][:8].ljust(8, "0"), 2)


def test_mersenne_quadratic_trace_is_a_distinct_five_source_owner() -> None:
    for exponent in (11, 13):
        demand = SourceTerminalDemand.for_candidate("mersenne", exponent)
        obs = demand.observe_mersenne_sources()
        assert obs.terminal_status == "UNKNOWN"
        assert not obs.source_to_global_fold_proven
        assert len(obs.innovation_borrows) == 4
        # Only the finite modular trace, not candidate-modulus Lucas--Lehmer.
        for modulus_index, modulus in enumerate(obs.moduli):
            trace = 4
            reference: dict[int, int] = {}
            for t in range(demand.source_level + 1):
                reference[t] = trace % modulus
                trace = (trace * trace - 2) % modulus
            assert tuple(row[modulus_index] for row in obs.source_rows) == tuple(
                reference[t] for t in demand.last_four_source_levels
            )
        with pytest.raises(ValueError, match="Fermat"):
            demand.observe_fermat_sources()


def test_wrong_family_levels_or_forged_carry_wave_cannot_promote_prime_status() -> None:
    with pytest.raises(ValueError, match="five nonnegative source levels"):
        SourceTerminalDemand.for_candidate("fermat", 2)
    with pytest.raises(ValueError, match="five nonnegative source levels"):
        SourceTerminalDemand.for_candidate("mersenne", 5)
    f4 = SourceTerminalDemand.for_candidate("fermat", 4)
    assert f4.last_four_source_levels == (11, 12, 13, 14, 15)
    from number_compiler.sequences.power_numbers.numbers import (
        FermatNumberSpec,
        MersenneNumberSpec,
    )

    assert FermatNumberSpec(4).terminal_source_demand() == f4
    assert MersenneNumberSpec(13).terminal_source_demand() == (
        SourceTerminalDemand.for_candidate("mersenne", 13)
    )
    with pytest.raises(ValueError, match="source-aligned"):
        replace(f4, sign=1)
    with pytest.raises(ValueError, match="source-aligned"):
        replace(f4, source_level=14)
    good = f4.observe_fermat_sources(((2, 10), (5, 6)), moving_width=8)
    with pytest.raises(ValueError, match="foreign or unauthenticated"):
        replace(good, sources=good.sources[::-1])
    with pytest.raises(TypeError, match="absolute_moving_h5"):
        changes: dict[str, object] = {"absolute_moving_h5": (WalshH5.empty(),) * 5}
        unchecked_replace = cast(Callable[..., object], replace)
        unchecked_replace(good, **changes)
    with pytest.raises(ValueError, match="level budget"):
        f4.observe_fermat_sources(max_level=7)
    with pytest.raises(ValueError, match="candidate-bound and fail-closed"):
        row = terminal_threshold_probe("fermat", 4)
        replace(row, status="ALL_PASS")


def test_no_early_prime_labels_by_joint_or_signed_bare_h5() -> None:
    f5 = SourceTerminalDemand.for_candidate("fermat", 5)
    obs = f5.observe_fermat_sources(moving_width=0)
    assert obs.absolute_moving_h5 == (None,) * 5
    assert obs.terminal_status == "UNKNOWN"
    assert obs.missing_proofs[0] == SOURCE_TO_FOLD_GAP
    assert not hasattr(obs, "prime")
    assert obs.moving_unit_fold_edits() == (None,) * 5


def test_finite_crt_packets_cannot_project_the_global_fermat_remainder() -> None:
    for n in (4, 5, 6):
        evidence = SourceTerminalDemand.for_candidate(
            "fermat", n
        ).observe_fermat_sources(moving_width=0)
        one, minus_one = evidence.finite_crt_ambiguity()
        f = (1 << (1 << n)) + 1
        crt = evidence.sources[-1]
        assert one % crt.crt_modulus == minus_one % crt.crt_modulus == crt.crt_source
        assert one % f == 0
        assert minus_one % f == f - 1
        assert evidence.terminal_status == "UNKNOWN"


def test_guarded_moving_unit_xor_runs_project_to_fermat_ring_without_digits() -> None:
    # This is the actual reusable semidirect/endpoint correction from NC12.
    # It is partial: it never claims the unseen unit digits contribute zero.
    for n in (4, 5):
        obs = SourceTerminalDemand.for_candidate("fermat", n).observe_fermat_sources(
            moving_width=16
        )
        corrections = obs.moving_unit_fold_edits()
        assert len(corrections) == 5
        f = (1 << (1 << n)) + 1
        for packet, delta in zip(obs.sources, corrections, strict=True):
            window = packet.moving_unit_xor
            assert window is not None and delta is not None
            assert (
                delta
                == ((window.next_bits - window.current_bits) << window.unit_offset) % f
            )
        assert obs.terminal_status == "UNKNOWN"
