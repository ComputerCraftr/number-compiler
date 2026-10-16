"""Exact/source-guarded NC16 Mahler harmonic-ring cutover regression controls."""

from __future__ import annotations

import json
from collections.abc import Mapping
from dataclasses import replace
from itertools import pairwise

import pytest

import number_compiler.sequences.antihydra.mahler_harmonic_ring as ring_module
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.functions.finite_observer import (
    MAX_FINITE_ORBIT_STATES,
)
from number_compiler.sequences.antihydra.mahler_harmonic_ring import (
    MahlerFixedOddHarmonicRing as Ring,
)
from number_compiler.sequences.antihydra.mahler_harmonic_ring import (
    OpenMahlerRingInletsRequired,
)
from number_compiler.sequences.antihydra.mahler_odd_macro import (
    odd_seam_packet,
    odd_seam_step,
)
from number_compiler.sequences.antihydra.mahler_open_harmonic_moore import (
    MahlerConditionalOpenMoore as Moore,
)
from number_compiler.sequences.antihydra.mahler_open_harmonic_moore import (
    _entry,
)
from tests.support.mahler_harmonic_reference import literal_q_harmonic_counts


def _mapping(value: object) -> Mapping[object, object]:
    assert isinstance(value, Mapping)
    return value


def _literal(source: int, exponent: int, count: int) -> tuple[int, ...]:
    out = [source]
    for _ in range(count):
        assert (
            source & 1
            and ((3 * source + 1) & -(3 * source + 1)).bit_length() - 1 == exponent
        )
        source = 3 ** (exponent - 1) * ((3 * source + 1) >> exponent)
        assert source & 1
        out.append(source)
    return tuple(out)


def _source_for_deep_cone(exponent: int, copies: int, extra: int = 12) -> int:
    bits = exponent * copies + extra
    # Extend the unique Hensel root beyond the basic odd-seam guard.
    p, q, j = 3**exponent, 1 << exponent, 3 ** (exponent - 1)
    source: int = j * pow(q - p, -1, 1 << bits) % (1 << bits)
    assert source % 2 == 1
    return source


def test_fixed_run_source_capacity_and_exact_endpoint_all_small_odds() -> None:
    for source in range(1, 2500, 2):
        ring = Ring.from_source(source)
        horizon = min(ring.capacity, 12)
        reference = _literal(source, ring.exponent, horizon)
        assert ring.capacity == (ring.defect_valuation - 1) // ring.exponent
        for count in range(horizon + 1):
            assert ring.endpoint(count) == reference[count]
            for base, places in ((2, 4), (3, 3), (5, 3), (6, 2), (10, 3), (64, 2)):
                assert ring.radix_residue(base, places, count) == reference[count] % (
                    base**places
                )
            if count:
                r, m = Ring.source_cylinder(ring.exponent, count)
                assert source % m == r
        if ring.capacity < 12:
            assert not ring.admits(ring.capacity + 1)
            with pytest.raises(ValueError):
                ring.radix_residue(10, 1, ring.capacity + 1)


def test_moore_open_bank_matches_exact_pointed_source_and_all_input_transitions() -> (
    None
):
    for source in (1, 3, 7, 9, 13, 15, 31, 63, 127):
        ring = Ring.from_source(source)
        b = max(4, ring.exponent + 1)
        model = Moore.compile(ring, binary_bits=b, five_places=1)
        assert 1 <= model.class_count <= len(model.states)
        for idx, state in enumerate(model.states):
            cls_id = model.class_ids[idx]
            for inlet in model.alphabet:
                actual = _entry(ring, state, inlet, bits=b, places=1, position=0)
                target = model.transitions[cls_id][inlet]
                emission = model.outputs[cls_id][inlet]
                if actual is None:
                    assert target is None and emission is None
                else:
                    next_state, obs = actual
                    assert target == model.class_ids[model.states.index(next_state)]
                    assert emission == obs
        count = min(ring.capacity, 10)
        end_class, counts, mode = model.source_certified_path(ring, count)
        assert end_class < model.class_count
        assert mode in ("literal-source-certified-inlets", "constant-inlet-source-cone")
        reference = _literal(source, ring.exponent, count)
        assert sum(counts[:6]) % 5 == sum((s % 10) % 5 for s in reference[1:]) % 5
        with pytest.raises(ValueError):
            model.letter(1 << ring.exponent)
        with pytest.raises(ValueError):
            model.source_certified_path(Ring.from_source(source + 2), count)


def test_long_source_cone_powers_harmonics_without_walk() -> None:
    for exponent, copies in ((1, 160), (2, 96), (3, 70)):
        source = _source_for_deep_cone(exponent, copies)
        ring = Ring.from_source(source)
        assert ring.exponent == exponent and ring.capacity >= copies
        reference = _literal(source, exponent, copies)
        spec = ring.position_spectrum(10, 0, copies, walsh64=True)
        assert spec.period > 0
        assert spec.digit_counts == tuple(
            sum(s % 10 == d for s in reference[:-1]) for d in range(10)
        )
        assert spec.phase_f5 == tuple(
            sum((s % 10) for i, s in enumerate(reference[:-1]) if i % 6 == phase) % 5
            for phase in range(6)
        )
        assert spec.walsh64_parity is not None and len(spec.walsh64_parity) == 64
        moore = Moore.compile(ring, binary_bits=max(4, exponent + 1), five_places=1)
        _, counts, mode = moore.source_certified_path(ring, copies)
        assert mode == "constant-inlet-source-cone"
        assert sum(counts[:6]) % 5 == sum((s % 10) % 5 for s in reference[1:]) % 5
        assert (
            ring.action(min(copies, 32)).advance(source, 0)[0]
            == reference[min(copies, 32)]
        )


def test_unproved_period_and_false_moore_repeat_are_refused() -> None:
    ring = Ring.from_source(7)
    with pytest.raises(OpenMahlerRingInletsRequired):
        ring.position_spectrum(10, 1, 2)
    with pytest.raises(ValueError):
        ring.action(ring.capacity + 1)
    model = Moore.compile(ring, binary_bits=4, five_places=1)
    with pytest.raises(BlockContextBudgetExceeded):
        model.source_certified_path(ring, 2, max_discovery=0)
    with pytest.raises(ValueError):
        model.letter(0).then(
            Moore.compile(ring, binary_bits=5, five_places=1).letter(0)
        )
    with pytest.raises(ValueError):
        Ring.from_source(2)


@pytest.mark.parametrize(
    ("max_states", "error"),
    (
        (True, ValueError),
        (0, ValueError),
        (MAX_FINITE_ORBIT_STATES + 1, BlockContextBudgetExceeded),
    ),
)
def test_harmonic_spectrum_state_budgets_are_checked_before_orbit_work(
    max_states: int | bool,
    error: type[Exception],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ring = Ring.from_source(7)

    def unexpected_power(*_args: object) -> int:
        raise AssertionError("over-budget request reached orbit arithmetic")

    monkeypatch.setattr(ring_module, "pow", unexpected_power, raising=False)
    with pytest.raises(error):
        ring.position_spectrum(5, 0, 1, max_states=max_states)
    with pytest.raises(error):
        ring.q_phase_spectrum(3, 1, 1, clock=0, max_states=max_states)


def test_public_mahler_packet_demand_has_source_bound_ring_and_json_keys() -> None:
    source = 7
    step = odd_seam_step(source, 0, 0, 0)
    packet = odd_seam_packet(step, bits=8, decimal_places=3, walsh=False)
    ring = _mapping(packet["source_bound_harmonic_ring"])
    assert ring["fixed_exponent"] == 1
    assert ring["certified_capacity"] == 2
    assert ring["powered_copies"] == 2
    assert ring["powered_endpoint"] == 17
    assert ring["fractional_guard_empty"] is True
    open_bank = _mapping(ring["conditional_open_bank"])
    radix_endpoint = _mapping(ring["radix_endpoint"])
    decimal = _mapping(ring["decimal_position_zero"])
    assert open_bank["future_moore_classes"] == 3
    assert radix_endpoint["10"] == 17
    assert decimal["mode"] == "closed_binary_cone"
    json.dumps(packet)


def test_nested_odd_packet_projects_only_its_authenticated_endpoint() -> None:
    seam = odd_seam_step(7, 0, 0, 0)
    packet = odd_seam_packet(seam, bits=8, decimal_places=3, walsh=False)
    harmonics = _mapping(packet["harmonics"])
    q_ports = _mapping(packet["q_radix_orbits"])
    ring = _mapping(packet["source_bound_harmonic_ring"])

    assert packet["source"] == seam.source == 7
    assert packet["source_clock"] == seam.clock == 0
    assert packet["next_odd_source"] == seam.next_source == 11
    assert packet["next_clock"] == seam.next_clock == 1
    assert packet["next_balance"] == seam.ending_balance == 2
    assert harmonics["source_residue"] == packet["pointed_source_residue"]
    assert harmonics["source_modulus"] == packet["pointed_source_modulus"]
    assert harmonics["endpoint"] == seam.next_source
    assert harmonics["binary_endpoint"] == seam.next_source % 2**8
    assert harmonics["five_endpoint"] == seam.next_source % 5**3
    assert harmonics["decimal_endpoint"] == seam.next_source % 10**3
    assert harmonics["all_time_claim"] is False
    assert "binary_next" not in harmonics
    assert "decimal_next" not in harmonics
    assert q_ports["source_clock"] == seam.clock
    assert q_ports["odd_index"] == seam.index
    assert (
        q_ports["base_10_crt"] == ((1 << seam.next_clock) * (seam.next_x + 1)) % 10**3
    )
    assert ring["fixed_exponent"] == seam.exponent
    copies = ring["powered_copies"]
    assert type(copies) is int
    source_ring = Ring.from_source(seam.source)
    powered = source_ring.action(copies)
    assert ring["source_guard_residue"] == powered.source_residue
    assert ring["powered_endpoint"] == source_ring.endpoint(copies)


@pytest.mark.parametrize(
    ("field", "value"),
    (
        ("clock", 1),
        ("x", 24),
        ("q_valuation", 2),
        ("required_valuation", 1),
        ("barrier_fails", True),
    ),
)
def test_nested_odd_packet_rejects_forged_seam_fields(
    field: str, value: int | bool
) -> None:
    seam = odd_seam_step(7, 0, 0, 0)
    forged = replace(seam)
    object.__setattr__(forged, field, value)
    with pytest.raises(ValueError, match="canonical odd-seam fields|source recurrence"):
        odd_seam_packet(forged, bits=8, decimal_places=3, walsh=False)
    with pytest.raises(ValueError, match="canonical fields|source recurrence"):
        forged.demanded_q_ports(places=3)


def test_q_temporal_prime_rings_match_exact_q_recursion_and_phase_counts() -> None:
    for source in range(1, 256, 2):
        ring = Ring.from_source(source)
        copies = min(6, ring.capacity)
        reference = _literal(source, ring.exponent, copies)
        for clock in (0, 13):
            for radix in (3, 5, 7):
                places = 3
                sp = ring.q_phase_spectrum(radix, places, copies, clock=clock)
                events = (
                    (
                        2 ** (clock + i * ring.exponent) * (3 * here + 1),
                        2 ** (clock + (i + 1) * ring.exponent) * (3 * following + 1),
                        clock + i * ring.exponent,
                        ring.exponent,
                    )
                    for i, (here, following) in enumerate(pairwise(reference))
                )
                expected = literal_q_harmonic_counts(events, radix=radix, places=places)
                assert sp.carry_phase_counts == expected[0]
                assert sp.borrow_phase_counts == expected[1]
                assert sp.xor_phase_counts == expected[2]
                assert sp.xor_f5 == tuple(
                    sum(expected[2][j][p] for j in range(places)) % 5 for p in range(6)
                )


def test_large_q_ring_walsh_is_source_derived_not_assumed_periodic() -> None:
    from number_compiler.arithmetic.fields.walsh import walsh64_mod5

    source = _source_for_deep_cone(2, 130)
    ring = Ring.from_source(source)
    assert ring.capacity >= 130
    horizon = 130
    spec = ring.q_phase_spectrum(5, 2, horizon, clock=211, walsh64=True)
    reference = _literal(source, 2, horizon)
    for bit in range(2):
        mask = 0
        for i, (here, following) in enumerate(pairwise(reference[:65])):
            modulus = 5 ** (bit + 1)
            now = pow(2, 211 + 2 * i, modulus) * (3 * here + 1) % modulus
            after = pow(2, 211 + 2 * i + 2, modulus) * (3 * following + 1) % modulus
            product = 9 * now % modulus
            summand = pow(2, 211 + 2 * i + 2, modulus)
            carry = int(product + summand >= modulus)
            borrow = int(after < now)
            mask |= (carry ^ borrow) << i
        assert spec.walsh64_xor is not None
        assert spec.walsh64_xor[bit] == walsh64_mod5(mask)
    with pytest.raises(ValueError):
        ring.q_phase_spectrum(10, 2, 5, clock=0)


def test_conditional_moore_is_reused_by_crt_class_not_reused_inlet_word() -> None:
    a, b = Ring.from_source(7), Ring.from_source(87)
    assert a.exponent == b.exponent == 1 and a.capacity >= 2 and b.capacity >= 2
    moore_a = Moore.compile(a, binary_bits=4, five_places=1)
    moore_b = Moore.compile(b, binary_bits=4, five_places=1)
    assert moore_a is not moore_b  # independently owned, source-bound compilations
    assert moore_a.class_count == moore_b.class_count
    assert moore_a.transitions == moore_b.transitions
    assert moore_a.outputs == moore_b.outputs
    assert a.inlet(0, 4) != b.inlet(0, 4)
    target_a, counts_a, _ = moore_a.source_certified_path(a, 2)
    target_b, counts_b, _ = moore_b.source_certified_path(b, 2)
    assert 0 <= target_a < moore_a.class_count and 0 <= target_b < moore_b.class_count
    assert (
        counts_a == counts_b
    )  # allowed output equivalence can merge distinct integers
    assert a.endpoint(2) != b.endpoint(2)
