"""NC16 odd-run barrier, powered source guards and shared carry/CRT proofs."""

from __future__ import annotations

from collections.abc import Callable, Mapping
from random import Random
from typing import cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.consumer_pullback import ExactRational
from number_compiler.sequences.antihydra import mahler_action as mahler_action_module
from number_compiler.sequences.antihydra.mahler_action import associated_action
from number_compiler.sequences.antihydra.mahler_joint_future import (
    MahlerJointFutureAction,
)
from number_compiler.sequences.antihydra.mahler_odd_macro import (
    MahlerOddToOddAction as Odd,
)
from number_compiler.sequences.antihydra.mahler_odd_macro import (
    odd_seam_pointwise_packet,
    odd_seam_step,
)
from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm


def _mapping(value: object) -> Mapping[object, object]:
    assert isinstance(value, Mapping)
    return value


def _literal(
    source: int, exponent: int, balance: int
) -> tuple[int, int, int, tuple[int, ...]]:
    lowest = balance
    word = []
    for _ in range(exponent):
        epsilon = source & 1
        word.append(epsilon)
        balance += 2 if epsilon else -1
        lowest = min(lowest, balance)
        source = (3 * source + epsilon) // 2
    return source, balance, lowest, tuple(word)


def test_macro_lte_first_hole_and_pointed_boundary_are_exact() -> None:
    for source in range(1, 1500, 2):
        x = 3 * source
        exponent = ((x + 1) & -(x + 1)).bit_length() - 1
        action = Odd.run(exponent)
        assert action.integer_admits(source)
        end, balance, minimum, word = _literal(source, exponent, 0)
        assert word == (1,) + (0,) * (exponent - 1)
        assert end & 1
        assert action.advance(source, 0) == (end, balance)
        assert action.minimum == minimum
        assert (
            action.joint.gain * source + action.joint.innovation
        ) == end * 2**exponent
        assert 3 * end == 3**exponent * ((x + 1) >> exponent)
        assert (
            source + action.source_modulus
        ) % action.source_modulus == action.source_residue


def test_one_extra_odd_seam_bit_cannot_be_omitted() -> None:
    action = Odd.run(1)
    assert action.joint.integer_admits(1)  # follows finite word '1'
    assert not action.integer_admits(1)  # but ends EVEN at step 1
    assert action.integer_admits(3)  # ends odd
    assert action.source_modulus == 4
    assert action.source_residue == 3
    assert Odd.identity().source_residue == 1
    assert Odd.identity().integer_admits(7)
    assert not Odd.identity().integer_admits(8)


def test_direct_odd_action_cannot_admit_even_source_on_its_joint_fiber() -> None:
    even_branch = MahlerJointFutureAction.bit(0)
    assert even_branch.integer_admits(2)
    constructor = cast(Callable[..., object], Odd)
    with pytest.raises(TypeError):
        constructor(even_branch, odd_events=1, delta=2, minimum=0)

    # The odd-to-odd factory adds the authenticated terminal parity bit.
    action = Odd.run(1)
    assert action.joint.integer_admits(1)
    assert not action.integer_admits(1)
    assert action.integer_admits(3)


def test_odd_action_seal_detects_nested_guard_and_safety_mutation() -> None:
    action = Odd.run(2)
    guard = action.joint.guard
    original_lower = guard.lower
    try:
        object.__setattr__(
            guard,
            "lower",
            ExactRational(original_lower.numerator + 1, original_lower.denominator),
        )
        with pytest.raises(ValueError, match="unchanged factory result"):
            action.integer_admits(action.source_residue)
    finally:
        object.__setattr__(guard, "lower", original_lower)

    safety = action.joint.safety
    original_offset = safety.offset_hat
    try:
        object.__setattr__(safety, "offset_hat", original_offset + 1)
        with pytest.raises(ValueError, match="unchanged factory result"):
            action.integer_admits(action.source_residue)
    finally:
        object.__setattr__(safety, "offset_hat", original_offset)

    original_minimum = action.minimum
    try:
        object.__setattr__(action, "minimum", False)
        with pytest.raises(ValueError, match="unchanged factory result"):
            action.integer_admits(action.source_residue)
        with pytest.raises(ValueError, match="unchanged factory result"):
            action.power(0)
    finally:
        object.__setattr__(action, "minimum", original_minimum)


def test_q_formula_and_barrier_valuation_recurrence_on_source_seven() -> None:
    source, clock, balance, q = 7, 0, 0, 22
    times = []
    for index in range(85):
        times.append(clock)
        step = odd_seam_step(source, index, clock, balance)
        explicit = 21 * 3**clock + sum((1 << k) * 3 ** (clock - k) for k in times)
        assert q == explicit == (1 << clock) * (3 * source + 1)
        assert step.q_valuation == ((q & -q).bit_length() - 1)
        assert step.barrier_fails == (q % (1 << (3 * index + 4)) == 0)
        assert step.barrier_fails == (step.exponent >= balance + 4)
        assert step.ending_balance == balance + 3 - step.exponent
        assert step.next_clock == clock + step.exponent
        q_next = 3**step.exponent * q + (1 << step.next_clock)
        assert q_next == (1 << step.next_clock) * (step.next_x + 1)
        q = q_next
        source, clock, balance = step.next_source, step.next_clock, step.ending_balance


def test_first_barrier_on_source_five_is_not_mahler_margin() -> None:
    step = odd_seam_step(5, 0, 0, 0)
    assert step.exponent == 4
    assert step.q_valuation == step.required_valuation == 4
    assert step.barrier_fails
    assert step.ending_balance == -1
    assert step.next_source == 27
    action = Odd.run(4)
    assert action.minimum == -1
    assert action.advance(5, 0) == (27, -1)
    with pytest.raises(ValueError):
        action.apply(5, 0)
    assert action.apply(5, 1) == (27, 0)
    # Genuine Mahler fractional safety can fail even when the ledger doesn't.
    from number_compiler.sequences.antihydra.mahler_joint_future import (
        MahlerJointFutureAction,
    )

    assert MahlerJointFutureAction.from_source_prefix(7, 2).guard.empty
    assert odd_seam_step(7, 0, 0, 0).ending_balance == 2


def test_repeated_and_composed_odd_source_guards_and_ledger() -> None:
    for exponent in range(1, 6):
        a = Odd.run(exponent)
        for repetitions in (0, 1, 2, 3, 4, 8, 16):
            powered = a.power(repetitions)
            literal = Odd.identity()
            for _ in range(repetitions):
                literal = literal.then(a)
            assert powered == literal
            source = powered.source_residue
            assert powered.integer_admits(source)
            cur, balance, minimum = source, 0, 0
            for _ in range(repetitions):
                assert ((3 * cur + 1) & -(3 * cur + 1)).bit_length() - 1 == exponent
                cur, balance, level, word = _literal(cur, exponent, balance)
                minimum = min(minimum, level)
                assert word == (1,) + (0,) * (exponent - 1)
            assert powered.advance(source, 0) == (cur, balance)
            assert powered.minimum == minimum
            assert powered.odd_events == repetitions
    r = Random(160016)
    for _ in range(80):
        a, b, c = (Odd.run(r.randrange(1, 9)) for _ in range(3))
        assert a.then(b).then(c) == a.then(b.then(c))


def test_q_multiradix_orbit_recurrence_carries_and_decimal_crt() -> None:
    source, clock, balance = 7, 0, 0
    for index in range(30):
        step = odd_seam_step(source, index, clock, balance)
        observation = step.demanded_q_ports(places=6)
        qi = (1 << clock) * (3 * source + 1)
        qj = (1 << step.next_clock) * (step.next_x + 1)
        assert observation["base_10_crt"] == qj % 10**6
        ports = _mapping(observation["radix_ports"])
        for base in (2, 5, 10):
            data = _mapping(ports[base])
            modulus = base**6
            assert data["q_initial"] == qi % modulus
            assert data["q_next"] == qj % modulus
            carries = borrows = 0
            for j in range(1, 7):
                m = base**j
                left = pow(3, step.exponent, m) * (qi % m) % m
                right = pow(2, step.next_clock, m)
                carries |= int(left + right >= m) << (j - 1)
                borrows |= int(qj % m < qi % m) << (j - 1)
            assert data["carry_mask"] == carries
            assert data["difference_borrow_mask"] == borrows
            assert data["carry_borrow_xor"] == (carries ^ borrows)
        source, clock, balance = step.next_source, step.next_clock, step.ending_balance
    walsh_ports = _mapping(
        odd_seam_step(7, 0, 0, 0).demanded_q_ports(places=3, walsh=True)["radix_ports"]
    )
    walsh_at_64 = _mapping(walsh_ports[64])["walsh64_mod5"]
    assert isinstance(walsh_at_64, tuple) and len(walsh_at_64) == 64


def test_joint_boolean_harmonics_source_authentication() -> None:
    for exponent in (1, 2, 3, 4, 7):
        action = Odd.run(exponent)
        source = action.source_residue + 5 * action.source_modulus
        packet = action.demanded_harmonics(source, bits=18, decimal_places=5, places=4)
        endpoint = action.joint.endpoint(source)
        assert packet["binary_next"] == ((3 * endpoint + (endpoint & 1)) // 2) % (
            1 << 18
        )
        assert packet["decimal_next"] == ((3 * endpoint + (endpoint & 1)) // 2) % 10**5
        assert packet["five_next"] == ((3 * endpoint + (endpoint & 1)) // 2) % 5**5
        assert packet["balance_delta"] == 3 - exponent
        assert packet["radial_scale"] == (exponent, exponent)
        assert set(_mapping(packet["radix_ports"])) == {2, 5, 10}
        binary_h5 = packet["binary_counter_h5"]
        assert isinstance(binary_h5, tuple) and len(binary_h5) == 2
        assert packet["all_time_claim"] is False
        with pytest.raises(ValueError):
            action.demanded_harmonics(source + (1 << exponent))


def test_pointed_source_gate_matches_literal_run_and_rejects_last_bit_aliases() -> None:
    for exponent in range(1, 9):
        action = Odd.run(exponent)
        for lift in range(4):
            source = action.source_residue + lift * action.source_modulus
            end, balance, minimum, word = _literal(source, exponent, 0)
            assert word == (1,) + (0,) * (exponent - 1)
            assert action.integer_admits(source)
            assert action.advance(source, 0) == (end, balance)
            assert action.minimum == minimum

            # The first a bits still select the same finite word, but changing
            # its pointed endpoint bit makes the next odd seam unauthorized.
            wrong_endpoint = source ^ (1 << exponent)
            assert action.joint.integer_admits(wrong_endpoint)
            assert not action.integer_admits(wrong_endpoint)


def test_production_api_odd_seam_packet_is_demand_only_and_authenticated() -> None:
    for n in range(20):
        result = AntihydraArithmeticTerm(n, shared_cache=False).result()
        normal = associated_action(result)
        assert "source_bound_odd_to_odd" not in normal
        packet = associated_action(result, include_radix_ports=True)
        if (result.h - 1) & 1 == 0:
            assert "source_bound_odd_to_odd" not in packet
            continue
        odd = _mapping(packet["source_bound_odd_to_odd"])
        step = odd_seam_step(result.h - 1, result.odd_events, n, result.balance)
        assert odd["run_exponent"] == step.exponent
        assert odd["source"] == result.h - 1
        assert odd["next_odd_source"] == step.next_source
        assert odd["next_balance"] == step.ending_balance
        assert odd["q_valuation"] == step.q_valuation
        assert odd["required_q_valuation"] == step.required_valuation
        assert odd["barrier_failure_next_macro"] == step.barrier_fails
        q_orbits = _mapping(odd["q_radix_orbits"])
        if result.returns == 0:
            harmonics = _mapping(odd["harmonics"])
            assert (
                q_orbits["base_10_crt"]
                == ((1 << step.next_clock) * (step.next_x + 1)) % 10000
            )
            assert harmonics["source_modulus"] == odd["pointed_source_modulus"]
            assert harmonics["endpoint"] == step.next_source
            assert not odd["all_time_claim"]
        else:
            assert "harmonics" not in odd
            assert "source_bound_harmonic_ring" not in odd
            assert set(q_orbits) == {"2", "3", "5", "6", "10", "64"}
            for radix in (2, 3, 5, 6, 10, 64):
                row = _mapping(q_orbits[str(radix)])
                assert (
                    row["q_initial"]
                    == (1 << step.clock) * (3 * step.source + 1) % radix**4
                )
                assert (
                    row["q_next"]
                    == (1 << step.next_clock) * (step.next_x + 1) % radix**4
                )


def test_pointwise_barrier_packet_is_exact_but_does_not_build_future_observers(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.antihydra import mahler_odd_macro

    step = odd_seam_step(7, 0, 0, 0)

    def forbidden(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("pointwise barrier demand built a repeated-event observer")

    monkeypatch.setattr(mahler_odd_macro, "odd_seam_packet", forbidden)
    packet = odd_seam_pointwise_packet(step, places=4)
    assert packet["source"] == 7
    assert packet["odd_index"] == 0
    assert packet["source_clock"] == 0
    assert packet["incoming_balance"] == 0
    assert packet["run_exponent"] == 1
    assert packet["next_odd_source"] == 11
    assert packet["next_clock"] == 1
    assert packet["next_balance"] == 2
    assert packet["q_valuation"] == 1
    assert packet["required_q_valuation"] == 4
    assert packet["barrier_failure_next_macro"] is False
    assert packet["scope"] == (
        "authenticated next odd event; Boolean/Walsh windows separate and lazy"
    )
    assert "harmonics" not in packet
    assert "source_bound_harmonic_ring" not in packet
    ports = _mapping(packet["q_radix_orbits"])
    assert set(ports) == {"2", "3", "5", "6", "10", "64"}
    for radix in (2, 3, 5, 6, 10, 64):
        row = _mapping(ports[str(radix)])
        assert row["q_initial"] == (3 * 7 + 1) % radix**4
        assert row["q_next"] == 2 * (3 * 11 + 1) % radix**4


def test_pointwise_demand_checks_bounds_before_source_revalidation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.antihydra import mahler_odd_macro

    step = odd_seam_step(7, 0, 0, 0)

    def forbidden(_seam: object) -> object:
        raise AssertionError("invalid pointwise demand reached source validation")

    monkeypatch.setattr(mahler_odd_macro, "_canonical_odd_seam", forbidden)
    with pytest.raises(ValueError):
        step.demanded_q_ports(places=True)
    with pytest.raises(ValueError):
        odd_seam_pointwise_packet(step, places=65)


def test_mahler_high_digit_projection_is_only_computed_when_demanded(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("undemanded Mahler high-digit projection ran")

    monkeypatch.setattr(mahler_action_module, "affine_high_digit_transport", forbidden)
    result = AntihydraArithmeticTerm(3, shared_cache=False).result()
    packet = associated_action(result)
    assert "radial_affine_arithmetic" not in packet


def test_odd_macro_demand_budget_fails_closed() -> None:
    with pytest.raises(BlockContextBudgetExceeded):
        Odd.run(4097)
    with pytest.raises(BlockContextBudgetExceeded):
        Odd.run(50).power(100)
    with pytest.raises(ValueError):
        Odd.run(0)
    with pytest.raises(ValueError):
        odd_seam_step(4, 0, 0, 0)
    with pytest.raises(ValueError):
        odd_seam_step(7, 1, 0, 0)
