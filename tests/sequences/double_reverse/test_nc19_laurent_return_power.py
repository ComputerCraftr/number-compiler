"""Exact source-guarded Laurent accumulator return and period certificates."""

from __future__ import annotations

import json
from collections.abc import Iterator
from random import Random

import pytest

from number_compiler.api import cli
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.source_adapter import decimal_digits_lsd
from number_compiler.sequences.double_reverse.temporal_hashlife import (
    PHYSICAL_GROWTH_CYCLES,
    edge_phase_of_integer,
)
from number_compiler.sequences.double_reverse.temporal_laurent_return import (
    LaurentAccumulatorReturn,
    LaurentFirstJetReturn,
    projected_period_from_state,
    source_laurent_accumulator_packet,
)
from number_compiler.sequences.double_reverse.temporal_seed_morphism import (
    certified_seed_orbit_morphism,
)
from tests.sequences.double_reverse.packet_helpers import (
    integer_field,
    object_list,
    object_mapping,
)


def _reverse(x: int) -> int:
    return int(str(x)[::-1])


def _step(x: int) -> int:
    return 2 * _reverse(x)


def _physical_after(seed: int, generations: int) -> int:
    value = seed
    for _ in range(generations):
        value = _step(value)
    return value


def _normalized_trace(seed: int, steps: int) -> Iterator[tuple[int, int, int, int]]:
    x, norm_sum, rev_sum, last = seed, seed, 0, seed
    yield 0, x, norm_sum, rev_sum
    for n in range(1, steps + 1):
        x = _step(x)
        norm = _reverse(x) if n % 2 else x
        if n % 2:
            rev_sum += norm - last
        else:
            norm_sum += norm - last
        last = norm
        yield n, norm, norm_sum, rev_sum


def test_exact_carry_matrix_on_every_border_phase_without_inner_digit_assumptions() -> (
    None
):
    rng = Random(0x19A810)
    left = (("17",), ("17",), ("48", "49"), ("48", "49"))
    right = (("68", "88"), ("42",), ("42",), ("68", "88"))
    for phase in range(4):
        bits = PHYSICAL_GROWTH_CYCLES[phase]
        for size in range(1, 36):
            for _ in range(8):
                x = int(
                    rng.choice(left[phase])
                    + "".join(str(rng.randrange(10)) for _ in range(size % 16))
                    + rng.choice(right[phase])
                )
                assert edge_phase_of_integer(x) == phase
                trace = list(_normalized_trace(x, 4))
                physical = x
                for g in bits:
                    nxt = _step(physical)
                    assert len(str(nxt)) - len(str(physical)) == g
                    physical = nxt
                macro = LaurentAccumulatorReturn.generator(bits[0])
                got = macro.apply(x, x, 0)
                assert got == tuple(v % 198 for v in trace[-1][1:])
                first_jet = LaurentFirstJetReturn.generator(bits[0])
                assert first_jet.apply(x) == trace[-1][1] % 1980
                assert first_jet.apply(x) % 198 == got[0]


def test_binary_power_is_compositional_and_closed_in_modular_ring() -> None:
    rng = Random(0x198)
    for growth in (0, 1):
        one = LaurentAccumulatorReturn.generator(growth)
        for _ in range(200):
            i, j = rng.randrange(500), rng.randrange(500)
            x, a, b = (rng.randrange(198) for _ in range(3))
            pair = one.power(i).then(one.power(j))
            direct = one.power(i + j)
            assert pair == direct
            assert pair.apply(x, a, b) == one.power(j).apply(
                *one.power(i).apply(x, a, b)
            )
            assert direct.matrix[0][0] == pow(160, i + j, 198)


def test_first_jet_1980_power_and_finite_cycle_exact() -> None:
    rng = Random(0x1980)
    for growth in (0, 1):
        one = LaurentFirstJetReturn.generator(growth)
        for _ in range(100):
            i, j = rng.randrange(1024), rng.randrange(1024)
            x = rng.randrange(1980)
            assert one.power(i + j) == one.power(i).then(one.power(j))
            assert one.power(i + j).apply(x) == one.power(j).apply(
                one.power(i).apply(x)
            )
            period = one.exact_period(x)
            cycle_entry = one.power(period["transient_macros"]).apply(x)
            assert (
                one.power(period["primitive_period_macros"]).apply(cycle_entry)
                == cycle_entry
            )
            for p in range(1, period["primitive_period_macros"]):
                assert one.power(p).apply(cycle_entry) != cycle_entry


def test_exact_primitive_period_in_projected_state() -> None:
    for seed, start, expected in ((168, 0, 30), (1, 8, 90), (196, 16, 90)):
        trace = list(_normalized_trace(seed, start + 24))
        x = trace[start][1] % 198
        result = projected_period_from_state(x, 1)
        assert result["transient_macros"] == 0
        assert result["primitive_joint_macros"] == expected
        first = LaurentAccumulatorReturn.generator(1)
        left = first.power(expected).apply(x, 31, 62)
        assert left == (x, 31, 62)
        for smaller in range(1, expected):
            if first.power(smaller).apply(x, 31, 62) == (x, 31, 62):
                raise AssertionError("reported period is not primitive")


def _assert_laurent_packet_matches_integer_path(
    seed: int, target: int, clock: dict[str, object]
) -> None:
    assert clock["status"] == "available"
    assert clock["target_generation"] == target
    exact = list(_normalized_trace(seed, target))[-1]
    assert (
        clock["target_normalized_mod198"],
        clock["target_norm_sum_mod198"],
        clock["target_rev_sum_mod198"],
    ) == tuple(v % 198 for v in exact[1:])
    assert (
        integer_field(clock, "target_normalized_mod198")
        - integer_field(clock, "target_norm_sum_mod198")
        - integer_field(clock, "target_rev_sum_mod198")
    ) % 198 == 0
    assert clock["certified_growth_and_mod198_all_future"] is True
    assert clock["all_depth_digit_period_certified"] is False
    jet = object_mapping(clock["first_laurent_jet"])
    assert jet["modulus"] == 1980
    anchor = object_list(clock["anchor_state_mod198"])
    assert len(anchor) == 3
    source, norm_sum, reverse_sum = anchor
    assert type(source) is int
    assert type(norm_sum) is int
    assert type(reverse_sum) is int
    assert (
        integer_field(jet, "target_residue") % 198
        == (
            LaurentAccumulatorReturn.generator(
                integer_field(clock, "first_mirrored_growth")
            )
            .power(integer_field(clock, "powered_macros"))
            .apply(source, norm_sum, reverse_sum)[0]
        )
    )


@pytest.mark.parametrize("seed", [1, 168, 196])
@pytest.mark.parametrize("target", [40, 41, 42, 43, 64, 65, 66, 67, 68, 128, 511, 512])
def test_cli_source_anchored_power_matches_independent_integer_path(
    seed: int, target: int, capsys: pytest.CaptureFixture[str]
) -> None:
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                str(seed),
                "--nth",
                str(target),
                "--no-value",
                "--info",
                "temporal.residue99",
                "--format",
                "json",
            ]
        )
        == 0
    )
    data = json.loads(capsys.readouterr().out)["info"]["temporal.residue99"]
    _assert_laurent_packet_matches_integer_path(
        seed, target, data["normalized_laurent_accumulator"]
    )


@pytest.mark.parametrize("seed", [1, 168, 196])
@pytest.mark.parametrize("target", [65, 66, 128, 256])
def test_full_powered_source_morphism_shares_laurent_action(
    seed: int, target: int, capsys: pytest.CaptureFixture[str]
) -> None:
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                str(seed),
                "--nth",
                str(target),
                "--no-value",
                "--info",
                "temporal.seed-morphism",
                "--format",
                "json",
            ]
        )
        == 0
    )
    data = json.loads(capsys.readouterr().out)["info"]["temporal.seed-morphism"]
    assert data["power"]["mode"] == "source_certified_hashlife_dyadic"
    clock = data["normalized_laurent_accumulator"]
    _assert_laurent_packet_matches_integer_path(seed, target, clock)
    if target % 2 == 0:
        assert data["endpoint"]["mod198"] == clock["target_normalized_mod198"]


def test_long_jump_does_not_expand_full_word(
    capsys: pytest.CaptureFixture[str],
) -> None:
    target = 4096
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "168",
                "--nth",
                str(target),
                "--no-value",
                "--info",
                "temporal.residue99",
                "--format",
                "json",
            ]
        )
        == 0
    )
    data = json.loads(capsys.readouterr().out)["info"]["temporal.residue99"]
    clock = data["normalized_laurent_accumulator"]
    assert clock["powered_macros"] >= 1000
    assert clock["primitive_period"]["primitive_joint_macros"] == 30
    assert clock["target_generation"] == target
    assert data["target_mod198"] == clock["target_normalized_mod198"]


def test_laurent_join_rejects_seed_alias_after_orbit_merge() -> None:
    # T(168) = T(1680); the joined cursor word does not identify the
    # original seed's separate norm/reversal accumulator history.
    assert _step(168) == _step(1680)
    with (
        DoubleReverseTerm(168, 64, max_state_bits=16384) as issued_owner,
        DoubleReverseTerm(1680, 64, max_state_bits=16384) as merged_owner,
    ):
        prefix, action = issued_owner.temporal_residue_quotient()
        assert prefix == 7
        assert _physical_after(168, prefix) == _physical_after(1680, prefix)
        with pytest.raises(ValueError, match="different source owner"):
            source_laurent_accumulator_packet(merged_owner, prefix, action)


def test_laurent_join_rejects_equal_width_mod198_source_collision() -> None:
    with (
        DoubleReverseTerm(168, 64, max_state_bits=16384) as issued_owner,
        DoubleReverseTerm(2373, 64, max_state_bits=16384) as collision_owner,
    ):
        prefix, action = issued_owner.temporal_residue_quotient()
        assert prefix == 7
        issued_word = _physical_after(168, prefix)
        collision_word = _physical_after(2373, prefix)
        assert issued_word == 487488
        assert collision_word == 499368
        assert issued_word != collision_word
        assert len(tuple(decimal_digits_lsd(issued_word))) == action.width_in
        assert len(tuple(decimal_digits_lsd(collision_word))) == action.width_in
        assert issued_word % 198 == collision_word % 198 == action.source_mod198
        with pytest.raises(ValueError, match="different source owner"):
            source_laurent_accumulator_packet(collision_owner, prefix, action)


def test_laurent_join_requires_the_exact_current_prefix_cursor() -> None:
    with DoubleReverseTerm(168, 64, max_state_bits=16384) as term:
        prefix, action = term.temporal_residue_quotient()
        cursor = term.temporal_engine.source_prefix()
        assert cursor is not None
        assert cursor.physical_steps == prefix
        term.temporal_engine.advance_source_prefix()
        with pytest.raises(ValueError, match="matching issued source-prefix cursor"):
            source_laurent_accumulator_packet(term, prefix, action)


def test_full_word_join_rejects_a_substituted_first_root() -> None:
    with DoubleReverseTerm(168, 64, max_state_bits=16384) as term:
        _entry, source = term.prepare_bank_source(max_prefix=32)
        morphism = certified_seed_orbit_morphism(source, steps=source.f_steps)
        source_word = _physical_after(168, source.physical_prefix)
        wrong_word = source_word + 198
        wrong_digits = tuple(decimal_digits_lsd(wrong_word))
        wrong_root = term.source_arena.word(tuple(reversed(wrong_digits)))
        assert term.source_arena.nodes[wrong_root].length == morphism.first.width
        assert wrong_word != source_word
        assert wrong_word % 198 == morphism.first.residue198
        first = morphism.first
        exact_root = first.root
        try:
            object.__setattr__(first, "root", wrong_root)
            with pytest.raises(ValueError):
                source_laurent_accumulator_packet(
                    term,
                    source.physical_prefix,
                    morphism.residue_action,
                    authenticated_morphism=morphism,
                )
        finally:
            object.__setattr__(first, "root", exact_root)


def test_completed_scheduler_join_rejects_same_residue_target_root() -> None:
    with DoubleReverseTerm(168, 64, max_state_bits=16384) as term:
        term.prepare_endpoint()
        _entry, source = term.prepare_bank_source(max_prefix=32)
        morphism = certified_seed_orbit_morphism(
            source, steps=source.f_steps, completed_term=term
        )
        assert (
            source_laurent_accumulator_packet(
                term,
                source.physical_prefix,
                morphism.residue_action,
                authenticated_morphism=morphism,
            )["status"]
            == "available"
        )
        endpoint_root = term.issued_completed_endpoint_root()
        assert endpoint_root == morphism.last.root
        endpoint_digits_lsd = tuple(term.iter_digits())
        endpoint_value = 0
        for digit in reversed(endpoint_digits_lsd):
            endpoint_value = 10 * endpoint_value + digit
        false_value = endpoint_value - 198
        false_digits_lsd = tuple(decimal_digits_lsd(false_value))
        false_root = term.source_arena.word(tuple(reversed(false_digits_lsd)))
        assert term.source_arena.nodes[false_root].length == morphism.last.width
        assert false_value % 198 == morphism.last.residue198
        last = morphism.last
        exact_root = last.root
        try:
            object.__setattr__(last, "root", false_root)
            with pytest.raises(ValueError):
                source_laurent_accumulator_packet(
                    term,
                    source.physical_prefix,
                    morphism.residue_action,
                    authenticated_morphism=morphism,
                )
        finally:
            object.__setattr__(last, "root", exact_root)
