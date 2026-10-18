"""100-state conditional and source-certified Mahler center matrix gates."""

from __future__ import annotations

from copy import copy
from dataclasses import replace
from random import Random
from typing import cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.sequences.antihydra.mahler_center_depth_matrix import (
    MahlerCenterBooleanMatrix as M,
)
from number_compiler.sequences.antihydra.mahler_center_depth_matrix import (
    MahlerCertifiedCenterDepthTransfer as T,
)
from number_compiler.sequences.antihydra.mahler_center_depth_matrix import (
    center_next,
    conditional_center_moore,
)
from number_compiler.sequences.antihydra.mahler_center_exterior_join import (
    MahlerCenterExteriorJoin,
)
from number_compiler.sequences.antihydra.mahler_odd_program import (
    MahlerOddSourceProgram,
    compile_mahler_odd_program,
)


def scalar(d: int) -> int:
    return (3 * d + (d & 1)) // 2


def test_all_six_100_state_matrices_agree_with_full_source() -> None:
    # Independent integer source recomposition for all 600 conditional rows.
    for lower_carry in range(3):
        for upper_parity in range(2):
            matrix = M.from_driver(lower_carry, upper_parity)
            assert matrix.nonempty_rows == matrix.edges == 100
            for c in range(100):
                # c_lower comes from L=lower_carry*100//3, except when
                # c=0..2 choose explicit exact witnesses by searching L.
                low = next(
                    x for x in range(100) if (3 * x + (x & 1)) // 100 == lower_carry
                )
                upper = 4 + upper_parity
                d = low + 100 * c + 10000 * upper
                expect = (scalar(d) // 100) % 100
                assert center_next(c, lower_carry, upper_parity) == expect
                assert matrix.destinations(c) == (expect,)


def test_bitset_composition_and_conditional_squaring() -> None:
    rng = Random(17)
    for _ in range(18):
        word = tuple((rng.randrange(3), rng.randrange(2)) for _ in range(11))
        matrix = M.identity()
        for letter in word:
            matrix = matrix.then(M.from_driver(*letter))
        for c in range(100):
            literal = c
            for letter in word:
                literal = center_next(literal, *letter)
            assert matrix.destinations(c) == (literal,)
        repeat = matrix.power(33)
        for c in (0, 1, 48, 99):
            literal = c
            for _ in range(33):
                for letter in word:
                    literal = center_next(literal, *letter)
            assert repeat.destinations(c) == (literal,)
        assert repeat.compact_packet()["source_authority"] == (
            "matrix-relation-only; temporal repeat not certified"
        )
        assert not repeat.compact_packet()["temporal_repeat_certified"]


def test_all_declared_input_letters_are_retained() -> None:
    alphabet = ((0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1))
    matrix = M.from_contexts(alphabet)
    for c in range(100):
        assert set(matrix.destinations(c)) == {
            center_next(c, lower, upper) for lower, upper in alphabet
        }
        assert len(matrix.destinations(c)) <= 6


def test_00_99_exterior_alias_remains_separate() -> None:
    join = MahlerCenterExteriorJoin.from_source(100007)
    assert {c.center for c in join.candidates} == {0, 99}
    matrix = M.from_exterior(join)
    assert matrix.destinations(0) == (0,)
    assert matrix.destinations(99) == (48,)
    assert matrix.nonempty_rows == 2
    assert M.from_exterior(join).compact_packet(include_rows=True)["sparse_rows"]


def test_real_source_certification_and_width_birth() -> None:
    # 6667 -> 10001 crosses the four-to-five-digit midpoint in one tick.
    certificate = T.from_source(6667, 4)
    assert certificate.width_births == (1,)
    assert certificate.center_positions[0] == 1
    assert certificate.center_positions[1] == 1
    assert certificate.pointed_sources[0] == 6667
    assert certificate.pointed_sources[1] == 10001
    assert certificate.pointed_sources[-1] == scalar(scalar(scalar(scalar(6667))))
    assert certificate.pointed_centers[-1] in certificate.matrix.destinations(
        certificate.pointed_centers[0]
    )
    assert certificate.packet()["source_authority"] == "source-finite-trace"
    assert certificate.conditional_composition.edges >= certificate.matrix.edges


def test_powered_source_reuses_admitted_pointed_successor_actions(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.antihydra.mahler_joint_future import (
        MahlerJointFutureAction,
    )

    def forbidden_prefix_discovery(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("pointed powered leaves must reuse selected actions")

    monkeypatch.setattr(
        MahlerJointFutureAction,
        "from_source_prefix",
        classmethod(forbidden_prefix_discovery),
    )
    certificate = T.powered_from_source(7, 3, leaf_steps=2)
    assert certificate.pointed_sources == (7, 11, 17, 26)
    assert certificate.steps == 3
    assert certificate.packet()["source_authority"] == "source-finite-trace"


def test_short_sources_use_a_fixed_zero_padded_pair() -> None:
    certificate = T.from_source(7, 3)
    assert certificate.pointed_sources == (7, 11, 17, 26)
    assert certificate.center_positions == (1, 1, 1, 1)
    assert certificate.pointed_centers == (0, 1, 1, 2)
    assert certificate.pointed_centers[-1] in certificate.matrix.destinations(
        certificate.pointed_centers[0]
    )


def test_source_authority_cannot_be_forged_through_public_dataclass_fields() -> None:
    certificate = T.from_source(100007, 2)
    assert not hasattr(T, "_source_issued")
    with pytest.raises(ValueError, match="source issuer"):
        replace(certificate, steps=31)
    assert M(certificate.matrix.rows).compact_packet()["source_authority"] == (
        "matrix-relation-only; temporal repeat not certified"
    )
    with pytest.raises(ValueError, match="source issuer"):
        T(
            certificate.matrix,
            certificate.safety_matrix,
            certificate.steps,
            certificate.pointed_sources,
            certificate.pointed_centers,
            certificate.center_positions,
            certificate.radix99,
            certificate.radix198,
            certificate.rejected_source_paths,
            certificate.width_births,
            certificate.conditional_composition,
            certificate.initial_ledger,
            certificate.low_border_carries,
            certificate.source_port_punctures,
            certificate.source_fiber_edges,
        )
    copied = copy(certificate)
    with pytest.raises(ValueError, match="source-issued"):
        copied.packet()
    object.__setattr__(copied, "steps", 31)
    with pytest.raises(ValueError, match="source-issued"):
        copied.then(certificate)
    tampered = T.from_source(100007, 2)
    object.__setattr__(tampered, "steps", 31)
    with pytest.raises(ValueError, match="source-issued"):
        tampered.packet()
    bool_tampered = T.from_source(1, 1)
    object.__setattr__(bool_tampered, "pointed_sources", (True, 2))
    with pytest.raises(ValueError, match="source-issued"):
        bool_tampered.packet()
    mutated_matrix = T.from_source(100007, 2)
    object.__setattr__(
        mutated_matrix.matrix._relation,
        "rows",
        tuple(bool(row) for row in mutated_matrix.matrix.rows),
    )
    with pytest.raises(ValueError, match="source-issued"):
        mutated_matrix.packet()


def test_source_prefix_fractional_safety_not_assumed() -> None:
    cert = T.from_source(100007, 2)
    assert cert.pointed_centers[-1] in cert.matrix.destinations(cert.pointed_centers[0])
    # The source produces '11'. Its fractional Mahler guard is empty.
    assert not cert.safety_matrix.destinations(cert.pointed_centers[0])
    packet = cert.packet()
    assert not packet["actual_pointed_path_fractional_guard_nonempty"]
    assert packet["actual_pointed_path_ledger_safe"] is None


def test_join_packet_counts_compositions_without_claiming_cache_hits() -> None:
    cert = T.powered_from_source(7, 4, leaf_steps=2)
    packet = cert.packet()
    assert packet["composition_joins"] == 1
    assert packet["equal_span_joins"] == 1
    assert packet["temporal_matrix_join_mode"] == "source-fiber-action-composition"


def test_randomized_full_source_and_crt_transport() -> None:
    rng = Random(29)
    for _ in range(160):
        d = rng.randrange(1000, 10**12)
        steps = rng.randrange(1, 8)
        cert = T.from_source(d, steps, initial_ledger=3 * steps + 12)
        p = cert.packet()
        assert p["source_certified_physical_ticks"] == steps
        first_center = cast(int, p["pointed_first_center"])
        last_center = cast(int, p["pointed_last_center"])
        assert last_center in cert.matrix.destinations(first_center)
        assert p["source_mod99_path"] == tuple(s % 99 for s in cert.pointed_sources)
        assert p["source_mod198_path"] == tuple(s % 198 for s in cert.pointed_sources)
        assert cert.safety_matrix.edges <= cert.matrix.edges
        assert cert.conditional_composition.edges >= cert.matrix.edges


def test_forged_source_and_invalid_letter_refused() -> None:
    with pytest.raises(ValueError, match="unverified"):
        T.from_sources((100007, 100008))
    with pytest.raises(ValueError):
        M.from_driver(3, 0)
    with pytest.raises(ValueError):
        M.from_driver(0, 2)
    with pytest.raises(ValueError):
        M.identity().power(-1)
    with pytest.raises(ValueError):
        M(tuple([1] * 99))


def test_oversized_source_is_rejected_before_decimal_or_successor_work(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    oversized = 10**5000
    with pytest.raises(BlockContextBudgetExceeded, match="256-digit"):
        T.from_sources((oversized, 1))

    def unexpected_from_sources(
        _cls: type[T], /, *_args: object, **_kwargs: object
    ) -> T:
        raise AssertionError("oversized root reached successor construction")

    monkeypatch.setattr(T, "from_sources", classmethod(unexpected_from_sources))
    with pytest.raises(BlockContextBudgetExceeded, match="256-digit"):
        T.from_source(oversized, 32)


def test_compiled_program_horizon_and_real_tick_sources() -> None:
    program = compile_mahler_odd_program(100007, max_events=8)
    available = program.ending_clock - program.clock
    assert available >= 4
    packet = program.center_transfer_at_tick(program.clock, steps=4, include_rows=True)
    assert packet["source_authority"] == "source-finite-trace"
    assert "compiled_program_source_authenticated" not in packet
    assert packet["pointed_first_center"] == 0
    source_mod99_path = cast(tuple[int, ...], packet["source_mod99_path"])
    assert source_mod99_path[0] == 100007 % 99
    assert packet["sparse_rows"]
    with pytest.raises(ValueError):
        program.center_transfer_at_tick(program.ending_clock, steps=1)
    with pytest.raises(ValueError):
        program.center_transfer_at_tick(program.clock, steps=available + 1)


def test_caller_built_program_does_not_claim_compiler_provenance() -> None:
    program = MahlerOddSourceProgram(
        source=3,
        index=0,
        clock=0,
        balance=0,
        fragments=(),
        endpoint=5,
        ending_index=1,
        ending_clock=1,
        ending_balance=2,
        stop_reason="caller-built",
        source_certified=False,
    )
    packet = program.center_transfer_at_tick(0, steps=1)
    assert packet["source_authority"] == "source-finite-trace"
    assert packet["source_mod99_path"] == (3, 5)
    assert packet["source_mod198_path"] == (3, 5)
    assert packet["pointed_center_path"] == (0, 0)
    assert "compiled_program_source_authenticated" not in packet


def test_true_root_temporal_square_requires_real_second_half() -> None:
    first = T.from_source(6667, 3, initial_ledger=10)
    second_source = first.pointed_sources[-1]
    second_balance = 10 + sum(3 * (x & 1) - 1 for x in first.pointed_sources[:-1])
    second = T.from_source(second_source, 3, initial_ledger=second_balance)
    squared = first.then(second)
    independent = T.from_source(6667, 6, initial_ledger=10)
    assert squared.matrix.rows == independent.matrix.rows
    assert squared.pointed_sources == independent.pointed_sources
    assert squared.width_births == independent.width_births
    with pytest.raises(ValueError, match="nonadjacent"):
        first.then(first)


def test_future_closed_conditional_moore_partition() -> None:
    letters = ((0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1))
    partition = conditional_center_moore(letters)
    classes = {state: i for i, states in enumerate(partition) for state in states}
    assert len(classes) == 100
    assert classes[0] != classes[99]
    for states in partition:
        for left in states:
            for right in states:
                for letter in letters:
                    assert (
                        classes[center_next(left, *letter)]
                        == classes[center_next(right, *letter)]
                    )
    literal = conditional_center_moore(letters, output="literal")
    assert len(literal) == 100
