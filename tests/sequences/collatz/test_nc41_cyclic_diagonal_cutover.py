"""Primitive phase, diagonal residue, Laurent seam and production cutover gates."""

from __future__ import annotations

from dataclasses import replace
from itertools import product
from random import Random

import pytest

from number_compiler.hashlife.execution.dyadic_return_runs import RunArithmeticWorkspace
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.collatz.cyclic_abc_execution import issued_field_prefix
from number_compiler.sequences.collatz.cyclic_abc_grammar import (
    CyclicGuardedRow,
    MixedUpperBand,
    ShortcutAffine,
    issue_cyclic_row,
)
from number_compiler.sequences.collatz.cyclic_diagonal import (
    CyclicDefectGuard,
    CyclicLaurentAction,
    CyclicNecklace,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.temporal_run_quotient import (
    compile_collatz_temporal_run_quotient,
)


def reserve(_bits: int) -> None:
    pass


def literal(source: int, steps: int) -> tuple[list[int], str]:
    values = [source]
    letters: list[str] = []
    for _ in range(steps):
        p = source & 1
        letters.append(str(p))
        source = (3 * source + 1) // 2 if p else source // 2
        values.append(source)
    return values, "".join(letters)


def source_for(row: CyclicGuardedRow, guard_bits: int) -> int:
    # Independent finite affine-word oracle, not the new centered descriptor.
    motif = ShortcutAffine.from_word(row.word)
    modulus = 1 << guard_bits
    delta = motif.gain - (1 << motif.steps)
    return (-motif.offset * pow(delta, -1, modulus)) % modulus + modulus


def test_all_510_bounded_words_have_exact_primitive_phase_and_joint_fields() -> None:
    for m in range(1, 9):
        for bits in product("01", repeat=m):
            word = "".join(bits)
            row = CyclicGuardedRow(word)
            source = source_for(row, 48)
            plan = row.admitted_prefix(source, 200, maximum_steps=40)
            assert plan is not None and plan.action.steps == 40
            values, observed = literal(source, 40)
            assert observed == (word * 40)[:40]
            law = plan.guard.action
            assert law.word * (m // len(law.word)) == word
            assert row.canonical_phase == CyclicGuardedRow(word * 3).canonical_phase
            assert plan.action == ShortcutAffine.from_word(observed)
            assert plan.endpoint == values[-1]
            fields = issued_field_prefix(plan)
            denominator = 1 << 40
            assert fields.sum_gain * source + fields.sum_offset == denominator * sum(
                values[1:]
            )
            assert (
                fields.previous_gain * source + fields.previous_offset
                == (denominator // 2) * values[-2]
            )
            # Two independent source inlets distinguish the entire affine sum.
            sibling = source + denominator
            second, second_word = literal(sibling, 40)
            assert second_word == observed
            assert fields.sum_gain * sibling + fields.sum_offset == denominator * sum(
                second[1:]
            )
            for t in (0, 1, 13, 40):
                assert plan.point_at(t, reserve_bits=reserve) == values[t]
                phase = law.rotated(t)
                assert phase.defect(values[t]) == 3 ** observed[:t].count("1") * (
                    law.defect(source) >> t
                )


def test_canonical_word_retains_rotation_and_complete_source_guard() -> None:
    reference = CyclicLaurentAction.from_word("00101")
    rotated = CyclicLaurentAction.from_word("10010" * 3)
    assert rotated.necklace is reference.necklace
    assert rotated.word == "10010"
    assert rotated.phase == 4
    for steps in range(11):
        assert (
            rotated.rotated(steps).word == (rotated.word * 2)[steps % 5 : steps % 5 + 5]
        )

    source = source_for(CyclicGuardedRow(rotated.word), 20)
    guard = CyclicDefectGuard(rotated, source)
    values, observed = literal(source, 20)
    assert observed == rotated.word * 4
    assert guard.point(20, 3 ** rotated.odds(20))[0] == values[-1]
    with pytest.raises(ValueError, match="must be primitive"):
        CyclicNecklace("0010100101")
    with pytest.raises(ValueError, match="canonically rotated"):
        CyclicNecklace("10010")


def test_first_mismatch_is_valuation_not_a_countdown_in_the_response() -> None:
    rng = Random(921)
    for _ in range(1800):
        word = "".join(rng.choice("01") for _ in range(rng.randrange(1, 9)))
        row = CyclicGuardedRow(word)
        source = rng.randrange(3, 1 << 40)
        guard = CyclicDefectGuard(row.laurent_action, source)
        _, actual = literal(source, 100)
        h = next((t for t, p in enumerate(actual) if p != word[t % len(word)]), None)
        assert guard.first_mismatch == h
    short = CyclicGuardedRow("0111").admitted_prefix(14, 40)
    long = issue_cyclic_row(1486, 24)
    assert short is not None and long is not None
    assert short.canonical_action_id == long.canonical_action_id
    assert short.maximum_match != long.maximum_match
    assert long.guard.first_mismatch == 14
    with pytest.raises(ValueError, match="physical guard"):
        long.guard.require_steps(15)
    with pytest.raises(ValueError, match="certified admission"):
        long.diagonal_state(15, 2, 8, reserve_bits=reserve)
    infinite = CyclicGuardedRow("10").admitted_prefix(1, 10**10)
    assert infinite is not None and infinite.guard.first_mismatch is None


def test_production_cutover_forbids_old_affine_and_field_power_paths(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kw: object) -> None:
        raise AssertionError("old occurrence/SLP reconstruction path reached")

    monkeypatch.setattr(ShortcutAffine, "power", forbidden)
    monkeypatch.setattr(CyclicGuardedRow, "prefix_action", forbidden)
    monkeypatch.setattr(CyclicGuardedRow, "advance_entry_phase", forbidden)
    monkeypatch.setattr(MixedUpperBand, "from_lower", forbidden)
    monkeypatch.setattr(DyadicTerminalFieldAction, "power", forbidden)
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(
        1486,
        24,
        ledger=ledger,
        include_joint_cocycle=True,
        include_f5=True,
        include_width_spine=True,
        include_innovation_tape=True,
        innovation_modulus=97,
    )
    assert result.endpoint == 5366 and result.run_actions == 1
    assert result.joint_action is not None
    assert result.normalized_f5 is not None and result.normalized_f5.apply(1486) == 1
    assert result.innovation_observation is not None
    assert ledger.nodes == ledger.entries == 0
    assert ledger.counters["collatz_cyclic_grammar_admitted_actions"] == 1


def test_issued_endpoint_projection_uses_sealed_value_without_reconstruction(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = PoweredCollatzTerm(1486, 24, shared_cache=False)
    term.prepare_joint_cocycle()
    workspace = term.source_image()
    try:
        seam = term.diagonal_carry_seam()
        scratch = RunArithmeticWorkspace.for_ledger(
            term.resource_ledger, "endpoint-test"
        )

        def forbidden(*_args: object, **_kwargs: object) -> None:
            raise AssertionError("issued endpoint was reconstructed")

        monkeypatch.setattr(CyclicDefectGuard, "__post_init__", forbidden)
        demands: list[int] = []
        with scratch.scope():
            assert (
                seam.endpoint_residue(8, reserve_bits=demands.append, max_width=128)
                == 246
            )
            assert demands == [8 * (2 * 8 + 64)]
            assert (
                seam.endpoint_residue(
                    8, reserve_bits=scratch.require_bits, max_width=128
                )
                == 246
            )
            assert (
                seam.field(8, reserve_bits=scratch.require_bits, max_width=128).width
                == 8
            )

        def refuse(_bits: int) -> None:
            raise MemoryError("reservation refused")

        with pytest.raises(MemoryError, match="reservation refused"):
            seam.endpoint_residue(8, reserve_bits=refuse, max_width=128)
        with pytest.raises(MemoryError, match="reservation refused"):
            seam.field(8, reserve_bits=refuse, max_width=128)
    finally:
        workspace.dispose()


@pytest.mark.parametrize(
    "motif", ("0", "1", "01", "001", "0111", "0011111", "01011101")
)
def test_binary_decimal_fixed_cut_and_rebased_quotients(motif: str) -> None:
    row = CyclicGuardedRow(motif)
    source = source_for(row, 100)
    plan = row.admitted_prefix(source, 130, maximum_steps=60)
    assert plan is not None and plan.action.steps == 60
    values, _ = literal(source, 60)
    for radix in (2, 10):
        for precision in (0, 1, 7, 24, 73):
            initial = plan.diagonal_state(0, radix, precision, reserve_bits=reserve)
            for t in (0, 1, 7, 17, 60):
                at = plan.diagonal_state(t, radix, precision, reserve_bits=reserve)
                assert at == initial.advance(t // 2).advance(t - t // 2)
                assert at.numerator_residue() == radix**t * values[t] % radix**precision
                rebased = plan.guard.rebased_state(t, radix, precision)
                assert rebased.numerator_residue() == values[t] % radix**precision
                assert rebased == at.action.initial_state(values[t], radix, precision)
                if precision:
                    assert (
                        at.band(precision - 1, 1)
                        == (radix**t * values[t] // radix ** (precision - 1)) % radix
                    )
            # Equivalent physical numerators/seams must have equal successors,
            # including in the nonunit decimal delta=-5 case.
            same = initial.action.initial_state(
                source + radix**precision, radix, precision
            )
            assert same == initial
            assert same.advance(10**60 + 51) == initial.advance(10**60).advance(51)


def test_modular_upper_ports_compose_at_transported_binary_and_decimal_cuts() -> None:
    rng = Random(4123)
    for _ in range(160):
        word = "".join(rng.choice("01") for _ in range(rng.randrange(1, 9)))
        row = CyclicGuardedRow(word)
        source = source_for(row, 45)
        plan = row.admitted_prefix(source, 80, maximum_steps=30)
        assert plan is not None and plan.action.steps == 30
        h = rng.randrange(1, 30)
        following = plan.advance(h, reserve_bits=reserve)
        assert following is not None
        for radix in (2, 10):
            cut = rng.randrange(30, 39)
            width = rng.randrange(1, 9)
            parent = plan.projected_upper_action(
                30, radix, cut, width, reserve_bits=reserve
            )
            left = plan.projected_upper_action(
                h, radix, cut, width, reserve_bits=reserve
            )
            right = following.projected_upper_action(
                30 - h, radix, cut - h, width, reserve_bits=reserve
            )
            assert left.then(right) == parent
            for child in (0, 1, radix**width - 1):
                inlet = source % radix**cut + child * radix**cut
                expected, _ = literal(inlet, 30)
                assert (
                    parent.apply(child)
                    == expected[-1] // radix ** (cut - 30) % radix**width
                )
            if radix == 2:
                band = plan.moving_cut(cut, reserve_bits=reserve)
                assert parent == band.projected_response(width)


def test_modular_projection_never_asks_for_full_gain_or_full_prefix(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    row = CyclicGuardedRow("0011111")
    plan = row.admitted_prefix(source_for(row, 4200), 7000, maximum_steps=4000)
    assert plan is not None and plan.action.steps == 4000
    expected, _ = literal(plan.source, 4000)

    def forbidden(*_args: object, **_kw: object) -> None:
        raise AssertionError("modular projection constructed a full affine action")

    monkeypatch.setattr(ShortcutAffine, "gain", property(forbidden))
    monkeypatch.setattr(ShortcutAffine, "power", forbidden)
    monkeypatch.setattr(CyclicGuardedRow, "prefix_action", forbidden)
    for radix in (2, 10):
        assert (
            plan.guard.rebased_state(4000, radix, 9).numerator_residue()
            == expected[-1] % radix**9
        )
        port = plan.projected_upper_action(4000, radix, 4002, 8, reserve_bits=reserve)
        assert (
            port.apply(plan.source // radix**4002)
            == expected[-1] // radix**2 % radix**8
        )


def test_published_source_image_retains_same_law_and_reads_both_radices(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = PoweredCollatzTerm(1486, 24, shared_cache=False)
    term.prepare_joint_cocycle()
    workspace = term.source_image()
    try:
        assert workspace.joint_action is not None
        assert workspace.joint_action.fields.cyclic_phase == ("0111", 0)
        seam = term.diagonal_carry_seam()
        scratch = RunArithmeticWorkspace.for_ledger(
            term.resource_ledger, "cyclic-projection-test"
        )

        def forbidden(*_args: object, **_kw: object) -> None:
            raise AssertionError("published seam tried to rediscover a source row")

        monkeypatch.setattr(CyclicGuardedRow, "admitted_prefix", forbidden)
        monkeypatch.setattr(CyclicGuardedRow, "advance_entry_phase", forbidden)
        values, _ = literal(1486, 14)
        with scratch.scope():
            assert (
                seam.endpoint_residue(
                    8, reserve_bits=scratch.require_bits, max_width=128
                )
                == 246
            )
            for radix in (2, 10):
                for t in (0, 7, 14):
                    assert (
                        seam.cyclic_moving_band(
                            radix,
                            t + 1,
                            4,
                            normalized_offset=t,
                            reserve_bits=scratch.require_bits,
                            max_width=128,
                        )
                        == values[t] // radix % radix**4
                    )
            with pytest.raises(ValueError, match="precision demand"):
                seam.cyclic_moving_band(
                    10,
                    15,
                    4,
                    normalized_offset=15,
                    reserve_bits=scratch.require_bits,
                    max_width=128,
                )
    finally:
        workspace.dispose()


def test_cyclic_field_binding_survives_only_aligned_composition() -> None:
    plan = issue_cyclic_row(1486, 24)
    assert plan is not None
    first = plan.row.admitted_prefix(plan.source, plan.row.prefix_ticks(7))
    second = plan.advance(7, reserve_bits=reserve)
    assert first is not None and second is not None
    assert second.source == literal(plan.source, 7)[0][-1]
    assert second.endpoint == plan.endpoint
    left, right = issued_field_prefix(first), issued_field_prefix(second)
    joined = left.then(right)
    assert joined.cyclic_phase == ("0111", 0)
    assert (
        joined.coefficient_snapshot()
        == issued_field_prefix(plan).coefficient_snapshot()
    )
    assert left.then(DyadicTerminalFieldAction.zero_run(1)).cyclic_phase is None
    assert left.then(left).cyclic_phase is None
    changed_gain = left.then(right)
    object.__setattr__(changed_gain, "gain", changed_gain.gain + 1)
    assert not changed_gain.producer_issued
    object.__setattr__(joined, "_cyclic_phase", ("01", 0))
    assert not joined.producer_issued
    with pytest.raises(ValueError, match="not producer issued"):
        _ = joined.cyclic_phase
    with pytest.raises(ValueError, match="source issuer"):
        replace(plan).diagonal_state(1, 2, 5, reserve_bits=reserve)


def test_moving_projection_reserves_before_modular_work(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    plan = issue_cyclic_row(1486, 24)
    assert plan is not None

    def refuse(_bits: int) -> None:
        raise MemoryError("reservation refused")

    def forbidden(*_args: object, **_kw: object) -> None:
        raise AssertionError("allocated modular ring before reservation")

    monkeypatch.setattr(CyclicLaurentAction, "initial_state", forbidden)
    with pytest.raises(MemoryError, match="reservation refused"):
        plan.diagonal_state(7, 10, 30, reserve_bits=refuse)
    with pytest.raises(MemoryError, match="reservation refused"):
        plan.projected_upper_action(7, 10, 20, 5, reserve_bits=refuse)
