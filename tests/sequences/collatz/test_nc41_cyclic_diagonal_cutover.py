"""Primitive phase, diagonal residue, Laurent seam and production cutover gates."""

from __future__ import annotations

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


def test_issued_field_composition_and_transported_source() -> None:
    plan = issue_cyclic_row(1486, 24)
    assert plan is not None
    first = plan.row.admitted_prefix(plan.source, plan.row.prefix_ticks(7))
    second = plan.advance(7, reserve_bits=reserve)
    assert first is not None and second is not None
    assert second.source == literal(plan.source, 7)[0][-1]
    assert second.endpoint == plan.endpoint
    joined = issued_field_prefix(first).then(issued_field_prefix(second))
    assert (
        joined.coefficient_snapshot()
        == issued_field_prefix(plan).coefficient_snapshot()
    )
    object.__setattr__(joined, "gain", joined.gain + 1)
    assert not joined.producer_issued


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
