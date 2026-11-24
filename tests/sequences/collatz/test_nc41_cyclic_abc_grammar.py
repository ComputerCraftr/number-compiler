"""NC41 production regression: mixed abc grammar, cyclic source guards and band lifts."""

from __future__ import annotations

from dataclasses import replace
from itertools import product
from random import Random

import pytest

from number_compiler.arithmetic.fields.blank_ledger import BlankLedger
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.cyclic_abc_execution import (
    exact_cyclic_width_ledger,
    issued_field_prefix,
)
from number_compiler.sequences.collatz.cyclic_abc_grammar import (
    CyclicGuardedRow,
    MixedUpperBand,
    ParameterizedABC,
    ShortcutAffine,
    issue_cyclic_row,
)
from number_compiler.sequences.collatz.temporal_run_quotient import (
    compile_collatz_temporal_run_quotient,
)


def literal_prefix(source: int, steps: int) -> tuple[int, str, int]:
    result: list[str] = []
    ticks = 0
    for _ in range(steps):
        bit = source & 1
        result.append(str(bit))
        ticks += 1 + bit
        source = (3 * source + 1) >> 1 if bit else source >> 1
    return source, "".join(result), ticks


def literal_physical(source: int, ticks: int) -> int:
    for _ in range(ticks):
        source = 3 * source + 1 if source & 1 else source >> 1
    return source


def test_non_border_1486_743_phase_and_partial_copy() -> None:
    x = issue_cyclic_row(1486, 24)
    y = issue_cyclic_row(743, 23)
    assert x is not None and y is not None
    assert x.row.word == "0111"
    assert y.row.word == "1110"
    assert x.row.canonical_phase == ("0111", 0)
    assert y.row.canonical_phase == ("0111", 1)
    assert x.row.rotated(1).word == y.row.word
    assert x.row.abc.words == ("0", "1", "0")
    assert x.row.abc.counts == (1, 3, 0)
    assert y.row.abc.counts == (3, 1, 0)
    assert x.row.motif_phase_id[:2] == y.row.motif_phase_id[:2]
    assert x.row.motif_phase_id[2] == 0 and y.row.motif_phase_id[2] == 1
    assert x.action != y.action
    shallow = CyclicGuardedRow("0111").admitted_prefix(14, 40)
    assert shallow is not None and shallow.maximum_match == 6
    assert shallow.action != x.action
    assert (x.maximum_match, y.maximum_match) == (14, 13)
    assert (x.action.steps, x.action.odds, x.physical_ticks) == (14, 10, 24)
    assert (y.action.steps, y.action.odds, y.physical_ticks) == (13, 10, 23)
    for source, plan in ((1486, x), (743, y)):
        end, word, ticks = literal_prefix(source, plan.action.steps)
        assert (end, ticks) == (plan.endpoint, plan.physical_ticks)
        assert word == (plan.row.word * 4)[: plan.action.steps]
        field = issued_field_prefix(plan)
        assert field.producer_issued and field.endpoint(source) == plan.endpoint
        assert field.steps == plan.action.steps and field.gain == 3**10


def test_cyclic_phase_uses_first_rotation_for_repeated_motifs() -> None:
    for size in range(1, 9):
        for letters in product("01", repeat=size):
            word = "".join(letters)
            primitive_size = next(
                p
                for p in range(1, size + 1)
                if size % p == 0 and word == word[:p] * (size // p)
            )
            primitive = word[:primitive_size]
            rotations = tuple(
                primitive[i:] + primitive[:i] for i in range(primitive_size)
            )
            canonical = min(rotations)
            phase = next(
                i
                for i in range(primitive_size)
                if canonical[i:] + canonical[:i] == primitive
            )
            assert CyclicGuardedRow(word).canonical_phase == (canonical, phase)


def test_issued_cyclic_suffix_and_moving_cut(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    admission = issue_cyclic_row(1486, 24)
    assert admission is not None
    shallow = CyclicGuardedRow("0111").admitted_prefix(14, 40)
    assert shallow is not None
    assert admission.canonical_action_id == shallow.canonical_action_id
    assert admission.maximum_match != shallow.maximum_match

    def forbidden(*_args: object) -> None:
        raise AssertionError("suffix replayed physical source occurrences")

    monkeypatch.setattr(CyclicGuardedRow, "advance_entry_phase", forbidden)
    charges: list[int] = []
    for steps in range(1, admission.action.steps):
        suffix = admission.advance(steps, reserve_bits=charges.append)
        assert suffix is not None
        source, _, ticks = literal_prefix(admission.source, steps)
        assert suffix.source == source
        assert suffix.endpoint == admission.endpoint
        assert suffix.physical_ticks + ticks == admission.physical_ticks
        assert suffix.row == admission.row.rotated(steps)
    assert charges and all(charge > 0 for charge in charges)
    assert admission.advance(0, reserve_bits=charges.append) is admission
    assert (
        admission.advance(admission.action.steps, reserve_bits=charges.append) is None
    )
    with pytest.raises(ValueError):
        admission.advance(admission.action.steps + 1, reserve_bits=charges.append)
    with pytest.raises(ValueError, match="source issuer"):
        replace(admission, source=1488).advance(1, reserve_bits=charges.append)

    cut = admission.action.steps + 6
    band = admission.moving_cut(cut, reserve_bits=charges.append)
    assert band.upper_endpoint(admission.source >> cut) == admission.endpoint >> (
        cut - admission.action.steps
    )
    for high in (0, 1, 42):
        value = (high << cut) + band.low_source
        assert band.upper_endpoint(high) == admission.action.endpoint(value) >> (
            cut - admission.action.steps
        )
    with pytest.raises(ValueError):
        admission.moving_cut(admission.action.steps - 1, reserve_bits=charges.append)


def test_abc_parameters_compile_without_letter_expansion() -> None:
    grammar = ParameterizedABC(("01", "111", "0"), (12, 5, 6))
    action = grammar.action
    word = "01" * 12 + "111" * 5 + "0" * 6
    assert action.steps == len(word) and action.odds == word.count("1")
    assert action == ShortcutAffine.from_word(word)
    assert action.gain == 3**action.odds and action.steps + action.odds == 72
    huge = ParameterizedABC(("0111", "1", "0"), (800, 0, 0))
    assert huge.action.steps == 3200 and huge.action.odds == 2400
    with pytest.raises(ValueError):
        huge.short_word(limit=256)


def test_issued_field_prefix_does_not_rebuild_motif_grammar(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    plan = issue_cyclic_row(1486, 24)
    assert plan is not None
    evaluations = 0

    def counted(row: CyclicGuardedRow) -> ParameterizedABC:
        nonlocal evaluations
        evaluations += 1
        if evaluations > 1:
            raise AssertionError("issued row reconstructed its grammar")
        return ParameterizedABC.from_motif(row.word)

    monkeypatch.setattr(CyclicGuardedRow, "abc", property(counted))
    field = issued_field_prefix(plan)
    assert field.endpoint(plan.source) == plan.endpoint
    assert evaluations == 0


def test_powers_and_temporal_splits_vs_literal() -> None:
    rng = Random(43)
    for _ in range(500):
        a = "".join(str(rng.randrange(2)) for _ in range(rng.randrange(1, 9)))
        b = "".join(str(rng.randrange(2)) for _ in range(rng.randrange(1, 9)))
        count = rng.randrange(0, 16)
        source = ShortcutAffine.from_word(a)
        after = ShortcutAffine.from_word(b)
        joined = source.then(after)
        assert joined == ShortcutAffine.from_word(a + b)
        assert source.power(count) == ShortcutAffine.from_word(a * count)
        assert joined.steps + joined.odds == len(a + b) + (a + b).count("1")


def test_defect_exact_periodic_right_congruence() -> None:
    for p in range(1, 9):
        for source in range(1, 140):
            _, word, _ = literal_prefix(source, p)
            row = CyclicGuardedRow(word)
            match = row.matched_steps(source)
            extent = 34 if match is None else min(34, match + 1)
            _, observed, _ = literal_prefix(source, extent)
            periodic = (word * (1 + (extent // p)))[:extent]
            assert (
                observed[: min(match or extent, extent)]
                == periodic[: min(match or extent, extent)]
            )
            if match is not None and match < extent:
                assert observed[match] != periodic[match]
            admitted = row.admitted_prefix(source, 80)
            if admitted is not None:
                direct_end, word_prefix, ticks = literal_prefix(
                    source, admitted.action.steps
                )
                assert (direct_end, ticks) == (
                    admitted.endpoint,
                    admitted.physical_ticks,
                )
                assert (
                    word_prefix == periodic[: admitted.action.steps]
                    or admitted.action.steps > extent
                )


def test_moving_cut_mixed_upper_band_gain_and_carry() -> None:
    rng = Random(442)
    successful = 0
    for _ in range(3500):
        source = rng.randrange(1, 1 << 20)
        steps = rng.randrange(1, 9)
        middle, word_a, _ = literal_prefix(source, steps)
        n2 = rng.randrange(1, 8)
        endpoint, word_b, _ = literal_prefix(middle, n2)
        a = ShortcutAffine.from_word(word_a)
        b = ShortcutAffine.from_word(word_b)
        cut = rng.randrange(steps + n2, 22)
        lo = source % (1 << cut)
        part_a = MixedUpperBand.from_lower(a, cut, lo)
        part_b = MixedUpperBand.from_lower(b, cut - steps, part_a.lower_endpoint)
        combined = part_a.then(part_b)
        assert combined.action == a.then(b)
        assert combined.upper_gain == 3 ** (word_a.count("1") + word_b.count("1"))
        assert combined.carry == part_b.upper_gain * part_a.carry + part_b.carry
        assert combined.upper_endpoint(source >> cut) == endpoint >> (cut - steps - n2)
        assert combined.lower_endpoint == endpoint % (1 << (cut - steps - n2))
        successful += 1
    assert successful == 3500


def test_exhaustive_8_step_mixed_9_bit_right_congruence() -> None:
    # Exhaustive 12-bit lower rows; 16 + 16 uniform rows are excluded.
    # Compare complete projected upper responses, not just sampled residues.
    keys: set[tuple[int, int, int]] = set()
    mixed_count = 0
    for source in range(1 << 12):
        _, word, _ = literal_prefix(source, 8)
        if word in ("00000000", "11111111"):
            continue
        action = ShortcutAffine.from_word(word)
        band = MixedUpperBand.from_lower(action, 12, source)
        key = band.projected_action_id(9)
        keys.add(key)
        mixed_count += 1
        for upper in (0, 1, 17, 511):
            assert (band.upper_endpoint(upper) & 511) == (
                (key[1] * upper + key[2]) & 511
            )
    assert mixed_count == 4064
    assert len(keys) == 747


def test_source_guard_and_partial_tick_boundaries() -> None:
    row = CyclicGuardedRow("0111")
    assert row.motif.source_residue == 14
    assert row.motif.certifies(1486)
    assert not row.motif.certifies(743)
    assert row.admitted_prefix(743, 100) is None
    for requested_ticks in range(1, 28):
        plan = row.admitted_prefix(1486, requested_ticks)
        if plan is None:
            continue
        assert plan.physical_ticks <= requested_ticks
        assert plan.endpoint == literal_prefix(1486, plan.action.steps)[0]
    assert row.matched_steps(1486) == 14


@pytest.mark.parametrize(
    "source,ticks,expected,avoided",
    [
        (1486, 24, 5366, 14),
        (743, 23, 5366, 13),
        (1486, 25, 2683, 14),
        (1486, 23, 10732, 13),
        (743, 24, 2683, 13),
    ],
)
def test_actual_scalar_scheduler_consumes_cyclic_row(
    source: int, ticks: int, expected: int, avoided: int
) -> None:
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(source, ticks, ledger=ledger)
    assert result.endpoint == expected == literal_physical(source, ticks)
    assert ledger.counters.get("collatz_cyclic_grammar_admitted_actions") == 1
    assert (
        ledger.counters.get("collatz_cyclic_grammar_classifications_elided") == avoided
    )
    assert result.physical_ticks == ticks


@pytest.mark.parametrize(
    "f5,joint", [(False, False), (True, False), (False, True), (True, True)]
)
def test_joint_f5_source_projection_preserved(f5: bool, joint: bool) -> None:
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(
        1486, 24, ledger=ledger, include_f5=f5, include_joint_cocycle=joint
    )
    assert result.endpoint == 5366
    if joint:
        assert ledger.counters.get("collatz_cyclic_grammar_admitted_actions") == 1
        assert result.joint_action is not None
        assert result.joint_action.fields.steps == 14
        assert result.joint_action.normalized_endpoint == 5366
    else:
        assert ledger.counters.get("collatz_cyclic_grammar_admitted_actions") == 1
    if f5:
        assert result.normalized_f5 is not None
        assert result.normalized_f5.apply(1486) == 5366 % 5


def test_source_preflight_happens_before_power() -> None:
    calls: list[int] = []

    def reject(steps: int) -> None:
        calls.append(steps)
        raise RuntimeError("budget blocked")

    with pytest.raises(RuntimeError, match="budget blocked"):
        issue_cyclic_row(1486, 24, reserve_bits=reject)
    assert calls == [14]


def test_period_eight_nonborder_issuer() -> None:
    source = 1431
    issued = issue_cyclic_row(source, 22)
    assert issued is not None and len(issued.row.word) == 8
    assert issued.row.word == "11100000"
    assert issued.action.steps == 16
    assert issued.action.odds == 6
    assert issued.physical_ticks == 22 and issued.endpoint == 16
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(source, 22, ledger=ledger)
    assert result.endpoint == issued.endpoint
    assert ledger.counters["collatz_cyclic_grammar_admitted_actions"] == 1


def test_production_admitted_row_cannot_reenter_old_discovery(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.collatz import temporal_run_executor as executor
    from number_compiler.sequences.collatz.unified_skew_clock import SkewQuadraticClock

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("cyclic row fell back to per-step or skew discovery")

    monkeypatch.setattr(executor, "leading_homogeneous_run", forbidden)
    monkeypatch.setattr(executor, "attempt_unified_skew_reentry", forbidden)
    monkeypatch.setattr(SkewQuadraticClock, "power", forbidden)
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(1486, 21, ledger=ledger)
    assert result.endpoint == literal_physical(1486, 21)
    assert ledger.counters["collatz_cyclic_grammar_admitted_actions"] == 1
    assert ledger.counters.get("collatz_physical_unified_skew_selector_checks", 0) == 0


@pytest.mark.parametrize(("source", "ticks"), [(1486, 24), (743, 23), (1431, 22)])
def test_cyclic_action_supplies_joint_width_and_innovation(
    source: int, ticks: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    from number_compiler.sequences.collatz import temporal_run_executor as executor

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("certified cyclic action rediscovered its source")

    monkeypatch.setattr(executor, "leading_homogeneous_run", forbidden)
    monkeypatch.setattr(executor, "attempt_unified_skew_reentry", forbidden)
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(
        source,
        ticks,
        ledger=ledger,
        include_f5=True,
        include_joint_cocycle=True,
        include_width_spine=True,
        include_innovation_tape=True,
        innovation_modulus=97,
    )
    value, expected_width = literal_physical_widths(source, ticks)
    assert result.endpoint == value
    assert result.tape_width_summary is not None
    assert result.tape_width_summary.blank == expected_width
    assert result.joint_action is not None
    assert result.innovation_observation is not None
    assert result.normalized_f5 is not None
    assert result.normalized_f5.apply(source) == value % 5
    assert ledger.counters["collatz_cyclic_grammar_admitted_actions"] == 1
    assert ledger.counters["collatz_cyclic_grammar_joint_projections"] == 1
    assert ledger.counters["collatz_cyclic_grammar_parity_projections"] == 1
    assert ledger.counters["collatz_cyclic_grammar_width_projections"] == 1
    assert ledger.counters["collatz_cyclic_grammar_width_phase_steps"] <= 16


def test_boundary_witness_keeps_physical_observation_path() -> None:
    # At tick 7 the selected macro reaches 99047, a certified cyclic source.
    # The complete innovation packet still needs the existing physical path.
    source, ticks = 352164, 30
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(
        source,
        ticks,
        ledger=ledger,
        include_innovation_tape=True,
        innovation_modulus=49,
        require_boundary_witness=True,
    )
    assert result.endpoint == literal_physical(source, ticks) == 713954
    assert result.first_boundary_stamp is not None
    assert result.first_boundary_macro is not None
    stamp = result.first_boundary_stamp
    assert stamp.certifies(source, ticks, stamp.occurrence, result.first_boundary_macro)
    assert stamp.occurrence[:3] == (0, source, 7)
    assert result.first_boundary_macro.endpoint == 99047
    assert issue_cyclic_row(99047, 23) is not None
    assert ledger.counters.get("collatz_cyclic_grammar_admitted_actions", 0) == 0


def test_cyclic_width_rejects_tampered_admission() -> None:
    admission = issue_cyclic_row(1486, 24)
    assert admission is not None
    with pytest.raises(ValueError, match="source issuer"):
        exact_cyclic_width_ledger(replace(admission, source=1488))
    with pytest.raises(ValueError, match="source issuer"):
        exact_cyclic_width_ledger(replace(admission))


def test_cyclic_admission_reuses_checked_endpoint_without_refolding(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.collatz.innovation_input_tape import (
        ParityProgramBuilder,
    )

    admission = issue_cyclic_row(1486, 24)
    assert admission is not None
    expected = admission.endpoint
    original_certifies = ShortcutAffine.certifies
    original_endpoint = ShortcutAffine.endpoint

    def certifies(action: ShortcutAffine, source: int) -> bool:
        if action is admission.action:
            raise AssertionError("rechecked issued cyclic source")
        return original_certifies(action, source)

    def endpoint(action: ShortcutAffine, source: int) -> int:
        if action is admission.action:
            raise AssertionError("refolded issued cyclic endpoint")
        return original_endpoint(action, source)

    monkeypatch.setattr(ShortcutAffine, "certifies", certifies)
    monkeypatch.setattr(ShortcutAffine, "endpoint", endpoint)
    assert admission.endpoint == expected
    assert exact_cyclic_width_ledger(admission).delta == (
        expected.bit_length() - admission.source.bit_length()
    )
    assert issued_field_prefix(admission).endpoint(admission.source) == expected
    ledger = ResourceLedger()
    with ParityProgramBuilder(admission.source, ledger) as builder:
        builder.append_cyclic_row(admission)
        assert builder.source == expected
    assert ledger.nodes == ledger.entries == 0


def literal_physical_widths(source: int, ticks: int) -> tuple[int, BlankLedger]:
    value = source
    widths = [value.bit_length()]
    for _ in range(ticks):
        value = 3 * value + 1 if value & 1 else value >> 1
        widths.append(value.bit_length())
    return value, BlankLedger(
        widths[-1] - widths[0],
        min(widths) - widths[0],
        max(widths) - widths[0],
    )


def test_cyclic_width_extrema_match_literal_physical_steps() -> None:
    rng = Random(5614)
    for _ in range(300):
        source = rng.randrange(3, 1 << 20)
        steps = rng.randrange(1, 9)
        _, word, _ = literal_prefix(source, steps)
        admission = CyclicGuardedRow(word).admitted_prefix(source, 96)
        if admission is None:
            continue
        endpoint, expected = literal_physical_widths(source, admission.physical_ticks)
        assert admission.endpoint == endpoint
        assert exact_cyclic_width_ledger(admission) == expected


def test_long_cyclic_width_uses_only_boundary_phases() -> None:
    row = CyclicGuardedRow("0111")
    modulus = 1 << 512
    defect_gain = row.motif.gain - (1 << row.motif.steps)
    source = (-row.motif.offset * pow(defect_gain, -1, modulus)) % modulus
    admission = row.admitted_prefix(source, 500)
    assert admission is not None and admission.action.steps > 200
    _, expected = literal_physical_widths(source, admission.physical_ticks)
    assert exact_cyclic_width_ledger(admission) == expected


def test_cyclic_optional_publication_releases_resources_on_budget_failure() -> None:
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )

    for capacity in (1, 10, 45, 60, 100, 300, 4000):
        ledger = ResourceLedger(max_nodes=capacity)
        with pytest.raises(BlockContextBudgetExceeded):
            compile_collatz_temporal_run_quotient(
                1486,
                24,
                ledger=ledger,
                include_joint_cocycle=True,
                include_width_spine=True,
                include_innovation_tape=True,
                innovation_modulus=97,
            )
        assert ledger.nodes == ledger.entries == 0


def test_affine_power_stays_logarithmic_not_occurrence_replay(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_then = ShortcutAffine.then
    count = 0

    def counted(self: ShortcutAffine, after: ShortcutAffine) -> ShortcutAffine:
        nonlocal count
        count += 1
        return original_then(self, after)

    monkeypatch.setattr(ShortcutAffine, "then", counted)
    power = ShortcutAffine.from_word("0111").power(4096)
    assert power.steps == 16384 and power.odds == 12288
    assert count < 32  # 2*log2(4096), not 4096 occurrence joins


def test_large_source_uses_same_guard_and_mixed_band_projection() -> None:
    source = 1486 + (1 << 20)
    admitted = issue_cyclic_row(source, 24)
    assert admitted is not None and admitted.action.steps == 14
    upper_cut = 18
    from number_compiler.sequences.collatz.cyclic_abc_grammar import MixedUpperBand

    band = MixedUpperBand.from_lower(
        admitted.action, upper_cut, source % (1 << upper_cut)
    )
    reconstructed = (
        band.upper_endpoint(source >> upper_cut) << (upper_cut - admitted.action.steps)
    ) + band.lower_endpoint
    assert reconstructed == admitted.endpoint == literal_physical(source, 24)
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(source, 24, ledger=ledger)
    assert result.endpoint == literal_physical(source, 24)
    assert ledger.counters["collatz_cyclic_grammar_admitted_actions"] == 1


def test_cyclic_defect_transport_1004_source_rotations() -> None:
    rng = Random(1044)
    for _ in range(1004):
        source = rng.randrange(3, 1 << 18)
        _, word, _ = literal_prefix(source, rng.randrange(1, 9))
        row = CyclicGuardedRow(word)
        old = row.matched_steps(source)
        rotated, following = row.advance_entry_phase(source)
        assert following == literal_prefix(source, 1)[0]
        assert rotated.word == word[1:] + word[:1]
        assert rotated.canonical_phase[0] == row.canonical_phase[0]
        if old is not None:
            assert old >= 1
            assert rotated.matched_steps(following) == old - 1
