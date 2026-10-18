"""Source and guard audits of Collatz's missing 100x100 and F5 matrices."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.border_harmonic_ring import PeriodicTail6305Ring
from number_compiler.sequences.collatz.border_pair_temporal_matrix import (
    BooleanPairMatrix,
    GuardedDecimalPairTransfer,
    UpperNumeratorF5Matrix,
    WeightedPairMatrix,
    demanded_trace_carry_counts,
    mul3_two_digit_carries,
    upper_numerator_f5,
)
from number_compiler.sequences.collatz.collatz_two_sided_ring import (
    CollatzTwoSidedCylinder,
)
from number_compiler.sequences.collatz.conditional_border_moore import (
    compile_conditional_border_moore,
    compile_conditional_return_power,
)
from number_compiler.sequences.collatz.conditional_border_observation import (
    demanded_powered_pair_transfer,
    demanded_powered_upper_phase,
)
from number_compiler.sequences.collatz.cross_family_port_power import MacroTraceGrammar
from number_compiler.sequences.collatz.temporal_run_quotient import (
    compile_collatz_temporal_run_quotient,
)


def test_local_boolean_pair_matrices_exhaust_all_100_pairs_and_both_upper_parities() -> (
    None
):
    for parity in (0, 1):
        even = BooleanPairMatrix.even(parity)
        odd = BooleanPairMatrix.odd_half(parity)
        for pair in range(100):
            x = 100 * (2 * 3 + parity) + pair
            if pair & 1:
                assert even.successors(pair) == ()
                assert odd.successors(pair) == (((3 * x + 1) // 2) % 100,)
            else:
                assert odd.successors(pair) == ()
                assert even.successors(pair) == ((x // 2) % 100,)
    assert BooleanPairMatrix.odd_half(0).then(BooleanPairMatrix.odd_half(0)).successors(
        63
    ) == (43,)


def test_weighted_pair_matrices_accumulate_exact_carry_vectors_when_inlets_are_fixed() -> (
    None
):
    for parity in (0, 1):
        odd = WeightedPairMatrix.odd_half(parity)
        even = WeightedPairMatrix.even(parity)
        assert odd.support() == BooleanPairMatrix.odd_half(parity)
        assert even.support() == BooleanPairMatrix.even(parity)
        for pair in range(100):
            assert odd.successors(pair) == tuple(
                (target, *mul3_two_digit_carries(pair))
                for target in BooleanPairMatrix.odd_half(parity).successors(pair)
            )
        assert odd.power(0) == WeightedPairMatrix.identity()
        assert odd.power(2) == odd.then(odd)
    # For x=63 the upper parity stays zero through two odd half-steps.
    assert WeightedPairMatrix.odd_half(0).power(2).successors(63) == ((43, 2, 3),)
    # The *same* low pair in 263 uses upper parity 0 and then 1, and
    # therefore lands in 93 rather than 43.  Naked temporal squaring is
    # inadmissible on this source; guarded matrix composition is required.
    assert WeightedPairMatrix.odd_half(0).then(
        WeightedPairMatrix.odd_half(1)
    ).successors(63) == ((93, 2, 3),)
    with pytest.raises(ValueError, match="budget"):
        WeightedPairMatrix.odd_half(0).then(
            WeightedPairMatrix.odd_half(1), max_row_entries=0
        )


def test_spatial_mul3_carry_count_wires_match_decimal_arithmetic() -> None:
    for inlet in (0, 1, 2):
        for pair in range(100):
            c1, c2 = mul3_two_digit_carries(pair, inlet=inlet)
            assert c1 == (3 * (pair % 10) + inlet) // 10
            assert c2 == (3 * (pair // 10) + c1) // 10
            assert c2 == (3 * pair + inlet) // 100


def test_original_source_pair_guards_keep_63_263_collision_disjoint() -> None:
    family = CollatzTwoSidedCylinder(63, 263, 63, 200)
    one = compile_conditional_return_power(family, 0, max_tail=8)
    branch = one.select(63)
    assert branch.port is not None
    transfer = GuardedDecimalPairTransfer(branch.port)
    entries = transfer.row(family, 63)
    assert {(entry.output_pair, entry.count) for entry in entries} == {(43, 1), (93, 1)}
    assert sum(entry.count for entry in entries) == family.count
    assert transfer.support_matrix(family).successors(63) == (43, 93)
    for x, output in ((63, 43), (263, 93)):
        chosen = next(entry for entry in entries if entry.guard.admits(x))
        assert chosen.output_pair == output
        assert chosen.target.contains(branch.port.endpoint(x))
    with pytest.raises(ValueError, match="budget"):
        transfer.row(family, 63, max_entries=1)


def test_source_guard_pullback_is_retained_under_return_composition() -> None:
    family = CollatzTwoSidedCylinder(73, 153, 73, 80)
    one = compile_conditional_return_power(family, 0, max_tail=8)
    two = compile_conditional_return_power(family, 1, max_tail=8)
    for source in (73, 153):
        first = one.select(source)
        second = two.select(source)
        assert first.port is not None and second.port is not None
        assert second.tails.length == 2
        matrix = demanded_powered_pair_transfer(two, source)
        assert matrix is not None
        entry = matrix.pointed_entry(source)
        assert entry.guard.admits(source)
        assert entry.output_pair == second.port.endpoint(source) % 100
        # This pair guard is *stricter* than the raw parity/action guard.
        assert entry.guard.meet(second.port.guard) == entry.guard


def test_upper_numerator_phase_is_true_composable_two_by_two_matrix() -> None:
    for tail in range(12):
        matrix = UpperNumeratorF5Matrix.tail(tail)
        for x in range(3, 4000, 10):
            n = 3 * ((x - 3) // 10) + 1
            if (n & -n).bit_length() - 1 != tail:
                continue
            u = n >> tail
            if u % 4 != 3:
                continue
            endpoint = (15 * u + 1) // 2
            assert endpoint % 10 == 3
            assert matrix.apply(n % 5) == upper_numerator_f5(endpoint)
    trace = MacroTraceGrammar.leaf((0, 1, 3))
    for _ in range(8):
        trace = trace.then(trace)
    matrix = UpperNumeratorF5Matrix.from_trace(trace)
    scalar = UpperNumeratorF5Matrix()
    for tail in (0, 1, 3) * (1 << 8):
        scalar = scalar.then(UpperNumeratorF5Matrix.tail(tail))
    assert matrix == scalar
    assert matrix == UpperNumeratorF5Matrix.from_trace(
        MacroTraceGrammar.leaf((0, 1, 3))
    ).power(256)
    assert matrix.returns == 768


def test_phase_is_explicitly_refused_across_eight_and_nine_exits() -> None:
    for source in (33, 53):
        one = compile_conditional_return_power(
            CollatzTwoSidedCylinder(source, source, 0, 1), 0, max_tail=12
        )
        assert demanded_powered_upper_phase(one, source) is None
    graph = compile_conditional_border_moore(
        CollatzTwoSidedCylinder(33, 33, 0, 1), 8, max_tail=12
    )
    packet = graph.demanded_pointed_ports(33)
    assert packet["low_pair_transition"] == (33, 29)
    assert packet["joint_punctured_pair_endpoints"] == (50, 29)
    source_guard = packet["joint_punctured_source_guard"]
    assert isinstance(source_guard, tuple)
    assert source_guard[2] == 1
    assert "low_border_f5_phase_matrix" not in packet


def test_source_certified_temporal_carry_counts_refuse_wrong_tails() -> None:
    trace = MacroTraceGrammar.leaf((0, 0))
    counted = demanded_trace_carry_counts(63, trace)
    assert counted.endpoint == 323
    assert counted.odd_updates == 4
    x = 63
    expected = [0, 0]
    for tail in (0, 0):
        for y in (x, ((3 * x + 1) // 2) >> tail):
            c1, c2 = mul3_two_digit_carries(y % 100)
            expected[0] += c1
            expected[1] += c2
        x = (3 * (((3 * x + 1) // 2) >> tail) + 1) // 2
    assert (counted.first_wire, counted.second_wire) == tuple(expected)
    with pytest.raises(ValueError, match="nonadmitted|second odd"):
        demanded_trace_carry_counts(73, MacroTraceGrammar.leaf((0,)))
    with pytest.raises(BlockContextBudgetExceeded, match="budget"):
        demanded_trace_carry_counts(63, trace, max_returns=1)


def _sample(motif: tuple[int, ...], copies: int = 128) -> tuple[int, int]:
    residue, modulus = PeriodicTail6305Ring.guard_residue(motif, copies)
    residue += ((3 - residue) * pow(modulus, -1, 5) % 5) * modulus
    return residue + 5 * modulus * (1 << 48), (copies // len(motif)) * sum(
        j + 4 for j in motif
    )


def test_powered_3_border_phase_reuses_compressed_trace() -> None:
    x, _ = _sample((0, 1), 128)
    cylinder = CollatzTwoSidedCylinder.from_pointed_source(
        x, binary_bits=512, leading_bits=8
    )
    powered = compile_conditional_return_power(cylinder, 7, max_tail=8)
    matrix = demanded_powered_upper_phase(powered, x)
    assert matrix is not None and matrix.returns == 128
    branch = powered.select(x)
    assert branch.port is not None
    assert matrix.apply(upper_numerator_f5(x)) == upper_numerator_f5(
        branch.port.endpoint(x)
    )


def test_cli_conditional_scheduler_consumes_cached_pair_and_phase() -> None:
    x, ticks = _sample((0, 1), 128)
    ledger = ResourceLedger()
    result = compile_collatz_temporal_run_quotient(
        x, ticks, ledger=ledger, include_f5=True, require_mixed_prefix=True
    )
    assert result.physical_ticks == ticks
    assert result.endpoint % 100 in range(100)
    assert (
        ledger.counters.get("collatz_conditional_scheduler_certified_actions", 0) == 1
    )
    assert ledger.counters.get("collatz_conditional_power_pair_matrix_checks", 0) == 1
    assert ledger.counters.get("collatz_low_border_numerator_phase_checks", 0) == 1
    # The cache guard certifies not only the parity word but every lower
    # border: a translation by its modulus retains the 3-ending endpoint.
    from number_compiler.hashlife.execution.dyadic_return_runs import (
        RunArithmeticWorkspace,
    )
    from number_compiler.sequences.collatz.conditional_scheduler_adapter import (
        issue_conditional_scheduler_candidate,
    )

    cache_ledger = ResourceLedger()
    scratch = RunArithmeticWorkspace.for_ledger(cache_ledger, "matrix-guard-audit")
    with scratch.scope():
        candidate = issue_conditional_scheduler_candidate(
            x, ticks, scratch=scratch, ledger=cache_ledger, include_f5=True
        )
        assert candidate is not None
        assert candidate.numerator_phase is not None
        assert (
            candidate.port.guard.modulus % (5 << (candidate.normalized_steps + 1)) == 0
        )
        transported = x + candidate.port.guard.modulus
        assert candidate.port.admits(transported)
        assert candidate.port.endpoint(transported) % 10 == 3
        assert candidate.numerator_phase.apply(
            upper_numerator_f5(transported)
        ) == upper_numerator_f5(candidate.port.endpoint(transported))


def test_existing_short_border_macro_uses_pair_matrix_only_on_demand() -> None:
    for x, ticks in ((63, 4), (33, 8), (143, 4)):
        enabled = ResourceLedger()
        disabled = ResourceLedger()
        with_f5 = compile_collatz_temporal_run_quotient(
            x, ticks, ledger=enabled, include_f5=True
        )
        ordinary = compile_collatz_temporal_run_quotient(x, ticks, ledger=disabled)
        assert with_f5.endpoint == ordinary.endpoint
        assert with_f5.physical_f5 is not None
        assert enabled.counters.get("collatz_low_border_pair_matrix_checks", 0) >= 1
        assert disabled.counters.get("collatz_low_border_pair_matrix_checks", 0) == 0


def test_powered_carry_join_starts_at_authenticated_term_endpoint() -> None:
    from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
    from number_compiler.sequences.collatz.named_border_carry_matrix import (
        powered_from_term,
    )

    initial = PoweredCollatzTerm(7, 0)
    at_seed = powered_from_term(initial, 2)
    assert at_seed is not None
    assert at_seed.macro.source == 7
    assert at_seed.macro.endpoint == 11

    unprepared = PoweredCollatzTerm(11, 2)
    assert powered_from_term(unprepared, 2) is None

    occurrence = PoweredCollatzTerm(11, 2)
    occurrence.prepare_joint_cocycle()
    endpoint = occurrence.true_root_morphism().last.value
    assert endpoint == 17
    after_query = powered_from_term(occurrence, 2)
    assert after_query is not None
    assert after_query.macro.source == endpoint
    assert after_query.macro.endpoint == 26
    assert after_query.macro.physical_ticks == 2
