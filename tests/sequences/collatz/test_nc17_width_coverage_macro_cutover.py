"""Exact base-6 coverage and source-selected Collatz border continuation."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.fields.radix import radix_width
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import collatz as collatz_metrics
from number_compiler.resources.temporal_diagnostics import (
    collect_temporal_diagnostics_snapshot,
)
from number_compiler.sequences.collatz.border_harmonic_ring import PeriodicTail6305Ring
from number_compiler.sequences.collatz.collatz_two_sided_ring import (
    CollatzTwoSidedCylinder,
)
from number_compiler.sequences.collatz.cross_family_port_power import (
    CrossFamilyPortAction,
    SourceCongruence,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.temporal_source_morphism import (
    PointedCollatzSource,
    certified_collatz_root_from_port,
)
from tests.support.reference_arithmetic import collatz_literal


def _changing_tail_source(motif: tuple[int, ...]) -> int:
    residue, modulus = PeriodicTail6305Ring.guard_residue(motif, 1)
    source = residue + ((3 - residue) * pow(modulus, -1, 5) % 5) * modulus
    return source + 5 * modulus * (1 << 512)


def _first_two_return_port(motif: tuple[int, ...]) -> CrossFamilyPortAction:
    action = DyadicTerminalFieldAction.identity()
    for tail in motif[:2]:
        odd = DyadicTerminalFieldAction.one_run(1)
        action = action.then(
            odd.then(DyadicTerminalFieldAction.zero_run(tail)).then(odd)
        )
    guard = SourceCongruence(action.source_residue, action.source_modulus).meet(
        SourceCongruence(3, 5)
    )
    assert guard is not None
    return CrossFamilyPortAction(action, guard, 4, None)


def test_width_coverage_retains_uncovered_middle_positions() -> None:
    exponent = 32
    left, right = 1_000_000_000_107, 1_000_000_116_747
    scale = (1 << (129 - 2 * exponent)) * 3 ** (2 * exponent)
    first, last = scale * left - 1, scale * right - 1
    cylinder = CollatzTwoSidedCylinder(first, last, first % 6**70, 6**70)

    coverage = cylinder.radix6_coverage()

    assert coverage is not None
    assert (coverage.width, coverage.low_digits, coverage.high_digits) == (80, 70, 8)
    assert coverage.forced_five_suffix == 65
    assert coverage.uncovered == (70, 72)
    assert coverage.digit_at(69) == first // 6**69 % 6
    assert coverage.digit_at(70) is None
    assert coverage.digit_at(71) is None
    assert coverage.digit_at(72) == first // 6**72 % 6
    assert coverage.proven_value is None


def test_touching_width_bands_reconstruct_only_the_singleton() -> None:
    places = 40
    value = 4 * 6**places - 1
    cylinder = CollatzTwoSidedCylinder(
        3 * 6**places,
        value + 1,
        value % 6**places,
        6**places,
    )

    coverage = cylinder.radix6_coverage(max_leading_digits=1)

    assert coverage is not None
    assert coverage.complete
    assert coverage.alternatives == 1
    assert coverage.proven_value == value
    assert coverage.high_word == 3
    assert coverage.low_digits == places
    assert coverage.forced_five_suffix == places


@pytest.mark.parametrize("motif", [(0, 2, 1, 1), (1, 2, 2, 1), (0, 1, 1, 0)])
def test_cylinder_selects_only_the_exact_changing_tail_word(
    motif: tuple[int, ...],
) -> None:
    source = _changing_tail_source(motif)
    cylinder = CollatzTwoSidedCylinder.from_pointed_source(
        source, binary_bits=128, leading_bits=12
    )
    ticks = sum(tail + 4 for tail in motif)

    result = cylinder.forced_border_word_for_ticks(ticks)

    assert result is not None
    action, target, selected = result
    assert selected == motif
    assert action.endpoint(source) == collatz_literal(source, ticks)
    assert target.contains(action.endpoint(source))
    assert cylinder.forced_border_word_for_ticks(ticks - 1) is None
    assert cylinder.forced_border_word_for_ticks(ticks, max_returns=2) is None


def test_true_root_square_uses_forced_cylinder_before_old_compiler(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    motif = (0, 2, 1, 1)
    source = _changing_tail_source(motif)
    port = _first_two_return_port(motif)
    assert port.admits(source)
    ticks = port.action.steps + port.odd_events
    assert ticks == sum(tail + 4 for tail in motif[:2])

    owner = PointedCollatzSource.issue(source, 2 * ticks, ledger=ResourceLedger())
    first = certified_collatz_root_from_port(owner, port)
    assert first._guarded_repetition(2, max_coefficient_bits=8192) is None

    def reject_reconstruction(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("source-forced second half reached the old compiler")

    monkeypatch.setattr(
        "number_compiler.sequences.collatz.temporal_run_quotient.compile_collatz_temporal_run_quotient",
        reject_reconstruction,
    )
    doubled = first.square()

    assert doubled.ticks == 2 * ticks
    assert doubled.last.value == collatz_literal(source, 2 * ticks)
    assert doubled.odd_ticks == 8
    assert doubled.port_action is not None
    assert doubled.port_action.endpoint(source) == doubled.last.value
    assert doubled.second_half_selected_from_true_root
    assert (
        owner.ledger.counters[
            collatz_metrics.COLLATZ_PHYSICAL_BORDER_RETURN_CANDIDATE_CHECKS
        ]
        > 0
    )
    assert (
        owner.ledger.counters[
            collatz_metrics.COLLATZ_PHYSICAL_BORDER_RETURN_VALUATION_CHECKS
        ]
        > 0
    )


def test_different_tail_after_shared_first_return_stays_unresolved() -> None:
    cylinder = CollatzTwoSidedCylinder(73, 153, 73, 80)
    first = cylinder.forced_border_word_for_ticks(5)

    assert first is not None
    _, target, tails = first
    assert tails == (1,)
    assert (target.first, target.last) == (83, 173)
    assert target.forced_next_6305_tail is None
    assert cylinder.forced_border_word_for_ticks(9) is None
    assert {tail for tail, _ in target.conditional_next_tails(max_tail=4)} == {0, 2}


def test_eight_exit_is_a_terminal_selected_endpoint_not_a_reused_border() -> None:
    cylinder = CollatzTwoSidedCylinder.from_pointed_source(
        33, binary_bits=8, leading_bits=2
    )

    final_return = cylinder.forced_border_word_for_ticks(5)

    assert final_return is not None
    action, endpoint, tails = final_return
    assert tails == (1,)
    assert action.endpoint(33) == 38
    assert endpoint.contains(38)
    # Continuing six ticks would need a proof of the next 8-border step;
    # the 6305-only source cylinder must refuse instead of fabricating it.
    assert cylinder.forced_border_word_for_ticks(6) is None


def test_width_and_horizon_admission_are_bounded() -> None:
    source = 6**8
    varying_width = CollatzTwoSidedCylinder(source - 1, source + 1, 0, 1)
    assert varying_width.radix6_coverage() is None
    assert radix_width(varying_width.first, 6) != radix_width(varying_width.last, 6)

    cylinder = CollatzTwoSidedCylinder.from_pointed_source(
        13, binary_bits=8, leading_bits=2
    )
    assert cylinder.forced_border_word_for_ticks(5) is None
    with pytest.raises(ValueError, match="border horizon"):
        cylinder.forced_border_word_for_ticks(0)
    with pytest.raises(ValueError, match="digit budget"):
        cylinder.radix6_coverage(max_leading_digits=-1)


def test_cylinder_and_width_coverage_charge_the_query_ledger() -> None:
    ledger = ResourceLedger()
    before = collect_temporal_diagnostics_snapshot(ledger)
    assert before.observations.collatz_two_sided_cylinder_constructions is None
    assert before.observations.collatz_radix6_coverage_evaluations is None
    cylinder = CollatzTwoSidedCylinder.from_pointed_source(
        33, binary_bits=8, leading_bits=2, ledger=ledger
    )
    coverage = cylinder.radix6_coverage(ledger=ledger)

    assert coverage is not None
    assert (
        ledger.counters[collatz_metrics.COLLATZ_TWO_SIDED_CYLINDER_CONSTRUCTIONS] == 1
    )
    assert ledger.counters[collatz_metrics.COLLATZ_TWO_SIDED_CYLINDER_OPERAND_BITS] > 0
    assert ledger.counters[collatz_metrics.COLLATZ_RADIX6_COVERAGE_EVALUATIONS] == 1
    assert ledger.counters[collatz_metrics.COLLATZ_RADIX6_COVERAGE_OPERAND_BITS] > 0
    counters = dict(ledger.counters)
    snapshot = collect_temporal_diagnostics_snapshot(ledger)
    assert snapshot.observations.collatz_two_sided_cylinder_constructions == 1
    assert snapshot.observations.collatz_two_sided_cylinder_operand_bits is not None
    assert snapshot.observations.collatz_radix6_coverage_evaluations == 1
    assert snapshot.observations.collatz_radix6_coverage_operand_bits is not None
    assert ledger.counters == counters


def test_unforced_border_candidate_records_its_refusal() -> None:
    ledger = ResourceLedger()
    cylinder = CollatzTwoSidedCylinder.from_pointed_source(
        31, binary_bits=8, leading_bits=5, ledger=ledger
    )

    assert cylinder.forced_next_return(ledger=ledger) is None
    assert (
        ledger.counters[collatz_metrics.COLLATZ_PHYSICAL_BORDER_RETURN_CANDIDATE_CHECKS]
        == 1
    )
    assert (
        ledger.counters[
            collatz_metrics.COLLATZ_PHYSICAL_BORDER_RETURN_CANDIDATE_REFUSALS
        ]
        == 1
    )


def test_invalid_width_coverage_precision_precedes_port_observation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    motif = (0, 2, 1, 1)
    source = _changing_tail_source(motif)
    port = _first_two_return_port(motif)
    ticks = port.action.steps + port.odd_events
    owner = PointedCollatzSource.issue(source, 2 * ticks, ledger=ResourceLedger())
    root = certified_collatz_root_from_port(owner, port)

    def forbidden_demand(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("invalid coverage precision reached port observation")

    monkeypatch.setattr(CrossFamilyPortAction, "demanded_ports", forbidden_demand)
    with pytest.raises(ValueError, match="coverage precision"):
        root.demanded_outer_inner_ports(
            include_width_coverage=True, max_leading_digits=0
        )
