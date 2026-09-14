from __future__ import annotations

from devtools.experiments.power_numbers.special_source_certificate import (
    candidate_certificate_differential,
    control_summary,
    folded_support_local_controls,
    synthesize_folded_support_program,
)
from devtools.proofs.special_source_program import (
    FoldedSupportInstruction,
    FoldedSupportProgram,
)


def _old_fermat_overfit_program() -> FoldedSupportProgram:
    # (baseline_v2-trace_seed) * (factor_stride-required_stride)
    return FoldedSupportProgram(
        (
            FoldedSupportInstruction("atom", "baseline_v2"),
            FoldedSupportInstruction("atom", "trace_seed"),
            FoldedSupportInstruction("sub", 0, 1),
            FoldedSupportInstruction("atom", "factor_stride"),
            FoldedSupportInstruction("atom", "required_stride"),
            FoldedSupportInstruction("sub", 3, 4),
            FoldedSupportInstruction("mul", 2, 5),
        )
    )


def test_local_control_set_contains_nontrivial_split_and_deeper_fermat_adversaries() -> (
    None
):
    fermat = control_summary("fermat")
    mersenne = control_summary("mersenne")
    assert fermat.local_axes >= 180
    assert fermat.split_candidate_chunks >= 1
    assert mersenne.local_axes >= 400
    assert mersenne.split_candidate_chunks >= 1
    assert any(
        c.parameter == 9 and c.expected_pass
        for c in folded_support_local_controls("fermat")
    )
    assert any(
        c.parameter == 9 and not c.expected_pass
        for c in folded_support_local_controls("fermat")
    )


def test_f9_mixed_depth_controls_reject_the_shallow_fermat_metadata_fit() -> None:
    program = _old_fermat_overfit_program()
    mismatches = 0
    for control in folded_support_local_controls("fermat"):
        value = program.evaluate(control.spec).value
        actual_pass = value % control.prime_factor == 0
        mismatches += actual_pass != control.expected_pass
    assert mismatches > 0


def test_exhaustive_cost_one_source_grammar_does_not_close_either_family() -> None:
    for family in ("fermat", "mersenne"):
        result = synthesize_folded_support_program(
            family,
            max_operator_cost=1,
            state_cap=20_000,
            allow_internal_gcd=True,
        )
        assert not result.found
        assert result.exhaustive_cost_reached == 1
        assert not result.theorem_proved


def test_candidate_certificate_differential_keeps_unproved_zero_program_out_of_composite_path() -> (
    None
):
    zero = FoldedSupportProgram.atom("zero")
    candidate, expected, exact = candidate_certificate_differential("fermat", 5, zero)
    assert candidate.support_gcd == (1 << 32) + 1
    assert expected == 1
    assert not exact
    assert not candidate.theorem_proved
