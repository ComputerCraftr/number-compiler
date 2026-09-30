from devtools.verification.quotient_synthesis import (
    ObserverFeature,
    synthesize_finite_quotient,
    synthesize_finite_target_observer,
)
from number_compiler.arithmetic.functions.finite_unary import analyze_observer


def test_analyze_observer_counts_target_and_successor_conflicts_exactly() -> None:
    keys = ("a", "a", "b", "b")
    next_keys = ("a", "b", "a", "a")
    targets = (0, 0, 1, 0)
    audit = analyze_observer(keys, next_keys, targets)
    assert audit.classes == 2
    assert audit.target_conflicts == 1
    assert audit.successor_conflicts == 1
    assert not audit.closed


def test_cegar_synthesizer_refines_and_prunes_complete_finite_system() -> None:
    # Four source states.  `coarse` separates the target but not successor;
    # `phase` repairs closure; `duplicate` is redundant and should be pruned.
    successors = (2, 0, 3, 1)
    targets = (0, 0, 1, 1)
    features = (
        ObserverFeature("coarse", (0, 0, 1, 1), cost=1),
        ObserverFeature("phase", (0, 1, 0, 1), cost=2),
        ObserverFeature("duplicate", (0, 1, 0, 1), cost=9),
    )
    result = synthesize_finite_quotient(
        successors,
        targets,
        features,
        required_features=("coarse",),
    )
    assert result.closed
    assert result.selected_features == ("coarse", "phase")
    assert result.classes == 4
    assert not result.noninjective
    assert result.total_cost == 3


def test_cegar_synthesizer_fails_closed_when_features_cannot_repair_conflict() -> None:
    result = synthesize_finite_quotient(
        (1, 0),
        (0, 1),
        (ObserverFeature("constant", (0, 0)),),
    )
    assert not result.closed
    assert result.unresolved_counterexamples > 0


def test_cegar_synthesizes_exact_m7_sign_quotient_from_primary_factors() -> None:
    from number_compiler.arithmetic.fields.radix import digits_lsd
    from number_compiler.arithmetic.polynomials.cyclotomic_factor import (
        cyclotomic_factors_mod_prime,
    )
    from number_compiler.arithmetic.polynomials.digit_cyclotomic import (
        CyclotomicDigitBlock,
    )

    p = 7
    modulus = (1 << p) - 1
    factors = cyclotomic_factors_mod_prime(p, 2)
    assert len(factors) == 2
    columns = []
    for i, factor in enumerate(factors):
        values = tuple(
            CyclotomicDigitBlock.from_coefficients(
                digits_lsd(state, 2, p),
                order=p,
                modulus=2,
                factor=factor,
                length=p,
            ).residue
            for state in range(modulus)
        )
        columns.append(
            ObserverFeature(f"phi7_factor_{i}", values, cost=len(factor) - 1)
        )
    result = synthesize_finite_quotient(
        tuple((state * state - 2) % modulus for state in range(modulus)),
        tuple(state == 0 for state in range(modulus)),
        tuple(columns),
    )
    assert result.closed and result.noninjective
    assert result.classes == 64
    assert set(result.selected_features) == {"phi7_factor_0", "phi7_factor_1"}


def test_target_only_synthesizer_does_not_claim_successor_closure() -> None:
    targets = (0, 0, 0, 1)
    features = (
        ObserverFeature("hi", (0, 0, 1, 1), cost=1),
        ObserverFeature("lo", (0, 1, 0, 1), cost=1),
    )
    result = synthesize_finite_target_observer(targets, features)
    assert result.target_separating
    assert result.selected_features == ("lo", "hi")
    assert result.classes == 4
    assert not result.noninjective
    assert not hasattr(result, "next_closed")


def test_target_only_synthesizer_fails_closed_on_unseparable_labels() -> None:
    result = synthesize_finite_target_observer(
        (0, 1),
        (ObserverFeature("constant", (0, 0), cost=1),),
    )
    assert not result.target_separating
    assert result.unresolved_counterexamples == 1


def test_unary_target_distance_machine_is_canonical_saturating_counter() -> None:
    from number_compiler.arithmetic.functions.finite_unary import (
        unary_target_distance_machine,
    )

    machine = unary_target_distance_machine(5)
    assert machine.transition == (0, 0, 1, 2, 3, 4, 5)
    assert machine.outputs == (False, True, False, False, False, False, False)
    source = 6
    assert [machine.output_after(source, steps) for steps in range(8)] == [
        False,
        False,
        False,
        False,
        False,
        True,
        False,
        False,
    ]


def test_unary_behavioral_block_machine_preserves_within_block_remainders() -> None:
    from number_compiler.arithmetic.functions.finite_unary import (
        unary_behavioral_block_machine,
    )

    # Distance chain: endpoint-only sampling by two merges classes, but an
    # exact two-step block must retain the output at remainder one.
    transition = (0, 0, 1, 2, 3, 4)
    outputs = (False, True, False, False, False, False)
    machine, report = unary_behavioral_block_machine(transition, outputs, 2)
    assert report.one_step_classes == 6
    assert report.sampled_block_classes < report.exact_block_classes
    assert report.exact_block_classes == 6
    assert machine.classes == 6
    assert all(
        isinstance(trace, tuple) and len(trace) == 2 for trace in machine.outputs
    )
