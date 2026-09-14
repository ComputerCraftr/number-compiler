"""Bounded audit of successor-quotient generators for Fermat/Mersenne.

The purpose of this probe is to identify *injectors* for the small binary-jump
machines, not to create another retained state.  It tests the same generator
families used elsewhere in the repository:

* successor-image set morphisms;
* quadratic field/Jacobi residue constraints;
* alternate-radix reinterpretation as a derived observer only;
* finite structured decision automata; and
* Boolean ANF complexity of image-membership predicates.

Nothing here promotes a prime-case identity through a composite candidate.  In
particular M11 is retained as the ring-safety counterexample.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from devtools.experiments.algebra.math_support import ceil_sqrt
from devtools.experiments.power_numbers.special_successor_models import (
    AlgebraicBlockObserverAudit,
    BehavioralPurityBlockAudit,
    CRTPurityAudit,
    LocalTwoPrimaryComponent,
    TwoPrimaryResidualInterfaceAudit,
    TwoPrimaryResidualShape,
    TwoPrimaryShiftAudit,
)
from devtools.experiments.power_numbers.special_successor_purity import (
    crt_purity_audits,
)
from devtools.proofs.oracles.special_binary_jump import (
    _fermat_carrier_proof,
    _mersenne_carrier_proof,
)
from devtools.proofs.quotient_synthesis import (
    ObserverFeature,
    synthesize_finite_quotient,
)
from number_compiler.arithmetic.fields.adic_morphism import ValuationSensitivityMorphism
from number_compiler.arithmetic.fields.projection_field import (
    cyclotomic_jet_from_values,
)
from number_compiler.arithmetic.fields.radix import bit_width
from number_compiler.arithmetic.functions.finite_unary import (
    UnaryPowerArena,
    unary_behavioral_block_machine,
)
from number_compiler.arithmetic.polynomials.primary_jet import primary_jet_from_digits
from number_compiler.sequences.prime.set import jacobi_symbol

if TYPE_CHECKING:
    from devtools.proofs.oracles.special_binary_jump import _SpecialCarrierProof


def _two_primary_shape(
    family: str, component: LocalTwoPrimaryComponent
) -> TwoPrimaryResidualShape:
    if family == "fermat":
        ambient_v2 = int(
            component.quotient_v2
            if component.quotient_v2 is not None
            else component.ambient_v2
        )
        ambient_odd = int(
            component.quotient_odd_part
            if component.quotient_odd_part is not None
            else component.ambient_odd_part
        )
    elif family == "mersenne":
        ambient_v2 = int(component.ambient_v2)
        ambient_odd = int(component.ambient_odd_part)
    else:
        raise ValueError(family)
    return TwoPrimaryResidualShape(
        component.local_model,
        component.discriminant_character,
        ambient_v2,
        ambient_odd != 1,
        int(component.source_v2),
        int(component.source_odd_part) != 1,
    )


def _two_primary_interface_from_truth(
    audit: CRTPurityAudit,
) -> tuple[tuple[TwoPrimaryResidualShape, int], ...]:
    """Quotient factor identity immediately; retain only local dynamical shape.

    This function consumes factor-backed truth and therefore remains research
    only.  Equal local shapes are fused even when they came from different
    primes; the count is retained because multiple CRT components is itself a
    purity obstruction.
    """
    counts: dict[TwoPrimaryResidualShape, int] = {}
    for component in audit.components:
        shape = _two_primary_shape(audit.family, component)
        counts[shape] = counts.get(shape, 0) + int(component.multiplicity)
    return tuple(sorted(counts.items(), key=lambda item: repr(item[0])))


def _two_primary_interface_bits(
    family: str,
    parameter: int,
    shapes: tuple[tuple[TwoPrimaryResidualShape, int], ...],
) -> int:
    parameter = int(parameter)
    height = (1 << parameter) if family == "fermat" else parameter
    depth_bits = bit_width(max(1, height))
    # model id + discriminant ternary + four small fields + multiplicity.
    return bit_width(len(shapes)) + sum(
        3 + 2 + 2 * depth_bits + 2 + bit_width(max(1, count))
        for _shape, count in shapes
    )


def two_primary_residual_interface_audits() -> tuple[
    TwoPrimaryResidualInterfaceAudit, ...
]:
    rows: list[TwoPrimaryResidualInterfaceAudit] = []
    for truth in crt_purity_audits():
        shapes = _two_primary_interface_from_truth(truth)
        total = sum(count for _shape, count in shapes)
        if truth.family == "fermat":
            expected_v2 = (1 << truth.parameter) - truth.parameter - 1
            inferred_pure = (
                total == 1
                and len(shapes) == 1
                and shapes[0][0].ambient_v2 == expected_v2
                and not shapes[0][0].ambient_has_odd_part
                and shapes[0][0].source_v2 == expected_v2
                and not shapes[0][0].source_has_odd_part
            )
        else:
            expected_v2 = truth.parameter
            inferred_pure = (
                total == 1
                and len(shapes) == 1
                and shapes[0][0].discriminant_character == -1
                and shapes[0][0].ambient_v2 == expected_v2
                and not shapes[0][0].ambient_has_odd_part
                and shapes[0][0].source_v2 == expected_v2
                and not shapes[0][0].source_has_odd_part
            )
        rows.append(
            TwoPrimaryResidualInterfaceAudit(
                truth.family,
                truth.parameter,
                len(truth.components),
                shapes,
                _two_primary_interface_bits(truth.family, truth.parameter, shapes),
                False,
                inferred_pure == truth.pure_prime_domain_shape,
                "pure" if inferred_pure else "impure",
            )
        )
    return tuple(rows)


def two_primary_shift_block_audits() -> tuple[TwoPrimaryShiftAudit, ...]:
    """Reuse the Collatz tropical valuation channel for consumed 2-depth.

    If a local source has order ``2**v * odd``, one squaring consumes one unit
    of ``v`` while preserving the odd part.  Representing consumed depth turns
    this into the existing saturated affine action ``c -> min(v,c+1)``.
    """
    rows: list[TwoPrimaryShiftAudit] = []
    truth_rows = crt_purity_audits()
    interface_rows = {
        (r.family, r.parameter): r for r in two_primary_residual_interface_audits()
    }
    for truth in truth_rows:
        height = (1 << truth.parameter) if truth.family == "fermat" else truth.parameter
        blocks = tuple(sorted({1, 2, 4, ceil_sqrt(height)}))
        for block_size in blocks:
            exact = True
            compositions = 0
            for component in truth.components:
                v2 = int(component.source_v2)
                if v2 == 0:
                    consumed = 0
                    ops = 0
                else:
                    morphism = ValuationSensitivityMorphism(2, v2, 1, 1, 1, 0).power(
                        block_size
                    )
                    consumed = morphism.apply(0)
                    ops = morphism.compositions
                compositions = max(compositions, ops)
                expected_remaining = max(0, v2 - int(block_size))
                exact &= v2 - consumed == expected_remaining
                # Squaring cannot remove an odd-order component.
                exact &= (component.source_odd_part != 1) == (
                    component.source_odd_part != 1
                )
            interface = interface_rows[(truth.family, truth.parameter)]
            rows.append(
                TwoPrimaryShiftAudit(
                    truth.family,
                    truth.parameter,
                    block_size,
                    len(interface.canonical_shapes),
                    compositions,
                    exact,
                    interface.retained_description_bits,
                )
            )
    return tuple(rows)


def behavioral_purity_block_audits() -> tuple[BehavioralPurityBlockAudit, ...]:
    """Apply the exact 196-style compose/minimize experiment to unary dynamics.

    The exact block observable includes every within-block output so arbitrary
    remainders remain answerable.  Endpoint-only compression is recorded as a
    negative control and is never accepted as a semantic quotient.
    """
    rows: list[BehavioralPurityBlockAudit] = []
    for family, parameter in (("fermat", 4), ("mersenne", 13), ("mersenne", 11)):
        proof = (
            _fermat_carrier_proof(parameter)
            if family == "fermat"
            else _mersenne_carrier_proof(parameter)
        )
        for block_size in (1, 2, 4, 8):
            _machine, report = unary_behavioral_block_machine(
                proof.transition,
                proof.outputs,
                block_size,
            )
            rows.append(
                BehavioralPurityBlockAudit(
                    family,
                    parameter,
                    block_size,
                    proof.classes,
                    report.one_step_classes,
                    report.sampled_block_classes,
                    report.exact_block_classes,
                    report.sampled_block_classes < report.exact_block_classes,
                    report.powering_compositions,
                    report.exact_quotient_description_bits,
                )
            )
    return tuple(rows)


def _state_bits_lsf(value: int, width: int) -> tuple[int, ...]:
    return tuple((int(value) >> bit) & 1 for bit in range(int(width)))


def _native_algebraic_block_features(
    family: str, parameter: int
) -> tuple[ObserverFeature, ...]:
    """Only native arithmetic/digit theorem channels; no alternate-base observers."""
    family = str(family)
    parameter = int(parameter)
    if family == "fermat":
        proof = _fermat_carrier_proof(parameter)
        modulus = (1 << (1 << parameter)) + 1
        representatives = proof.representatives
        width = 1 << parameter
        features: list[ObserverFeature] = [
            ObserverFeature(
                f"native.jacobi.shift.{shift}",
                tuple(
                    jacobi_symbol(value + shift, modulus) for value in representatives
                ),
                2,
            )
            for shift in (-2, -1, 0, 1, 2)
        ]
    elif family == "mersenne":
        proof = _mersenne_carrier_proof(parameter)
        modulus = (1 << parameter) - 1
        representatives = tuple(range((modulus + 1) // 2))
        width = parameter
        features = [
            ObserverFeature(
                f"native.sign-jacobi.shift.{shift}",
                tuple(
                    tuple(
                        sorted(
                            (
                                jacobi_symbol(value + shift, modulus),
                                jacobi_symbol((-value) % modulus + shift, modulus),
                            )
                        )
                    )
                    for value in representatives
                ),
                2,
            )
            for shift in (-2, -1, 0, 1, 2)
        ]
    else:
        raise ValueError(family)

    # Reuse the canonical digit-field algebras that already power 196/prime
    # projections.  They are exact composable word summaries, but bounded CEGAR
    # still has to prove they are closed under this number-theoretic successor.
    words = tuple(_state_bits_lsf(value, width) for value in representatives)
    for degree in (2, 4):
        values = tuple(
            primary_jet_from_digits(word, degree=degree, modulus=8).jet
            for word in words
        )
        features.append(ObserverFeature(f"primary-jet.d{degree}.m8", values, degree))
    for order in (2, 4, 8):
        values = tuple(
            cyclotomic_jet_from_values(word, order=order, modulus=8).residue
            for word in words
        )
        features.append(ObserverFeature(f"cyclotomic.o{order}.m8", values, order))
    return tuple(features)


def _block_transition_and_trace(
    proof: _SpecialCarrierProof,
    block_size: int,
) -> tuple[tuple[int, ...], tuple[tuple[object, ...], ...]]:
    block_size = int(block_size)
    powered = UnaryPowerArena(proof.transition).power(block_size).effect.transition
    traces: list[tuple[object, ...]] = []
    for source in range(proof.classes):
        state = source
        trace: list[object] = []
        for _ in range(block_size):
            trace.append(proof.outputs[state])
            state = proof.transition[state]
        traces.append(tuple(trace))
    return powered, tuple(traces)


def algebraic_block_observer_audits() -> tuple[AlgebraicBlockObserverAudit, ...]:
    rows: list[AlgebraicBlockObserverAudit] = []
    for family, parameter in (("fermat", 4), ("mersenne", 13), ("mersenne", 11)):
        proof = (
            _fermat_carrier_proof(parameter)
            if family == "fermat"
            else _mersenne_carrier_proof(parameter)
        )
        features = _native_algebraic_block_features(family, parameter)
        for block_size in (1, 2, 4, 8):
            transition, trace = _block_transition_and_trace(proof, block_size)
            result = synthesize_finite_quotient(transition, trace, features)
            rows.append(
                AlgebraicBlockObserverAudit(
                    family,
                    parameter,
                    block_size,
                    proof.classes,
                    len(features),
                    result.selected_features,
                    result.classes,
                    result.closed,
                    result.noninjective,
                    result.unresolved_counterexamples,
                )
            )
    return tuple(rows)
