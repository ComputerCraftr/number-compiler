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

import os
import pickle
import subprocess
import sys
import tempfile
from dataclasses import asdict
from functools import lru_cache
from pathlib import Path
from typing import TypeVar, cast

from devtools.experiments.power_numbers.purity_cost import (
    cheap_purity_probe_audits,
    cheap_two_primary_purity_probe,
    purity_candidate_audits,
)
from devtools.experiments.power_numbers.special_successor_carry import (
    carry_cyclotomic_transducer_audits,
    carry_hensel_cyclotomic_audits,
    carry_phase_refinement_audits,
    carry_temporal_automaton_audits,
    carry_transfer_automaton_audits,
)
from devtools.experiments.power_numbers.special_successor_factor import (
    bounded_special_factor_short_circuit,
    special_factor_short_circuit_audits,
)
from devtools.experiments.power_numbers.special_successor_models import (
    AlgebraicBlockObserverAudit,
    BehavioralPurityBlockAudit,
    BooleanSetAudit,
    CarryCyclotomicTransducerAudit,
    CarryHenselCyclotomicAudit,
    CarryPhaseRefinementAudit,
    CarryTemporalAutomatonAudit,
    CarryTransferAutomatonAudit,
    CompositeDepthSemanticsAudit,
    CRTPurityAudit,
    ImageFiltrationAudit,
    LocalTwoPrimaryComponent,
    PrimeGroupDepthAudit,
    PureTwoGroupAudit,
    PurityCandidateAudit,
    PurityWorkCost,
    ResidueConstraintAudit,
    SpecialFactorShortCircuitAudit,
    SpecialSuccessorGeneratorMetrics,
    StaticInjectionAudit,
    StructuredAutomatonAudit,
    TwoPrimaryPurityProbe,
    TwoPrimaryResidualInterfaceAudit,
    TwoPrimaryResidualShape,
    TwoPrimaryShiftAudit,
)
from devtools.experiments.power_numbers.special_successor_purity import (
    _exact_target_hitting_times,
    boolean_set_audits,
    crt_purity_audits,
    image_filtration_audits,
    prime_group_depth_audits,
    residue_constraint_audits,
    static_injection_audits,
    structured_automaton_audits,
)
from devtools.experiments.power_numbers.special_successor_residual import (
    algebraic_block_observer_audits,
    behavioral_purity_block_audits,
    two_primary_residual_interface_audits,
    two_primary_shift_block_audits,
)
from devtools.paths import repository_root
from devtools.verification.oracles.special_binary_jump import (
    _fermat_carrier_proof,
    _mersenne_carrier_proof,
)
from number_compiler.arithmetic.functions.finite_unary import (
    minimize_unary_moore,
    partition_equivalent,
    unary_image_filtration,
)


def composite_depth_semantics_audit() -> CompositeDepthSemanticsAudit:
    """Reconstruct M11 image depth and target semantics without carry data."""
    family, parameter = "mersenne", 11
    proof = _mersenne_carrier_proof(parameter)
    filtration = unary_image_filtration(proof.transition)
    depth_ids = filtration.depth_ids
    moore = minimize_unary_moore(proof.transition, proof.outputs)
    hitting = _exact_target_hitting_times(proof.transition, proof.outputs)
    finite_depth_strata = tuple(
        sum(depth == level for depth in depth_ids)
        for level in range(filtration.finite_depths)
    )
    target_depths = tuple(
        sorted(
            {depth_ids[state] for state, output in enumerate(proof.outputs) if output}
        )
    )
    hitting_counts: dict[int, int] = {}
    never = 0
    for value in hitting:
        if value is None:
            never += 1
        else:
            hitting_counts[value] = hitting_counts.get(value, 0) + 1
    return CompositeDepthSemanticsAudit(
        family,
        parameter,
        filtration.ranks,
        finite_depth_strata,
        filtration.stable_states,
        filtration.finite_depths + 1,
        moore.classes,
        partition_equivalent(moore.class_ids, depth_ids),
        target_depths,
        sum(proof.outputs),
        tuple(sorted(hitting_counts.items())),
        never,
        depth_ids[proof.source_carrier],
        hitting[proof.source_carrier],
    )


def pure_two_group_audits() -> tuple[PureTwoGroupAudit, ...]:
    rows = []
    # Prime Fermat: F_n^* has order 2^N and the radix subgroup <2> has exact
    # order 2^(n+1), so the nonzero orbit quotient has order 2^(N-n-1).
    for n in (2, 3, 4):
        width = 1 << n
        proof = _fermat_carrier_proof(n)
        exponent = width - n - 1
        predicted = 1 << exponent
        rows.append(
            PureTwoGroupAudit(
                "fermat",
                n,
                exponent,
                predicted,
                proof.classes - 1,
                predicted == proof.classes - 1,
                "prime multiplicative group modulo exact radix-root subgroup; +1 carrier state is zero",
            )
        )
    # Prime Mersenne: the nonsplit norm-one torus has order M_p+1=2^p.  The
    # split/nonsplit discriminant character isolates this pure 2-group branch.
    for p in (5, 7, 13, 17, 19):
        modulus = (1 << p) - 1
        predicted = 1 << p
        rows.append(
            PureTwoGroupAudit(
                "mersenne",
                p,
                p,
                predicted,
                modulus + 1,
                predicted == modulus + 1,
                "prime nonsplit norm-one quadratic torus before inversion/trace quotient",
            )
        )
    return tuple(rows)


OrdinaryAuditParts = tuple[
    tuple[ImageFiltrationAudit, ...],
    tuple[ResidueConstraintAudit, ...],
    tuple[StaticInjectionAudit, ...],
    tuple[StructuredAutomatonAudit, ...],
    tuple[BooleanSetAudit, ...],
    tuple[PureTwoGroupAudit, ...],
    tuple[PrimeGroupDepthAudit, ...],
    tuple[CRTPurityAudit, ...],
    tuple[TwoPrimaryPurityProbe, ...],
    tuple[PurityCandidateAudit, ...],
    tuple[TwoPrimaryResidualInterfaceAudit, ...],
    tuple[TwoPrimaryShiftAudit, ...],
    tuple[BehavioralPurityBlockAudit, ...],
    tuple[AlgebraicBlockObserverAudit, ...],
    tuple[CarryTransferAutomatonAudit, ...],
    tuple[CarryCyclotomicTransducerAudit, ...],
    CompositeDepthSemanticsAudit,
    tuple[SpecialFactorShortCircuitAudit, ...],
]
HeavyAuditParts = tuple[
    tuple[CarryHenselCyclotomicAudit, ...],
    tuple[CarryTemporalAutomatonAudit, ...],
    tuple[CarryPhaseRefinementAudit, ...],
]
_AuditRecord = TypeVar("_AuditRecord")


def _ordinary_special_successor_parts() -> OrdinaryAuditParts:
    """Compute all bounded audits except the M17/reconstruction-heavy controls."""
    return (
        image_filtration_audits(),
        residue_constraint_audits(),
        static_injection_audits(),
        structured_automaton_audits(),
        boolean_set_audits(),
        pure_two_group_audits(),
        prime_group_depth_audits(),
        crt_purity_audits(),
        cheap_purity_probe_audits(),
        purity_candidate_audits(),
        two_primary_residual_interface_audits(),
        two_primary_shift_block_audits(),
        behavioral_purity_block_audits(),
        algebraic_block_observer_audits(),
        carry_transfer_automaton_audits(),
        carry_cyclotomic_transducer_audits(),
        composite_depth_semantics_audit(),
        special_factor_short_circuit_audits(),
    )


def _heavy_special_successor_parts() -> HeavyAuditParts:
    """Compute exhaustive negative/phase controls as one explicit audit group."""
    return (
        carry_hensel_cyclotomic_audits(),
        carry_temporal_automaton_audits(),
        carry_phase_refinement_audits(),
    )


def _run_audit_groups_isolated() -> tuple[OrdinaryAuditParts, HeavyAuditParts]:
    """Run the split audit groups concurrently in clean interpreters.

    The heavy controls now have physical module boundaries, so each gets its
    own worker instead of being serialized inside one oversized heavy worker.
    All children are explicitly joined or terminated; workers inherit no output
    stream that can outlive the parent.  The returned objects are small immutable
    audit records, never production sequence state.
    """
    root = repository_root()
    kinds = ("ordinary", "hensel", "temporal", "phase")
    with tempfile.TemporaryDirectory(prefix="special-successor-") as directory:
        directory_path = Path(directory)
        paths = {kind: directory_path / f"{kind}.pickle" for kind in kinds}
        env = dict(os.environ)
        processes: dict[str, subprocess.Popen[bytes]] = {}
        try:
            for kind in kinds:
                processes[kind] = subprocess.Popen(
                    [
                        sys.executable,
                        "-m",
                        "devtools.experiments.power_numbers.special_successor_worker",
                        kind,
                        str(paths[kind]),
                    ],
                    cwd=root,
                    env=env,
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.PIPE,
                )
            failures: list[tuple[str, int, str]] = []
            for kind, process in processes.items():
                _stdout, stderr = process.communicate()
                if process.returncode:
                    failures.append(
                        (
                            kind,
                            int(process.returncode),
                            stderr.decode("utf-8", errors="replace")[-4000:],
                        )
                    )
            if failures:
                raise RuntimeError(("isolated audit group failed", tuple(failures)))
        finally:
            for process in processes.values():
                if process.poll() is None:
                    process.terminate()
            for process in processes.values():
                if process.poll() is None:
                    try:
                        process.wait(timeout=2)
                    except subprocess.TimeoutExpired:
                        process.kill()
                        process.wait()
        ordinary: object = pickle.loads(paths["ordinary"].read_bytes())
        if not isinstance(ordinary, tuple) or len(ordinary) != 18:
            raise TypeError("ordinary audit worker returned another result schema")
        expected = (
            ImageFiltrationAudit,
            ResidueConstraintAudit,
            StaticInjectionAudit,
            StructuredAutomatonAudit,
            BooleanSetAudit,
            PureTwoGroupAudit,
            PrimeGroupDepthAudit,
            CRTPurityAudit,
            TwoPrimaryPurityProbe,
            PurityCandidateAudit,
            TwoPrimaryResidualInterfaceAudit,
            TwoPrimaryShiftAudit,
            BehavioralPurityBlockAudit,
            AlgebraicBlockObserverAudit,
            CarryTransferAutomatonAudit,
            CarryCyclotomicTransducerAudit,
            CompositeDepthSemanticsAudit,
            SpecialFactorShortCircuitAudit,
        )
        for index, (part, kind_type) in enumerate(zip(ordinary, expected, strict=True)):
            if index == 16:
                if not isinstance(part, CompositeDepthSemanticsAudit):
                    raise TypeError("depth audit has another record type")
            elif not isinstance(part, tuple) or any(
                not isinstance(item, kind_type) for item in part
            ):
                raise TypeError("ordinary audit has another record type")
        return cast(OrdinaryAuditParts, ordinary), (
            _load_audit_records(paths["hensel"], CarryHenselCyclotomicAudit),
            _load_audit_records(paths["temporal"], CarryTemporalAutomatonAudit),
            _load_audit_records(paths["phase"], CarryPhaseRefinementAudit),
        )


def _load_audit_records(
    path: Path, record_type: type[_AuditRecord]
) -> tuple[_AuditRecord, ...]:
    value: object = pickle.loads(path.read_bytes())
    if not isinstance(value, tuple) or any(
        not isinstance(item, record_type) for item in value
    ):
        raise TypeError("audit worker returned another record type")
    return cast(tuple[_AuditRecord, ...], value)


@lru_cache(maxsize=1)
def special_successor_generator_metrics() -> SpecialSuccessorGeneratorMetrics:
    """Return the complete audit from the four explicit modular workers.

    The split keeps peak construction costs independent and lets the bounded
    release audit use available cores without recreating one giant research
    module or retaining any worker state in production.
    """
    ordinary, heavy = _run_audit_groups_isolated()
    hensel, temporal, phase_refinement = heavy
    (
        filtrations,
        constraints,
        static,
        automata,
        boolean,
        groups,
        prime_depths,
        crt,
        cheap,
        candidates,
        residual,
        shifts,
        behavioral,
        algebraic,
        transfer,
        transducers,
        depth_guard,
        short_circuits,
    ) = ordinary
    return SpecialSuccessorGeneratorMetrics(
        filtrations,
        constraints,
        static,
        automata,
        boolean,
        groups,
        prime_depths,
        crt,
        cheap,
        candidates,
        residual,
        shifts,
        behavioral,
        algebraic,
        transfer,
        transducers,
        hensel,
        temporal,
        phase_refinement,
        depth_guard,
        short_circuits,
    )


def metrics_as_jsonable(metrics: SpecialSuccessorGeneratorMetrics) -> dict[str, object]:
    return asdict(metrics)


__all__ = [
    "AlgebraicBlockObserverAudit",
    "BehavioralPurityBlockAudit",
    "BooleanSetAudit",
    "CRTPurityAudit",
    "CarryCyclotomicTransducerAudit",
    "CarryHenselCyclotomicAudit",
    "CarryPhaseRefinementAudit",
    "CarryTemporalAutomatonAudit",
    "CarryTransferAutomatonAudit",
    "CompositeDepthSemanticsAudit",
    "ImageFiltrationAudit",
    "LocalTwoPrimaryComponent",
    "PrimeGroupDepthAudit",
    "PureTwoGroupAudit",
    "PurityCandidateAudit",
    "PurityWorkCost",
    "ResidueConstraintAudit",
    "SpecialFactorShortCircuitAudit",
    "SpecialSuccessorGeneratorMetrics",
    "StaticInjectionAudit",
    "StructuredAutomatonAudit",
    "TwoPrimaryPurityProbe",
    "TwoPrimaryResidualInterfaceAudit",
    "TwoPrimaryResidualShape",
    "TwoPrimaryShiftAudit",
    "algebraic_block_observer_audits",
    "behavioral_purity_block_audits",
    "boolean_set_audits",
    "bounded_special_factor_short_circuit",
    "carry_cyclotomic_transducer_audits",
    "carry_hensel_cyclotomic_audits",
    "carry_phase_refinement_audits",
    "carry_temporal_automaton_audits",
    "carry_transfer_automaton_audits",
    "cheap_purity_probe_audits",
    "cheap_two_primary_purity_probe",
    "composite_depth_semantics_audit",
    "crt_purity_audits",
    "image_filtration_audits",
    "metrics_as_jsonable",
    "prime_group_depth_audits",
    "pure_two_group_audits",
    "purity_candidate_audits",
    "residue_constraint_audits",
    "special_factor_short_circuit_audits",
    "special_successor_generator_metrics",
    "static_injection_audits",
    "structured_automaton_audits",
    "two_primary_residual_interface_audits",
    "two_primary_shift_block_audits",
]
