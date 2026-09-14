"""Exact bounded candidate filtration oracle.

This is the historical finite-carrier constructor used only for differential
validation.  It is intentionally outside the production import graph.
"""

from __future__ import annotations

from collections import Counter

from devtools.proofs.oracles.special_binary_jump import (
    _fermat_carrier_proof,
    _mersenne_carrier_proof,
    _SpecialCarrierProof,
)
from number_compiler.arithmetic.functions.finite_unary import (
    minimize_unary_moore,
    partition_equivalent,
    quotient_machine_from_moore,
    unary_image_filtration,
)
from number_compiler.arithmetic.polynomials.two_primary_filtration import (
    TwoPrimaryImageFiltration,
)


def _source_hitting_time(
    transition: tuple[int, ...],
    outputs: tuple[bool, ...],
    source: int,
) -> int | None:
    state = int(source)
    seen: set[int] = set()
    steps = 0
    while state not in seen:
        if outputs[state]:
            return steps
        seen.add(state)
        state = transition[state]
        steps += 1
    return None


def _candidate_filtration_from_proof(
    proof: _SpecialCarrierProof, *, expected_raw_step: int
) -> TwoPrimaryImageFiltration:
    filtration = unary_image_filtration(proof.transition)
    moore = minimize_unary_moore(proof.transition, proof.outputs)
    machine = quotient_machine_from_moore(
        proof.transition, proof.outputs, moore.class_ids
    )
    source_class = moore.class_ids[proof.source_carrier]
    depth_counts = Counter(depth for depth in filtration.depth_ids if depth >= 0)
    depth_strata = tuple(
        depth_counts[level] for level in range(filtration.finite_depths)
    )
    target_depths = tuple(
        sorted(
            {
                filtration.depth_ids[index]
                for index, output in enumerate(proof.outputs)
                if output
            }
        )
    )
    quotient_hitting = _source_hitting_time(
        proof.transition, proof.outputs, proof.source_carrier
    )
    expected_quotient_step = int(expected_raw_step) - int(proof.offset)
    if expected_quotient_step < 0:
        raise ValueError((expected_raw_step, proof.offset))
    state, _ops, _nodes = machine.power_state(source_class, expected_quotient_step)
    target = bool(machine.output(state))
    moore_image_exact = partition_equivalent(moore.class_ids, filtration.depth_ids)
    pure_shape = bool(
        target
        and moore_image_exact
        and filtration.depth_ids[proof.source_carrier] == 0
        and len(target_depths) == 1
    )
    return TwoPrimaryImageFiltration(
        proof.family,
        proof.parameter,
        int(proof.raw_source_states).bit_length(),
        proof.offset,
        filtration.ranks,
        depth_strata,
        filtration.stable_states,
        filtration.depth_ids[proof.source_carrier],
        target_depths,
        moore.classes,
        filtration.finite_depths + 1,
        moore_image_exact,
        None if quotient_hitting is None else quotient_hitting + proof.offset,
        int(expected_raw_step),
        target,
        pure_shape,
        "bounded-candidate-image-filtration",
        proof.proof_states_examined,
        proof.construction_raw_squarings,
        0,
        0,
        0,
        False,
        machine,
        source_class,
    )


def bounded_candidate_image_filtration(
    family: str,
    parameter: int,
    *,
    max_fermat_width: int = 16,
    max_mersenne_exponent: int = 13,
) -> TwoPrimaryImageFiltration:
    family = str(family)
    parameter = int(parameter)
    if family == "fermat":
        width = 1 << parameter
        proof = _fermat_carrier_proof(parameter, max_width=max_fermat_width)
        return _candidate_filtration_from_proof(proof, expected_raw_step=width - 1)
    if family == "mersenne":
        proof = _mersenne_carrier_proof(parameter, max_exponent=max_mersenne_exponent)
        return _candidate_filtration_from_proof(proof, expected_raw_step=parameter - 2)
    raise ValueError(family)


__all__ = ["bounded_candidate_image_filtration"]
