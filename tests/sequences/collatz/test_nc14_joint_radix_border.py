"""Source-bound CRT and typed finite-candidate regressions for Collatz."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.fields.three_power_radix import ThreePowerRadixOrbit
from number_compiler.arithmetic.fields.walsh import walsh64_mod5
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.border_identity import (
    CYCLE_89,
    ENTRY_89_AT_NINE,
    ENTRY_421,
    ENTRY_26847_PHASES,
    CycleEntryPhase,
    selector_guard_for,
)
from number_compiler.sequences.collatz.boundary_macros import (
    BoundaryActionTemplateMemo,
    admit_boundary_macro_plan,
)
from number_compiler.sequences.collatz.joint_radix_border import (
    JointRadix6Source,
    border_crt_moore,
    candidate_family_for_residue160,
    candidate_family_guard,
)
from number_compiler.sequences.collatz.unified_skew_chain import (
    select_unified_skew_chain,
)


def test_source_crt_coordinates_are_exact_and_reject_poison() -> None:
    for source in range(1, 2_001):
        state = JointRadix6Source.from_source(source)
        assert state.residue5 == source % 5
        assert state.low_binary == source % 32
        for modulus in (10, 20, 40, 80, 160):
            assert state.decimal_residue(modulus) == source % modulus
        for position in range(5):
            assert state.radix6_digit(position) == source // 6**position % 6
    with pytest.raises(ValueError, match="F5"):
        JointRadix6Source(63, 0, 31, 63)
    with pytest.raises(ValueError, match="foreign"):
        JointRadix6Source.from_source(63).require_source(64)


def test_complete_moore_graph_is_a_typed_finite_audit() -> None:
    machine = border_crt_moore()
    assert machine.classes == 155
    assert machine.rounds > 1
    assert machine.family(JointRadix6Source.from_source(19)) == ENTRY_89_AT_NINE
    for residue in range(160):
        state = JointRadix6Source.from_source(residue or 160)
        class_id = machine.control(state)
        for lift_bit in (0, 1):
            lifted = residue + 160 * lift_bit
            endpoint = lifted // 2 if lifted % 2 == 0 else (3 * lifted + 1) // 2
            assert (
                machine.successors[class_id][lift_bit]
                == machine.class_ids[endpoint % 160]
            )


def test_production_selector_uses_crt_candidate_but_keeps_exact_guard() -> None:
    state = JointRadix6Source.from_source(19)
    plan = admit_boundary_macro_plan(19, 128, minimum_repetitions=1, radix_state=state)
    assert plan is not None and plan.identity == ENTRY_89_AT_NINE
    assert plan.source == 19 and plan.maximum_repetitions >= plan.repetitions >= 1
    with pytest.raises(ValueError, match="foreign"):
        admit_boundary_macro_plan(20, 128, radix_state=state)


def test_candidate_projection_uses_the_identitys_guarded_phase_records() -> None:
    assert candidate_family_guard(ENTRY_421) == (4, 40, 5)
    assert candidate_family_for_residue160(112) == ENTRY_26847_PHASES[0]
    assert selector_guard_for(ENTRY_26847_PHASES[3]).wire_value() == (34, 40, 1)
    assert selector_guard_for(ENTRY_89_AT_NINE).wire_value() == (9, 10, 1)
    with pytest.raises(ValueError, match="no finite selector guard"):
        selector_guard_for(CycleEntryPhase(CYCLE_89, 0))


def test_f5_is_transported_by_issued_action_before_following_selection() -> None:
    with BoundaryActionTemplateMemo(ResourceLedger()) as templates:
        chain = select_unified_skew_chain(19, 128, templates=templates)
    assert chain is not None
    chain.verify()
    first, second = chain.seams[:2]
    assert first.joint_source == JointRadix6Source.from_source(19)
    transported = first.joint_endpoint
    assert transported is not None
    assert transported == second.joint_source
    assert transported.residue5 == first.endpoint % 5
    assert transported.candidate_family is not None
    assert second.source == first.endpoint


def test_shared_radix_orbit_and_walsh_are_demanded_from_same_event_count() -> None:
    orbit = ThreePowerRadixOrbit("ordinary", 7, 64)
    mask = orbit.forward_mask(64, "forward_difference_xor")
    transform = walsh64_mod5(mask)
    assert len(transform) == 64
    assert orbit.tape(64)[-1].position == 64
