from devtools.experiments.power_numbers.special_binary_germ import (
    special_binary_germ_truth_audit,
)
from number_compiler.arithmetic.fields.morphism_core import (
    binary_power_composition_count,
)
from number_compiler.projection.output_quotient import SpecialBranchMask
from number_compiler.sequences.power_numbers.frobenius_chunk import (
    SpecialFrobeniusChunkSpec,
    SpecialFrobeniusDefectPacket,
)
from number_compiler.sequences.power_numbers.germ import (
    SpecialGermConstraintState,
    SpecialGermTransfer,
    build_special_germ_plan,
    compose_support_packets,
)
from number_compiler.sequences.power_numbers.terminal_threshold import (
    prime_decision_chunk_spec,
    terminal_threshold_spec,
)


def test_special_germ_transport_is_binary_powered_not_level_replayed() -> None:
    for family in ("fermat", "mersenne"):
        atom = SpecialGermTransfer.atom(family)
        for span in (1, 2, 3, 9, 26, 1_000_003):
            block = atom.power_block(span)
            assert block.span == span
            assert block.endpoint_power.depth == span
            assert block.compositions == binary_power_composition_count(span)
            assert block.compositions <= 2 * span.bit_length()


def test_terminal_germ_plan_has_no_detached_support_observation() -> None:
    for family, parameter in (
        ("fermat", 4),
        ("fermat", 5),
        ("mersenne", 11),
        ("mersenne", 13),
    ):
        spec = prime_decision_chunk_spec(terminal_threshold_spec(family, parameter))
        plan = build_special_germ_plan(spec)
        assert plan.endpoint_level == spec.end_level
        assert plan.support_observations == 0
        assert plan.constraints.mask.bits == 0b11
        assert plan.constraints.checks == 0
        assert plan.one_level_replays == 0
        assert plan.factor_enumeration == 0
        assert plan.root_tree_nodes == 0
        assert plan.binary_compositions == binary_power_composition_count(spec.span)


def test_support_packet_intersection_is_non_cancelling_and_associative_on_support() -> (
    None
):
    modulus = 17 * 41 * 73
    a = SpecialFrobeniusChunkSpec("fermat", 9, 1, 1, 10, modulus.bit_length())
    b = a.adjacent(1)
    c = b.adjacent(1)

    # Pass sets by prime component:
    # A={17,41}, B={17,73}, C={17,41,73}.  The conjunction is {17}.
    pa = SpecialFrobeniusDefectPacket(a, modulus, 17 * 41, "a")
    pb = SpecialFrobeniusDefectPacket(b, modulus, 17 * 73, "b")
    pc = SpecialFrobeniusDefectPacket(c, modulus, 17 * 41 * 73, "c")

    left = compose_support_packets(compose_support_packets(pa, pb), pc)
    right = compose_support_packets(pa, compose_support_packets(pb, pc))
    assert left.support_gcd == right.support_gcd == 17
    assert left.classify().status == right.classify().status == "SPLIT"
    assert left.classify().gcd_packet == right.classify().gcd_packet == 17


def test_factor_backed_adversaries_validate_the_new_support_semantics() -> None:
    expected = {
        ("fermat", 4): "ALL_PASS",
        ("fermat", 5): "ALL_FAIL",
        ("mersenne", 11): "ALL_FAIL",
        ("mersenne", 13): "ALL_PASS",
    }
    for key, status in expected.items():
        row = special_binary_germ_truth_audit(*key)
        assert row.endpoint_result.status == status
        assert row.composed_result.status == status
        assert row.exact
        assert row.binary_transport_is_logarithmic
        assert row.source_support_observations == 1
        assert row.factor_enumeration >= 1  # audit truth, never production


def test_direct_endpoint_support_equals_intersection_of_all_level_supports() -> None:
    # This freezes the prime-clock analogy: exact support can be accumulated
    # without signs/phases, while production needs only the final endpoint bit.
    for family, parameter in (
        ("fermat", 4),
        ("fermat", 5),
        ("mersenne", 11),
        ("mersenne", 13),
    ):
        row = special_binary_germ_truth_audit(family, parameter)
        assert row.exact
        assert row.endpoint_result.gcd_packet == row.composed_result.gcd_packet


def test_production_binary_germ_plan_remains_fail_closed_without_pulled_back_evidence() -> (
    None
):
    for family, parameter in (
        ("fermat", 4),
        ("fermat", 5),
        ("mersenne", 11),
        ("mersenne", 13),
    ):
        spec = prime_decision_chunk_spec(terminal_threshold_spec(family, parameter))
        row = build_special_germ_plan(spec).probe()
        assert row.status == "UNKNOWN"
        assert row.method == "constraint-pullback-unresolved"
        assert row.polynomial_terms_materialized == 0
        assert row.one_level_replays == 0
        assert row.raw_trace_squarings == 0
        assert row.factor_enumeration == 0


def test_downstream_branch_mask_is_pulled_back_through_adjacent_germ_transport() -> (
    None
):
    a = SpecialFrobeniusChunkSpec("fermat", 9, 1, 2, 10, 65)
    b = a.adjacent(3)
    left = build_special_germ_plan(a)
    right = build_special_germ_plan(b).pullback_mask(
        SpecialBranchMask(0b01),
        method="forced-output-digit",
    )
    combined = left.then(right)
    assert combined.spec.span == 5
    assert combined.constraints.mask.bits == 0b01
    assert combined.constraints.checks == 1
    assert combined.constraints.pullbacks == 2
    assert combined.probe().status == "ALL_PASS"
    assert combined.factor_enumeration == 0 and combined.one_level_replays == 0


def test_candidate_support_ideals_intersect_inside_constrained_germ_without_slot_lists() -> (
    None
):
    modulus = 17 * 41 * 73
    a = SpecialFrobeniusChunkSpec("fermat", 9, 1, 1, 10, modulus.bit_length())
    b = a.adjacent(1)
    c = b.adjacent(1)
    pa = build_special_germ_plan(a).pullback_defect(
        modulus,
        17 * 41,
        method="a-defect",
    )
    pb = build_special_germ_plan(b).pullback_defect(
        modulus,
        17 * 73,
        method="b-defect",
    )
    pc = build_special_germ_plan(c).pullback_defect(
        modulus,
        modulus,
        method="c-defect",
    )
    combined = pa.then(pb).then(pc)
    assert combined.constraints.support_modulus == modulus
    assert combined.constraints.support_gcd == 17
    assert combined.constraints.checks == 3
    assert combined.constraints.pullbacks == 5
    row = combined.probe()
    assert row.status == "SPLIT" and row.gcd_packet == 17
    assert combined.support_observations == 0


def test_constraint_state_rank_does_not_grow_with_repeated_mask_pullback() -> None:
    state = SpecialGermConstraintState.identity()
    for index in range(1000):
        mask = SpecialBranchMask(0b11 if index < 999 else 0b10)
        state = state.then(
            SpecialGermConstraintState.from_mask(mask, method=f"k{index}")
        )
    assert state.mask.bits == 0b10
    assert state.checks == 1000
    # State still owns one two-bit mask and no hidden factor-slot carrier.
    assert state.support_modulus is None and state.support_gcd is None
    assert state.method == "mixed-constraint-pullback"
