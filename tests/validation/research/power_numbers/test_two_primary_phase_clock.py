from devtools.benchmarks.two_primary_phase_clock_probe import (
    two_primary_depth_view_audits,
    two_primary_phase_clock_audits,
)


def test_complete_bounded_phase_clock_matches_independent_moore_partition() -> None:
    rows = two_primary_phase_clock_audits()
    fermat = [row for row in rows if row.family == "fermat"]
    mersenne = [row for row in rows if row.family == "mersenne"]

    assert [row.independent_moore_classes for row in fermat] == [5, 9, 17]
    assert {row.carrier_scope for row in fermat} == {"complete-residue-ring"}
    assert [row.depth_action_classes for row in fermat] == [5, 9, 17]
    assert all(row.candidate_prime and row.pure_order_admitted for row in fermat)
    assert all(row.moore_equals_depth_action for row in fermat)

    assert [row.parameter for row in mersenne] == [5, 7, 11, 13]
    assert {row.carrier_scope for row in mersenne} == {
        "generated-quadratic-unit-trace-orbit"
    }
    assert [row.independent_moore_classes for row in mersenne] == [5, 7, 1, 13]
    assert [row.depth_action_classes for row in mersenne] == [5, 7, None, 13]
    assert [row.concrete_generator_order for row in mersenne] == [32, 128, 990, 8192]
    assert not mersenne[2].candidate_prime
    assert not mersenne[2].pure_order_admitted
    assert not mersenne[2].target_present
    assert not mersenne[2].moore_equals_depth_action
    assert mersenne[2].full_carrier_derived_view_classes is None
    assert mersenne[2].full_carrier_enriched_classes is None
    assert mersenne[2].full_carrier_views_refine_action is None

    admitted = fermat + [mersenne[0], mersenne[1], mersenne[3]]
    for row in admitted:
        assert row.moore_equals_depth_action
        assert row.independent_moore_classes == row.expected_prime_classes
        assert row.direct_jump_checks > 0
        assert row.direct_jump_primitive_successors == 0
        assert row.action_cache_second_lookup_hits == 1
        assert row.exact_phase_is_occurrence_payload
        assert row.full_carrier_derived_view_classes in (2, 3, 4)
        assert row.full_carrier_enriched_classes == row.independent_moore_classes
        assert row.full_carrier_views_refine_action is False
        assert row.full_carrier_dead_sink_objects == 1
        assert not row.scheduler_admitted
        assert row.measured_horizons[4:] == (
            16,
            32,
            64,
            128,
            256,
            512,
            1_024,
            10**12,
        )
        assert all(
            bits == 0
            for horizon, bits in zip(
                row.measured_horizons, row.retained_source_phase_bits, strict=True
            )
            if horizon >= 16
        )


def test_bounded_compilation_work_is_charged_outside_direct_jump() -> None:
    rows = two_primary_phase_clock_audits()
    for row in rows:
        assert row.generator_enumeration_rows == row.concrete_generator_order
        assert row.generator_multiplications == row.concrete_generator_order
        assert row.carrier_rows > 0
        assert row.direct_jump_primitive_successors == 0
    assert [row.phase_lookup_rows for row in rows] == [
        16,
        256,
        65_536,
        17,
        65,
        0,
        4_097,
    ]


def test_depth_views_do_not_refine_prime_source_moore_clocks() -> None:
    rows = two_primary_depth_view_audits()
    primes = rows[:6]
    assert [(row.family, row.parameter) for row in primes] == [
        ("fermat", 2),
        ("fermat", 3),
        ("fermat", 4),
        ("mersenne", 5),
        ("mersenne", 7),
        ("mersenne", 13),
    ]
    for row in primes:
        assert row.remaining_matches_source_moore
        assert row.derived_views_refine_source_moore is False
        assert row.point_observer_and_survival_observer_agree
        assert row.enriched_source_classes == row.source_moore_classes_seen
        assert row.dead_sink_objects == 1
        assert not row.extraction_candidate_derived
        assert not row.scheduler_admitted


def test_composite_depth_profiles_remain_conditional_and_m11_separates_observers() -> (
    None
):
    controls = two_primary_depth_view_audits()[6:]
    assert [row.local_depths for row in controls] == [
        (1, 1),
        (6, 1),
        (0, 0),
        (0, 0, 1),
    ]
    assert [row.minimum_local_depth for row in controls] == [1, 1, 0, 0]
    assert all(row.profile_source == "supplied-local-germ-control" for row in controls)
    assert all(row.dead_sink_objects == 1 for row in controls)
    assert controls[0].remaining_depth_classes == controls[1].remaining_depth_classes

    m11 = controls[2]
    assert m11.bounded_moore_classes == 3
    assert m11.source_moore_classes_seen == 1
    assert m11.enriched_source_classes == 2
    assert m11.remaining_matches_source_moore is False
    assert m11.derived_views_refine_source_moore
    assert m11.point_observer_and_survival_observer_agree is False
    assert controls[0].bounded_moore_classes is None
    assert controls[1].bounded_moore_classes is None
    assert controls[3].bounded_moore_classes is None
