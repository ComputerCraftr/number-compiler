from number_compiler.sequences.power_numbers.frobenius_chunk import (
    SpecialFrobeniusChunkResult,
    SpecialFrobeniusChunkSpec,
    SpecialFrobeniusDefectPacket,
    classify_frobenius_chunk_defect,
    folded_x_coefficient_from_stride_residue,
    folded_x_defect_from_stride_residue,
    special_frobenius_chunk_probe,
    stride_zero_class,
)


def test_r_level_fold_keeps_only_stride_zero_class_without_polynomial_materialization() -> (
    None
):
    assert folded_x_coefficient_from_stride_residue(0, 7) == 1
    assert folded_x_coefficient_from_stride_residue(1 << 6, 7) == -1
    for rho in (1, 2, 3, 17, 63, 65, 127):
        if rho != 1 << 6:
            assert folded_x_coefficient_from_stride_residue(rho, 7) == 0
    assert stride_zero_class(0, 100_000)
    assert not stride_zero_class(1, 100_000)


def test_chunk_spec_is_log_description_even_for_huge_terminal_span() -> None:
    # No 2**span degree is ever constructed.  The spec retains only exponents.
    spec = SpecialFrobeniusChunkSpec(
        "fermat",
        16,
        1,
        (1 << 16) - 17,
        17,
        (1 << 16) + 1,
    )
    assert spec.base_stride_v2 == 17
    assert spec.required_local_v2 == 1 << 16
    assert spec.folded_half_degree_log2 == (1 << 16) - 1
    assert len(spec.canonical_key) == 7


def test_chunk_conjunction_composes_without_reopening_levels() -> None:
    first = SpecialFrobeniusChunkSpec("fermat", 5, 1, 8, 6, 33)
    second = first.adjacent(18)
    p = SpecialFrobeniusChunkResult(first, "ALL_PASS", "left", True)
    q = SpecialFrobeniusChunkResult(second, "ALL_PASS", "right", True)
    both = p.compose(q)
    assert both.status == "ALL_PASS"
    assert both.spec.start_level == 1 and both.spec.span == 26
    assert both.one_level_replays == 0
    assert both.polynomial_terms_materialized == 0

    fail = SpecialFrobeniusChunkResult(
        second,
        "ALL_FAIL",
        "right-fail",
        False,
        first_failure_offset=2,
    )
    stopped = p.compose(fail)
    assert stopped.status == "ALL_FAIL"
    assert stopped.first_failure_offset == 10

    unknown = SpecialFrobeniusChunkResult(first, "UNKNOWN", "left-unknown")
    assert unknown.compose(q).status == "UNKNOWN"


def test_candidate_probe_is_explicit_fail_closed_zero_work_surface() -> None:
    spec = SpecialFrobeniusChunkSpec("mersenne", 13, 1, 11, 2, 13)
    row = special_frobenius_chunk_probe(spec)
    assert row.status == "UNKNOWN"
    assert row.method == "frobenius-chunk-zero-class-extractor-unavailable"
    assert row.zero_class is None
    assert row.polynomial_terms_materialized == 0
    assert row.one_level_replays == 0
    assert row.raw_trace_squarings == 0
    assert row.factor_enumeration == 0


def test_defect_packet_turns_local_zero_class_into_exact_gcd_classification() -> None:
    spec = SpecialFrobeniusChunkSpec("fermat", 4, 1, 3, 5, 17)
    passed = classify_frobenius_chunk_defect(spec, 65537, 0, method="test-defect")
    assert passed.status == "ALL_PASS"

    failed = classify_frobenius_chunk_defect(spec, 65537, -1, method="test-defect")
    assert failed.status == "ALL_FAIL"

    # Mixed support: zero on 17, unit on 41.  The one gcd returns the passing
    # packet without any sign/product cancellation.
    modulus = 17 * 41
    defect = 17  # 0 mod 17 and a unit mod 41
    split = SpecialFrobeniusDefectPacket(spec, modulus, defect, "test-mixed").classify()
    assert split.status == "SPLIT"
    assert split.gcd_packet == 17

    assert folded_x_defect_from_stride_residue(0, 5) == 0
    assert folded_x_defect_from_stride_residue(1, 5) == -1
    assert folded_x_defect_from_stride_residue(16, 5) == -2
