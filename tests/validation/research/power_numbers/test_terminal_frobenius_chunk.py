from devtools.experiments.power_numbers.terminal_frobenius_chunk import (
    special_frobenius_defect_crt_audit,
)


def test_complete_factor_audit_proves_one_defect_gcd_is_sufficient() -> None:
    f4 = special_frobenius_defect_crt_audit("fermat", 4, 2, 2, (65537,))
    assert f4.status == "ALL_PASS" and f4.support_gcd == 65537

    f5 = special_frobenius_defect_crt_audit("fermat", 5, 2, 9, (641, 6700417))
    assert f5.status == "ALL_FAIL" and f5.support_gcd == 1

    m13 = special_frobenius_defect_crt_audit("mersenne", 13, 1, 3, (8191,))
    assert m13.status == "ALL_PASS" and m13.support_gcd == 8191

    m11 = special_frobenius_defect_crt_audit("mersenne", 11, 1, 2, (23, 89))
    assert m11.status == "ALL_FAIL" and m11.support_gcd == 1

    for row in (f4, f5, m13, m11):
        assert row.polynomial_terms_materialized == 0
        assert row.one_level_replays == 0
