from devtools.experiments.power_numbers.special_source_residual import (
    source_bend_global_lower_bound,
    source_bend_residual_audit,
)


def test_local_bend_translation_language_has_exact_q_residual_classes() -> None:
    f5 = source_bend_residual_audit("fermat", 5, 641)
    m11 = source_bend_residual_audit("mersenne", 11, 23)
    m29 = source_bend_residual_audit("mersenne", 29, 233)
    assert (f5.bend_residue, f5.exact_residual_classes) == (5, 641)
    assert (m11.bend_residue, m11.exact_residual_classes) == (1, 23)
    assert (m29.bend_residue, m29.exact_residual_classes) == (4, 233)
    assert all(row.binary_translation_powerable for row in (f5, m11, m29))
    assert not any(row.source_injection_closed for row in (f5, m11, m29))


def test_global_source_observer_inherits_a_hidden_factor_sized_residual_lower_bound() -> (
    None
):
    f5 = source_bend_global_lower_bound("fermat", 5, (641, 6700417))
    m29 = source_bend_global_lower_bound("mersenne", 29, (233, 1103, 2089))
    assert f5.largest_local_residual_classes == 6700417
    assert f5.complete_factorization
    assert m29.largest_local_residual_classes == 2089
    assert m29.complete_factorization
