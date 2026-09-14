from math import gcd, isqrt
from pathlib import Path
from typing import Protocol, cast

import pytest

from devtools.experiments.power_numbers.special_transverse_jet import (
    SpecialJetProgressionSpec,
    build_special_jet_interval,
    special_jet_window_search_audit,
    transverse_jet_coefficient_mod,
)
from number_compiler.sequences.power_numbers.terminal_threshold import (
    terminal_threshold_probe,
)
from number_compiler.sequences.power_numbers.transverse_pullback import (
    CompactTransverseHolonomyPullback,
    SpecialTransverseWindow,
    build_compact_transverse_pullback,
)


class _PullbackConstructorWithUnit(Protocol):
    def __call__(
        self,
        family: str,
        parameter: int,
        odd_part: int,
        window: SpecialTransverseWindow,
        *,
        unit: bool,
    ) -> CompactTransverseHolonomyPullback: ...


@pytest.mark.parametrize(
    ("family", "parameter", "slots"),
    (
        ("fermat", 4, 3),
        ("fermat", 5, 511),
        ("mersenne", 11, 2),
        ("mersenne", 13, 3),
        ("mersenne", 29, 399),
    ),
)
def test_compact_transverse_window_matches_exact_sqrt_frontier(
    family: str, parameter: int, slots: int
) -> None:
    pullback = build_compact_transverse_pullback(family, parameter)
    assert pullback.window.materialize(maximum_slots=slots) == slots
    assert not pullback.window.contains(slots + 1)
    modulus = (
        (1 << (1 << parameter)) + 1 if family == "fermat" else (1 << parameter) - 1
    )
    assert slots == (isqrt(modulus) - 1) // pullback.window.stride


def test_production_transverse_pullback_is_compact_and_fail_closed() -> None:
    for family, parameter in (
        ("fermat", 4),
        ("fermat", 5),
        ("mersenne", 11),
        ("mersenne", 13),
        ("mersenne", 29),
    ):
        pullback = build_compact_transverse_pullback(family, parameter)
        assert not pullback.decided
        assert pullback.unit is None and pullback.annihilator is None
        assert pullback.method == "transverse-holonomy-pullback-unresolved"
        assert pullback.atom_evaluations == 0
        assert pullback.product_multiplications == 0
        assert pullback.factor_enumeration == 0
        row = terminal_threshold_probe(family, parameter)
        assert row.status == "UNKNOWN"
        assert row.method == pullback.method
        assert row.transverse_window == pullback.window
        assert row.transverse_pullbacks == 1
        assert row.transverse_atom_evaluations == 0
        assert row.transverse_product_multiplications == 0


def test_large_transverse_window_is_rejected_by_slot_cap_without_lowering() -> None:
    pullback = build_compact_transverse_pullback("fermat", 19)
    assert pullback.window.exceeds(4096)
    with pytest.raises(ValueError, match="exceeds maximum_slots"):
        pullback.window.materialize(maximum_slots=4096)


def test_terminal_probe_admits_candidate_before_building_large_metadata(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.sequences.power_numbers.terminal_threshold as terminal

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("terminal metadata built before candidate admission")

    monkeypatch.setattr(terminal, "terminal_threshold_spec", forbidden)
    with pytest.raises(ValueError, match="exceeds max_candidate_bits"):
        terminal.terminal_threshold_probe("fermat", 1_000_001)


def test_compact_builder_rejects_non_exact_candidate_parameters() -> None:
    with pytest.raises(ValueError, match="special parameter"):
        build_compact_transverse_pullback("fermat", cast(int, 4.0))


def test_transverse_window_rejects_forged_progressions() -> None:
    for forged in (
        ("fermat", 2, 1),
        ("fermat", 4, 32),
        ("mersenne", 11, 24),
        ("mersenne", 15, 30),
    ):
        with pytest.raises(ValueError, match="canonical progression"):
            SpecialTransverseWindow(*forged)


def test_compact_descriptor_cannot_accept_a_caller_decision() -> None:
    window = SpecialTransverseWindow("mersenne", 11, 22)
    with pytest.raises(TypeError, match="unexpected keyword argument 'unit'"):
        cast(_PullbackConstructorWithUnit, CompactTransverseHolonomyPullback)(
            "mersenne", 11, 11, window, unit=True
        )


def test_semantic_oracle_reproduces_unit_split_and_full_controls() -> None:
    expected = {
        ("fermat", 4): ("CLEAR", 1, None, 3, 2),
        ("fermat", 5): ("SPLIT", 641, 641, 511, 510),
        ("mersenne", 11): ("SPLIT", 23, 23, 2, 1),
        ("mersenne", 13): ("CLEAR", 1, None, 3, 2),
        # All three prime factors occur in the progression.  The root gcd is
        # N, so only interval descent may print the proper leaf factor 233.
        ("mersenne", 29): ("FULL", 536_870_911, 233, 399, 398),
    }
    for key, values in expected.items():
        spec = SpecialJetProgressionSpec.build(*key)
        block = build_special_jet_interval(spec, 1, spec.max_slot)
        status, root_gcd, factor, atoms, products = values
        assert (
            block.status,
            block.support_gcd,
            block.atom_evaluations,
            block.multiplications,
        ) == (status, root_gcd, atoms, products)
        assert gcd(block.product, spec.modulus) == root_gcd
        if factor is not None:
            row = special_jet_window_search_audit(*key)
            assert row.proper_factor == factor
            assert 1 < factor < spec.modulus and spec.modulus % factor == 0
            assert row.factor_enumeration == 0


def test_semantic_holonomy_product_does_not_consume_factor_witness(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import devtools.experiments.power_numbers.special_transverse_jet as oracle

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("factor witness entered holonomy product construction")

    monkeypatch.setattr(oracle, "batched_special_factor_witness", forbidden)
    spec = oracle.SpecialJetProgressionSpec.build("mersenne", 29)
    block = oracle.build_special_jet_interval(spec, 1, spec.max_slot)
    assert block.status == "FULL"
    assert block.support_gcd == spec.modulus


def test_m11_transverse_connection_reaches_exact_annihilator_without_factor_oracle(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import devtools.experiments.power_numbers.special_transverse_jet as oracle

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("factor oracle entered transverse coefficient construction")

    monkeypatch.setattr(oracle, "batched_special_factor_witness", forbidden)
    modulus = 2047
    assert all(
        transverse_jet_coefficient_mod(modulus, order) == 0 for order in range(1, 23)
    )
    coefficient = transverse_jet_coefficient_mod(modulus, 23)
    assert coefficient == 89
    assert 23 * coefficient == modulus
    assert gcd(23, modulus) == 23
    assert gcd(coefficient, modulus) == 89


def test_production_transverse_owner_has_no_oracle_or_factor_scan_import() -> None:
    import number_compiler.sequences.power_numbers.transverse_pullback as owner

    source = Path(owner.__file__).read_text()
    for forbidden in (
        "from devtools",
        "import devtools",
        "factor_morphism",
        "smallest_factor",
        "pepin",
        "lucas_lehmer",
        "build_special_jet_interval",
    ):
        assert forbidden not in source.lower()
