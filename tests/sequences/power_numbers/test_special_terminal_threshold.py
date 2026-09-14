from __future__ import annotations

import pytest

from number_compiler.sequences.power_numbers.certificate import (
    fermat_depth_certificate,
    mersenne_depth_certificate,
)
from number_compiler.sequences.power_numbers.terminal_threshold import (
    fermat_terminal_threshold_spec,
    mersenne_terminal_threshold_spec,
    prime_decision_chunk_spec,
    terminal_threshold_probe,
    terminal_threshold_spec,
)


def test_terminal_threshold_specs_keep_full_horizon_but_use_sqrt_prime_decision_levels() -> (
    None
):
    f4 = fermat_terminal_threshold_spec(4)
    assert f4.terminal_level == 11
    assert f4.baseline_local_v2 == 5
    assert f4.required_local_v2 == 16
    assert f4.prime_decision_level == 3
    assert f4.prime_decision_required_local_v2 == 8
    assert f4.pass_iff_prime

    f5 = terminal_threshold_spec("fermat", 5)
    assert f5.terminal_level == 26
    assert f5.prime_decision_level == 10
    assert f5.prime_decision_required_local_v2 == 16

    m13 = mersenne_terminal_threshold_spec(13)
    assert m13.terminal_level == 11
    assert m13.baseline_local_v2 == 2
    assert m13.required_local_v2 == 13
    assert m13.prime_decision_level == 3
    assert m13.prime_decision_required_local_v2 == 5
    assert m13.prime_decision_proof_method == "mersenne-crt-torus-sqrt-bound"
    assert m13.pass_iff_prime

    m11 = terminal_threshold_spec("mersenne", 11)
    assert m11.terminal_level == 9
    assert m11.prime_decision_level == 2
    assert m11.prime_decision_required_local_v2 == 4


def test_prime_decision_chunk_skips_the_universally_free_first_fermat_lift() -> None:
    f4 = prime_decision_chunk_spec(fermat_terminal_threshold_spec(4))
    assert f4.start_level == 2
    assert f4.span == 2
    assert f4.base_stride_v2 == 6
    assert f4.required_local_v2 == 8

    f5 = prime_decision_chunk_spec(fermat_terminal_threshold_spec(5))
    assert f5.start_level == 2
    assert f5.span == 9
    assert f5.base_stride_v2 == 7
    assert f5.required_local_v2 == 16

    m13 = prime_decision_chunk_spec(mersenne_terminal_threshold_spec(13))
    assert m13.start_level == 1
    assert m13.span == 3
    assert m13.base_stride_v2 == 2
    assert m13.required_local_v2 == 5


def test_terminal_query_is_fail_closed_and_never_hides_recurrence_or_carrier_work() -> (
    None
):
    f2 = terminal_threshold_probe("fermat", 2)
    assert f2.status == "ALL_PASS"
    assert f2.level == 1
    assert f2.root_witness == 11
    assert f2.witness_power_residue == 2
    assert f2.carrier_states_enumerated == 0
    assert f2.raw_specialization_squarings == 0

    # F3 and M3 are now structural square-root-bound passes: their guaranteed
    # local congruence already puts every possible prime divisor above sqrt(N).
    f3 = terminal_threshold_probe("fermat", 3)
    assert f3.status == "ALL_PASS" and f3.level == 0
    assert f3.method == "fermat-sqrt-divisor-lower-bound"
    m3 = terminal_threshold_probe("mersenne", 3)
    assert m3.status == "ALL_PASS" and m3.level == 0
    assert m3.method == "explicit-small-mersenne"

    for p in (5, 7):
        row = terminal_threshold_probe("mersenne", p)
        assert row.status == "ALL_PASS" and row.level == 0
        assert row.method == "mersenne-order-divisor-sqrt-bound"

    for family, parameter, level in (
        ("fermat", 4, 3),
        ("fermat", 5, 10),
        ("mersenne", 11, 2),
        ("mersenne", 13, 3),
        ("mersenne", 17, 3),
    ):
        row = terminal_threshold_probe(family, parameter)
        assert row.status == "UNKNOWN"
        assert row.level == level
        assert row.carrier_states_enumerated == 0
        assert row.raw_specialization_squarings == 0


def test_production_certificate_keeps_missing_terminal_extractor_unresolved() -> None:
    f2 = fermat_depth_certificate(2)
    assert f2.status == "prime"
    assert f2.method.startswith("terminal-threshold:")
    assert f2.scalable_construction
    assert f2.carrier_states_enumerated == 0
    assert f2.construction_raw_squarings == 0

    # Missing candidate recovery cannot be replaced with a recurrence.
    for n in (4, 5):
        cert = fermat_depth_certificate(n)
        assert cert.status == "unknown"
        assert cert.method.startswith("terminal-threshold:")
        assert cert.specialization_raw_squarings == 0
        assert cert.carrier_states_enumerated == 0
        assert cert.construction_raw_squarings == 0
        assert not cert.scalable_construction


def test_classical_ceiling_uses_shared_native_square_action(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from devtools.proofs.oracles.classical_ceiling import (
        fermat_classical_ceiling,
        mersenne_classical_ceiling,
    )
    from number_compiler.arithmetic.polynomials.arithmetic_tile import SquareTileAction

    original = SquareTileAction.apply
    calls: list[tuple[str, int]] = []

    def tracked(self: SquareTileAction, value: int, modulus: int) -> int:
        calls.append((self.family, self.span))
        return original(self, value, modulus)

    monkeypatch.setattr(SquareTileAction, "apply", tracked)
    assert fermat_classical_ceiling(4).passes
    assert not mersenne_classical_ceiling(11).passes
    assert calls == [("fermat", 15), ("mersenne", 9)]


def test_composite_mersenne_exponents_are_rejected_before_number_level_selector() -> (
    None
):
    for p in (4, 9, 15):
        cert = mersenne_depth_certificate(p)
        assert cert.status == "composite"
        assert cert.method == "composite-exponent-factor"
        assert cert.scalable_construction
        assert cert.carrier_states_enumerated == 0


def test_sqrt_decision_thresholds_really_put_every_passing_divisor_above_sqrt_candidate() -> (
    None
):
    for n in range(2, 10):
        spec = fermat_terminal_threshold_spec(n)
        N = (1 << (1 << n)) + 1
        lower = 1 + (1 << spec.prime_decision_required_local_v2)
        assert lower * lower > N

    from number_compiler.sequences.power_numbers.terminal_threshold import (
        _mersenne_branch_lower_bound,
    )

    for p in (3, 5, 7, 11, 13, 17, 19, 31, 61, 127):
        spec = mersenne_terminal_threshold_spec(p)
        N = (1 << p) - 1
        lower = _mersenne_branch_lower_bound(p, spec.prime_decision_required_local_v2)
        assert lower * lower > N
        if spec.prime_decision_level > 0:
            previous = _mersenne_branch_lower_bound(
                p, spec.prime_decision_required_local_v2 - 1
            )
            assert previous * previous <= N


def test_mersenne_threshold_does_not_construct_full_candidate(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Regression guard: threshold search compares against 2**p symbolically.
    import number_compiler.sequences.power_numbers.terminal_threshold as threshold

    original = threshold._mersenne_branch_lower_bound
    calls = []

    def tracked(p: int, v: int) -> int:
        calls.append((p, v))
        return original(p, v)

    monkeypatch.setattr(threshold, "_mersenne_branch_lower_bound", tracked)
    spec = threshold.mersenne_terminal_threshold_spec(127)
    assert spec.prime_decision_required_local_v2 > 0
    assert calls
