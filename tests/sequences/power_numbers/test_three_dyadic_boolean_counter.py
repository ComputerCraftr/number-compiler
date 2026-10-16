"""Source-first base-2 carry counter / Fermat fold regressions for NC15."""

from __future__ import annotations

from collections.abc import Callable
from copy import copy
from dataclasses import replace
from random import Random
from typing import Protocol, Self

import pytest

from number_compiler.arithmetic.fields.walsh import WalshH5
from number_compiler.sequences.power_numbers.numbers import FermatNumberSpec
from number_compiler.sequences.power_numbers.signed_counter_classes import (
    SignedCounterClassAction,
)
from number_compiler.sequences.power_numbers.three_dyadic_boolean_counter import (
    MAX_COUNTER_PRECISION,
    BinaryCounterFoldAction,
    BoundedCompleteUnitCertificate,
    BoundedFermatCounterCertificate,
    demand_bounded_complete_unit_certificate,
    demand_bounded_fermat_counter_certificate,
    demand_dyadic_boolean_counter,
    two_adic_unit_binomial,
)


class _ComposableCounterAction(Protocol):
    def then(self, higher: Self, /) -> Self: ...


def _build_fold_action(
    source: int, addend: int, length: int, fermat_width: int
) -> _ComposableCounterAction:
    return BinaryCounterFoldAction.from_words(source, addend, length, fermat_width)


def _build_signed_class_action(
    source: int, addend: int, length: int, fermat_width: int
) -> _ComposableCounterAction:
    return SignedCounterClassAction.from_words(source, addend, length, fermat_width)


def test_direct_unit_binomial_matches_exact_dyadic_source() -> None:
    for t in range(1, 14):
        exponent = 1 << t
        for bits in (1, 2, 3, 4, 7, 11, 16, 31, 64, 97):
            source_modulus = 1 << (bits + t + 2)
            numerator_modulus = pow(3, exponent, source_modulus)
            expected = (numerator_modulus - 1) >> (t + 2)
            assert two_adic_unit_binomial(t, bits) == expected
    assert two_adic_unit_binomial(10**12, 128) == two_adic_unit_binomial(
        10**12 + 1, 128
    )
    assert two_adic_unit_binomial(10**12, 128) & 1 == 1


def test_counter_provenance_cannot_be_transferred_to_a_copied_record() -> None:
    window = demand_dyadic_boolean_counter(2, 12, fermat_width=16)
    forged = copy(window)
    assert not forged.producer_verified
    with pytest.raises(ValueError, match="changed"):
        forged.verify()
    certificate = demand_bounded_fermat_counter_certificate(3)
    assert certificate.producer_verified
    assert not copy(certificate).producer_verified
    with pytest.raises(ValueError, match="seal"):
        _ = copy(certificate).verdict


def test_counter_provenance_rejects_equal_but_different_fold_and_boolean_alias() -> (
    None
):
    window = demand_dyadic_boolean_counter(2, 12, fermat_width=16)
    object.__setattr__(window, "fold_action", replace(window.fold_action))
    assert not window.producer_verified
    other = demand_dyadic_boolean_counter(2, 12, fermat_width=16)
    object.__setattr__(other, "carry_in", bool(other.carry_in))
    assert not other.producer_verified


def test_full_pivot_counter_ports_match_independent_sources() -> None:
    for level in range(1, 12):
        x = 3 ** (1 << level)
        u = (x - 1) >> (level + 2)
        u_next = ((x * x) - 1) >> (level + 3)
        for extra in (0, 1, 2, 7, 15):
            for width in (1, 2, 12, 32):
                window = demand_dyadic_boolean_counter(
                    level, width, fermat_width=16, offset=extra
                )
                mask = (1 << width) - 1
                start = level + 1 + extra
                assert window.source_bits == (u >> start) & mask
                assert window.addend_bits == (u * u >> extra) & mask
                assert window.result_bits == (u_next >> start) & mask
                assert window.xor_mask == ((u ^ u_next) >> start) & mask
                source_delta = sum(
                    (1 - 2 * ((u >> i) & 1)) * (1 << (i % 32))
                    for i in range(start, start + width)
                    if ((u ^ u_next) >> i) & 1
                )
                assert window.signed_fermat_correction == source_delta % 65537
                assert window.fold_action.apply(window.carry_in)[
                    2
                ] == WalshH5.from_mask(window.xor_mask, width)


@pytest.mark.parametrize("factory", [_build_fold_action, _build_signed_class_action])
def test_counter_action_associativity_across_both_seams(
    factory: Callable[[int, int, int, int], _ComposableCounterAction],
) -> None:
    rng = Random(42716)
    for fermat_width in (1, 2, 3, 5, 16):
        for _ in range(150):
            segments = [
                (rng.getrandbits(length), rng.getrandbits(length), length)
                for length in (
                    rng.randrange(1, 31),
                    rng.randrange(1, 31),
                    rng.randrange(1, 31),
                )
            ]
            left, middle, right = (
                factory(source, addend, length, fermat_width)
                for source, addend, length in segments
            )
            assert left.then(middle).then(right) == left.then(middle.then(right))
            source_word = addend_word = offset = 0
            for source, addend, length in segments:
                source_word += source << offset
                addend_word += addend << offset
                offset += length
            assert left.then(middle).then(right) == factory(
                source_word, addend_word, offset, fermat_width
            )


def test_fold_action_matches_boolean_addition_and_repeated_runs() -> None:
    rng = Random(51877)
    for fermat_width in (2, 4, 7, 16):
        modulus = (1 << fermat_width) + 1
        for _ in range(150):
            length = rng.randrange(1, 35)
            source = rng.getrandbits(length)
            addend = rng.getrandbits(length)
            action = BinaryCounterFoldAction.from_words(
                source, addend, length, fermat_width
            )
            for incoming in (0, 1):
                actual = source + addend + incoming
                next_carry, delta, harmonic = action.apply(incoming)
                assert next_carry == actual >> length
                emitted = actual & ((1 << length) - 1)
                assert delta == (emitted - source) % modulus
                assert harmonic == WalshH5.from_mask(source ^ emitted, length)
        run = BinaryCounterFoldAction.digit(0, 0, fermat_width)
        trillion = run.repeat(10**12)
        assert trillion.length == 10**12
        assert trillion.apply(0)[0:2] == (0, 0)
        assert trillion.apply(1)[0:2] == (0, 1)
        assert trillion.moore_carry_classes == 2
        period = __import__("math").lcm(2 * fermat_width, 6)
        assert run.repeat(period).semantic_id == run.repeat(period * 17).semantic_id


def test_digit_validates_modulus_width_before_constructing_it() -> None:
    with pytest.raises(ValueError, match="Fermat fold width"):
        BinaryCounterFoldAction.digit(0, 0, 10**9)


def test_source_guard_and_scope_for_counter() -> None:
    window = FermatNumberSpec(4).demand_dyadic_boolean_counter(14, 32)
    assert window.xor_mask == 0x56DBB589
    assert window.absolute_walsh_h5.length_mod6 == 0
    with pytest.raises((ArithmeticError, ValueError)):
        replace(window, result_bits=window.result_bits ^ 1)
    with pytest.raises((ArithmeticError, ValueError)):
        replace(window, source_bits=window.source_bits ^ 1)
    with pytest.raises((ArithmeticError, ValueError)):
        replace(window, carry_in=window.carry_in ^ 1)
    assert (
        FermatNumberSpec(5).demand_dyadic_boolean_counter(30, 32).xor_mask == 0x8BA54D79
    )
    with pytest.raises(ValueError, match="Boolean-counter-precision-budget"):
        demand_dyadic_boolean_counter(MAX_COUNTER_PRECISION - 4, 8, fermat_width=16)
    with pytest.raises(ValueError, match="level-exceeds-Fermat-source"):
        FermatNumberSpec(4).demand_dyadic_boolean_counter(17, 8)


def test_joint_source_and_terminal_handoff_share_counter() -> None:
    spec = FermatNumberSpec(4)
    joined = spec.demand_joint_three_power_quotient(15, moving_width=12)
    joint_window = joined.demand_boolean_counter(32)
    direct_window = spec.demand_dyadic_boolean_counter(15, 32)
    assert joint_window == direct_window
    assert joint_window.signed_position_counts
    assert joined.terminal_status == "UNKNOWN"
    demands = spec.terminal_source_demand().observe_fermat_boolean_counters(32)
    assert tuple(x.level for x in demands) == (11, 12, 13, 14)
    assert tuple(x.xor_mask for x in demands) == (
        0xBB497389,
        0x333E1D99,
        0xD039D2BF,
        0x56DBB589,
    )
    assert not any(x.covers_complete_unit_transition for x in demands)


def test_joint_counter_uses_one_binomial_source_demand(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from tests.support.power_numbers import track_two_adic_source_demands

    packet = FermatNumberSpec(4).demand_joint_three_power_quotient(15, moving_width=0)
    calls = track_two_adic_source_demands(monkeypatch)
    packet.demand_boolean_counter(32)
    assert calls == [(15, 48)]


def test_bounded_complete_counter_certificates_and_refusals() -> None:
    for index in (1, 2, 3):
        certificate = FermatNumberSpec(
            index
        ).demand_bounded_boolean_counter_certificate()
        certificate.verify()
        assert certificate.complete_source_verified
        assert certificate.verdict == "PRIME"
        assert certificate.terminal_unit_residue == 1
        assert all(w.covers_complete_unit_transition for w in certificate.windows)
    # Finite proof budget: no premature promotion of F4/F5/F6.
    for index in (4, 5, 6):
        with pytest.raises(ValueError, match="Boolean-counter-complete-source-budget"):
            demand_bounded_fermat_counter_certificate(index)


def test_bounded_complete_unit_sources_and_f5_preflight(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    for index, level, precision, terms in (
        (1, 1, 1, 1),
        (2, 3, 8, 5),
        (3, 7, 194, 100),
    ):
        certificate = FermatNumberSpec(index).demand_bounded_complete_unit_certificate()
        assert type(certificate) is BoundedCompleteUnitCertificate
        certificate.verify()
        assert certificate.complete_source_verified
        assert certificate.index == index
        assert certificate.level == level
        assert certificate.precision == precision
        assert certificate.term_count == terms
        assert certificate.terminal_residue == 1
        assert certificate.verdict == "PRIME"

    from number_compiler.sequences.power_numbers import (
        three_dyadic_boolean_counter as counter,
    )

    def forbidden_source(*_args: object, **_kwargs: object) -> int:
        raise AssertionError("F5 must fail before the binomial source is evaluated")

    monkeypatch.setattr(counter, "_binomial_unit_source", forbidden_source)
    with pytest.raises(ValueError, match="complete-unit-source-bound-exceeds-budget"):
        demand_bounded_complete_unit_certificate(5)


def test_complete_unit_certificate_requires_its_bound_source_seal() -> None:
    certificate = demand_bounded_complete_unit_certificate(2)
    forged = replace(certificate, terminal_residue=0)
    assert not forged.producer_verified
    assert not forged.complete_source_verified
    with pytest.raises(ValueError, match="no source seal"):
        forged.verify()
    with pytest.raises(ValueError, match="no source seal"):
        _ = forged.verdict

    original_unit = certificate.unit
    object.__setattr__(certificate, "unit", original_unit + 1)
    assert not certificate.producer_verified
    with pytest.raises(ValueError, match="no source seal"):
        certificate.verify()


def test_forged_or_partial_counter_cannot_issue_a_prime_verdict() -> None:
    with pytest.raises(ValueError, match="cover all unit transitions"):
        BoundedFermatCounterCertificate(2, (), 1)

    partial_f4 = tuple(
        demand_dyadic_boolean_counter(level, 32, fermat_width=16)
        for level in range(1, 15)
    )
    assert not all(window.covers_complete_unit_transition for window in partial_f4)
    with pytest.raises(ValueError, match="complete counter action"):
        BoundedFermatCounterCertificate(4, partial_f4, 1)
