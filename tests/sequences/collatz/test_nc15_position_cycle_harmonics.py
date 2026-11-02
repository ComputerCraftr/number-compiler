"""Exact, demanded harmonics for already-issued Collatz parity actions."""

from __future__ import annotations

from collections.abc import Mapping

import pytest

from number_compiler.arithmetic.contracts.input_validation import (
    is_object_tuple,
    string_keyed_mapping,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.collatz.border_return_grammar import (
    select_border_return_macro,
)
from number_compiler.sequences.collatz.boundary_macros import (
    admit_boundary_macro_plan,
    select_admitted_boundary_macro,
)
from number_compiler.sequences.collatz.boundary_templates import (
    BoundaryActionTemplateMemo,
)
from number_compiler.sequences.collatz.position_cycle_harmonics import (
    ZeroTailFree6305Orbit,
    issued_boundary_motif_orbit,
    minimize_fixed_word_odd_position,
)


def _object_map(value: object) -> Mapping[str, object]:
    mapping = string_keyed_mapping(value)
    if mapping is None:
        raise AssertionError("expected a string-keyed observation map")
    return mapping


def _object_tuple(value: object) -> tuple[object, ...]:
    if not is_object_tuple(value):
        raise AssertionError("expected an observation tuple")
    return value


def _zero_tail_source(repetitions: int) -> int:
    coefficient = 2 if repetitions % 2 == 0 else 3
    return (1 << (2 * repetitions + 1)) * coefficient - 1


def test_zero_tail_spectrum_matches_exact_modular_digits() -> None:
    for repetitions in (1, 2, 8, 32, 64):
        orbit = ZeroTailFree6305Orbit(_zero_tail_source(repetitions), repetitions)
        for radix, position in ((3, 0), (6, 1), (10, 2), (64, 1)):
            spectrum = orbit.spectrum(radix, position)
            direct = tuple(
                sum(
                    orbit.digit(tick, radix, position) == digit
                    for tick in range(repetitions)
                )
                for digit in range(radix)
            )
            assert spectrum.counts == direct
            assert sum(spectrum.counts) == repetitions
            assert spectrum.radial_scale.growths == 2 * repetitions
            assert spectrum.radial_scale.halvings == 2 * repetitions


def test_variable_tail_spectrum_matches_issued_upper_cursor() -> None:
    for source, ticks in ((13, 7), (23, 13), (43, 7), (73, 8)):
        macro = select_border_return_macro(source, ticks)
        if macro is None:
            continue
        spectrum = macro.demanded_position_harmonics(6, 1)
        current = source
        if macro.entry_port.value == 6:
            current //= 2
        elif macro.entry_port.value == 0:
            current >>= (current & -current).bit_length() - 1
        if current % 10 == 5:
            current = (3 * current + 1) // 2
        expected = [0] * 6
        for tail in macro.zero_tails:
            expected[(current // 6) % 6] += 1
            numerator = 3 * ((current - 3) // 10) + 1
            assert (numerator & -numerator).bit_length() - 1 == tail
            odd = numerator >> tail
            current = (15 * odd + 1) // 2
        assert spectrum.counts == tuple(expected)
        assert spectrum.radial_scale.halvings == sum(macro.zero_tails) + 2 * len(
            macro.zero_tails
        )


def test_named_motif_observer_is_source_issued_and_demanded() -> None:
    with BoundaryActionTemplateMemo(ResourceLedger()) as templates:
        plan = admit_boundary_macro_plan(33, 80, minimum_repetitions=1)
        assert plan is not None
        macro = select_admitted_boundary_macro(plan, templates=templates)
        spectrum = macro.demanded_motif_position_harmonics(3, 1)
        orbit = issued_boundary_motif_orbit(macro)
        expected = [0] * 3
        current = orbit.source
        for _ in range(orbit.repetitions):
            expected[(current // 3) % 3] += 1
            current = orbit.word.endpoint(current)
        assert spectrum.counts == tuple(expected)
        assert spectrum.radial_scale == orbit.radial_scale
        assert spectrum.repetitions == orbit.repetitions


def test_odd_position_moore_preserves_the_fixed_word_transition() -> None:
    macro = select_border_return_macro(23, 13)
    assert macro is not None
    quotient = minimize_fixed_word_odd_position(macro.fields, 3, 2)
    modulus = 3**3
    inverse = pow(2, -macro.fields.steps, modulus)
    assert quotient.states == modulus
    for residue in range(modulus):
        following = (
            (macro.fields.gain * residue + macro.fields.offset) * inverse
        ) % modulus
        state = quotient.class_ids[residue]
        target = quotient.class_ids[following]
        assert quotient.transitions[state] == (target,)
        assert quotient.outputs[state] == residue // (3**2)


def test_boundary_macro_position_ports_are_explicit_term_demands() -> None:
    term = PoweredCollatzTerm(23, 13, shared_cache=False)
    term.prepare_innovation_tape()
    packet = term.observe_boundary_macro(
        position_spectrum_requests=((6, 0),),
        odd_position_moore_requests=((3, 1),),
        position_moore_walsh64=True,
    )
    detail = _object_map(packet["position_cycle_harmonics"])
    assert detail["status"] == "complete"
    assert detail["starting_physical_tick"] == 0
    spectra = _object_tuple(detail["spectra"])
    assert len(spectra) == 1
    harmonic = _object_map(_object_map(spectra[0])["harmonic"])
    assert harmonic["radix"] == 6
    moore = _object_tuple(detail["odd_position_moore"])
    assert len(moore) == 1
    assert "future_digit_change_walsh64_mod5" in _object_map(moore[0])


def test_boundary_position_observer_is_absent_without_explicit_demand() -> None:
    term = PoweredCollatzTerm(23, 13, shared_cache=False)
    term.prepare_innovation_tape()
    packet = term.observe_boundary_macro()
    assert "position_cycle_harmonics" not in packet


def test_unrequested_invalid_or_nonadmitted_views_fail_before_materialization() -> None:
    macro = select_border_return_macro(23, 13)
    assert macro is not None
    with pytest.raises(ValueError, match="radix"):
        macro.demanded_position_harmonics(1, 0)
    with pytest.raises(ValueError, match="source cylinder"):
        ZeroTailFree6305Orbit(23, 8)
