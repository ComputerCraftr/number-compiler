"""Checks for source-authenticated Fermat checkpoint batches."""

import sys
from dataclasses import replace
from typing import Never

import pytest

from number_compiler.sequences.power_numbers import fermat_boundary_macros
from number_compiler.sequences.power_numbers._harmonic_authority import (
    HarmonicIssuer,
    harmonic_verified,
)
from number_compiler.sequences.power_numbers.fermat_boundary_macros import (
    FermatBorderMacro,
    FermatClockId,
    NamedFermatClock,
)
from number_compiler.sequences.power_numbers.fermat_powered_port_matrix import (
    FermatPoweredPortMatrix,
)
from number_compiler.sequences.power_numbers.numbers import FermatNumberSpec


def test_batch_matches_independent_ports_and_authenticates_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    matrix = FermatNumberSpec(3).demand_fermat_powered_port_matrix(7, 8)
    macro = matrix.macro
    offsets = (0, 1, 2, 4, 8)
    expected = tuple((macro.puncture(t), macro.radial_at(t)) for t in offsets)
    calls = 0

    def checked(
        record: object, payload: tuple[object, ...], *, issuer: HarmonicIssuer
    ) -> bool:
        nonlocal calls
        if record is macro:
            calls += 1
        return harmonic_verified(record, payload, issuer=issuer)

    monkeypatch.setattr(fermat_boundary_macros, "harmonic_verified", checked)
    assert macro.certified_checkpoint_ports(offsets) == expected
    assert calls == 1


def test_batch_rejects_foreign_sources_and_bad_clocks() -> None:
    matrix = FermatNumberSpec(2).demand_fermat_powered_port_matrix(3, 4)
    macro = matrix.macro
    with pytest.raises(ValueError, match="unissued"):
        replace(macro).certified_checkpoint_ports((0,))
    for offsets in ((), (1, 0), (0, 0), (False,), (4097,)):
        with pytest.raises(ValueError, match="checkpoints"):
            macro.certified_checkpoint_ports(offsets)


def test_batch_still_checks_each_crt_port(monkeypatch: pytest.MonkeyPatch) -> None:
    matrix = FermatNumberSpec(2).demand_fermat_powered_port_matrix(3, 4)
    original = NamedFermatClock.at

    def corrupted(clock: NamedFermatClock, offset: int) -> int:
        value = original(clock, offset)
        if clock.identity is FermatClockId.MOD_99 and offset == 2:
            return (value + 1) % clock.modulus
        return value

    monkeypatch.setattr(NamedFermatClock, "at", corrupted)
    with pytest.raises(ArithmeticError, match="clock / modular port join"):
        matrix.macro.certified_checkpoint_ports((0, 1, 2, 4))


def test_radial_checkpoint_renders_only_the_guaranteed_prefix() -> None:
    macro = FermatNumberSpec(5).demand_fermat_powered_port_matrix(31, 32).macro
    prefix = macro.root_radial_prefix
    assert prefix is not None
    offset = 4096
    scale = 3**offset
    lower, upper = str(prefix * scale), str((prefix + 1) * scale)
    places = macro.root_radial_places
    expected = next(
        (lower[:size] for size in range(places, 0, -1) if lower[:size] == upper[:size]),
        None,
    )
    old_limit = sys.get_int_max_str_digits()
    try:
        sys.set_int_max_str_digits(sys.int_info.str_digits_check_threshold)
        port = macro.radial_at(offset)
    finally:
        sys.set_int_max_str_digits(old_limit)
    assert port.guaranteed_word == expected
    assert port.guaranteed_places == len(expected or "")
    assert port.exact_width is not None


def test_repeated_span_issues_one_batch_at_its_exact_source(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    spec = FermatNumberSpec(5)
    start = spec.demand_fermat_powered_port_matrix(31, 3, position=12).rebase(7)
    direct = spec.demand_fermat_powered_port_matrix(31, 15, position=12).rebase(7)
    original = FermatBorderMacro.certified_checkpoint_ports
    batches: list[tuple[int, ...]] = []

    def tracked(
        macro: FermatBorderMacro, offsets: tuple[int, ...]
    ) -> tuple[
        tuple[
            tuple[tuple[FermatClockId, int], ...],
            fermat_boundary_macros.FermatRadialPort,
        ],
        ...,
    ]:
        assert macro is start.macro
        batches.append(offsets)
        return original(macro, offsets)

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("source-bound power constructed intermediate actions")

    monkeypatch.setattr(FermatBorderMacro, "certified_checkpoint_ports", tracked)
    monkeypatch.setattr(FermatPoweredPortMatrix, "then", forbidden)
    monkeypatch.setattr(FermatPoweredPortMatrix, "rebase", forbidden)
    powered = start.power(5)
    assert powered.producer_verified
    assert powered.macro is start.macro
    assert powered.issuer_payload() == direct.issuer_payload()
    assert batches == [(7, 8, 9, 11, 15, 22)]
    assert start.power_of_two(0) is start
    with pytest.raises(ValueError, match="requires an issued"):
        replace(start).power(1)
    with pytest.raises(ValueError, match="positive repeat count"):
        start.power(True)
    with pytest.raises(ValueError, match="production bound"):
        start.power(1 << 200)
    assert len(batches) == 1


@pytest.mark.parametrize(
    ("index", "radix", "position", "ticks"),
    ((4, 10, 6, 512), (5, 2, 16, 4096), (5, 5, 8, 4096), (5, 7, 3, 256)),
)
def test_matrix_affine_response_matches_every_literal_high_digit(
    index: int, radix: int, position: int, ticks: int
) -> None:
    level = (1 << index) - 1
    lower = radix**position
    modulus = lower * radix
    start = int.__pow__(3, 1 << level, modulus)
    gain = int.__pow__(3, ticks, modulus)
    matrix = FermatNumberSpec(index).demand_fermat_powered_port_matrix(
        level, ticks, base=radix, position=position
    )
    expected = tuple(
        (gain * (start % lower + lower * digit)) % modulus for digit in range(radix)
    )
    assert matrix.producer_verified
    assert matrix.source_residue == start
    assert matrix.conditional_endpoints == expected
    assert matrix.endpoint_residue == expected[start // lower]
