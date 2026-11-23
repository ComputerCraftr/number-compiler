"""Checks for source-authenticated Fermat checkpoint batches."""

import sys
from dataclasses import replace

import pytest

from number_compiler.sequences.power_numbers import fermat_boundary_macros
from number_compiler.sequences.power_numbers._harmonic_authority import (
    HarmonicIssuer,
    harmonic_verified,
)
from number_compiler.sequences.power_numbers.fermat_boundary_macros import (
    FermatClockId,
    NamedFermatClock,
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
