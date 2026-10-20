"""Proved changing-tail 6305 cylinders in the production border selector."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.fields.walsh import walsh64_mod5
from number_compiler.sequences.collatz.border_harmonic_ring import (
    PeriodicTail6305Ring,
    periodic_return_capacity,
)
from number_compiler.sequences.collatz.border_return_grammar import (
    select_border_return_macro,
    validate_border_return_macro,
)


def _source(motif: tuple[int, ...], repetitions: int) -> int:
    residue, modulus = PeriodicTail6305Ring.guard_residue(motif, repetitions)
    return residue + modulus * ((3 - residue) * pow(modulus, -1, 5) % 5)


def _scalar_returns(
    source: int, count: int
) -> tuple[int, tuple[int, ...], tuple[int, ...]]:
    current = source
    tails: list[int] = []
    sources: list[int] = []
    for _ in range(count):
        assert current % 10 == 3
        sources.append(current)
        numerator = 3 * ((current - 3) // 10) + 1
        j = (numerator & -numerator).bit_length() - 1
        tails.append(j)
        current = (15 * (numerator >> j) + 1) // 2
        assert current % 10 == 3
    sources.append(current)
    return current, tuple(tails), tuple(sources)


def _long_orbit(
    motif: tuple[int, ...], groups: int
) -> tuple[PeriodicTail6305Ring, int, tuple[int, ...]]:
    source = _source(motif, groups)
    ring = PeriodicTail6305Ring.from_source(source, motif)
    endpoint, _, sources = _scalar_returns(source, groups * len(motif))
    return ring, endpoint, sources


@pytest.mark.parametrize(
    "motif", ((0, 1), (1, 2), (2, 4), (1, 2, 1), (0, 1, 2), (1, 0, 3))
)
@pytest.mark.parametrize("groups", (3, 4, 8, 12))
def test_cross_tail_ring_power_and_production_guards(
    motif: tuple[int, ...], groups: int
) -> None:
    source = _source(motif, groups)
    ring = PeriodicTail6305Ring.from_source(source, motif)
    assert ring.return_capacity is not None
    assert ring.return_capacity >= groups
    assert ring.scale(groups).growths == 2 * groups * len(motif)
    assert ring.scale(groups).halvings == groups * sum(j + 2 for j in motif)
    assert (
        ring.admitted_count(
            ticks=groups * sum(j + 4 for j in motif), returns=groups * len(motif)
        )
        == groups
    )
    endpoint, tails, _ = _scalar_returns(source, groups * len(motif))
    assert tails == motif * groups
    assert ring.endpoint(groups) == endpoint
    assert ring.word().power(groups).endpoint(source) == endpoint
    for radix in (2, 3, 5, 6, 10, 27, 64):
        for places in (1, 2, 3):
            assert ring.radix_residue(radix, places, groups) == endpoint % radix**places
    for bits in (0, 1, 7, 67):
        assert ring.binary_residue(bits, groups) == endpoint % (1 << bits)
    macro = select_border_return_macro(source, groups * sum(j + 4 for j in motif))
    assert macro is not None
    validate_border_return_macro(macro)
    assert macro.endpoint == endpoint
    assert macro.zero_tails == motif * groups
    assert (
        macro.fields.coefficient_snapshot()
        == ring.word().power(groups).coefficient_snapshot()
    )
    assert macro.physical_ticks == groups * sum(j + 4 for j in motif)
    obs = macro.observation()
    radial_scale = obs["return_radial_scale"]
    assert isinstance(radial_scale, dict)
    assert radial_scale["growths"] == ring.scale(groups).growths
    assert radial_scale["halvings"] == ring.scale(groups).halvings


def test_changing_tail_horizon_and_guard_do_not_predict_unproved_future() -> None:
    motif = (1, 2)
    source = _source(motif, 8)
    ring = PeriodicTail6305Ring.from_source(source, motif)
    assert ring.return_capacity is not None
    assert ring.admitted_count(ticks=7 * 3, returns=64) == 1
    assert not ring.admits(ring.return_capacity + 1)
    with pytest.raises(ValueError):
        ring.endpoint(ring.return_capacity + 1)
    # A phase-shifted source or an incorrect cycle must not borrow authority.
    with pytest.raises(ValueError):
        PeriodicTail6305Ring.from_source(source, (2, 1))
    with pytest.raises(ValueError):
        PeriodicTail6305Ring.guard_residue((1, 1), 3)
    with pytest.raises(ValueError):
        PeriodicTail6305Ring.guard_residue((1, 2), 1 << 13)
    # A partial physical horizon can never round up to a longer word.
    ticks = 8 * ring.physical_ticks - 1
    macro = select_border_return_macro(source, ticks)
    assert macro is not None
    assert macro.physical_ticks <= ticks
    validate_border_return_macro(macro)


@pytest.mark.parametrize("radix", (3, 6, 10, 64))
@pytest.mark.parametrize("motif", ((0, 1), (1, 2), (1, 2, 1)))
def test_all_phase_position_harmonics_against_scalar(
    radix: int, motif: tuple[int, ...]
) -> None:
    groups = 12
    source = _source(motif, groups)
    ring = PeriodicTail6305Ring.from_source(source, motif)
    _endpoint, tails, sources = _scalar_returns(source, groups * len(motif))
    macro = select_border_return_macro(source, groups * ring.physical_ticks)
    assert macro is not None and macro.zero_tails == tails
    for position in (0, 1, 2):
        spectrum = macro.demanded_position_harmonics(radix, position)
        assert sum(spectrum.counts) == groups * len(motif)
        expected = [0] * radix
        for value in sources[:-1]:
            expected[(value // radix**position) % radix] += 1
        assert spectrum.counts == tuple(expected)
        assert spectrum.radial_scale == ring.scale(groups)


@pytest.mark.parametrize("motif", ((0, 1), (1, 2), (0, 1, 2), (1, 2, 3, 0)))
def test_walsh64_cross_tail_first_sixtyfour_changes(motif: tuple[int, ...]) -> None:
    groups = (64 + len(motif) - 1) // len(motif)
    ring, _, sources = _long_orbit(motif, groups)
    spectrum = ring.demanded_position_harmonics(groups, 6, 1, walsh64=True)
    mask = sum(
        1 << tick
        for tick in range(64)
        if (sources[tick] // 6) % 6 != (sources[tick + 1] // 6) % 6
    )
    assert spectrum.walsh64_change_mod5 == walsh64_mod5(mask)
    macro = select_border_return_macro(ring.source, ring.physical_ticks * groups)
    assert macro is not None and macro.zero_tails == (motif * groups)[:64]
    observed = macro.demanded_position_harmonics(6, 1, walsh64=True)
    assert observed.walsh64_change_mod5 == spectrum.walsh64_change_mod5
    if 64 % len(motif) == 0:
        assert observed == spectrum


def test_one_motif_harmonics_do_not_assume_next_motif() -> None:
    motif = (1, 2, 1)
    source = _source(motif, 1)
    ring = PeriodicTail6305Ring.from_source(source, motif)
    result = ring.demanded_position_harmonics(1, 6, 2)
    _target, _tails, sources = _scalar_returns(source, len(motif))
    expected = [0] * 6
    for x in sources[:-1]:
        expected[(x // 36) % 6] += 1
    assert result.counts == tuple(expected)
    assert ring.demanded_position_harmonics(0, 6, 2).repetitions == 0


def test_forged_ring_state_and_expensive_motif_refused() -> None:
    motif = (1, 2)
    source = _source(motif, 8)
    good = PeriodicTail6305Ring.from_source(source, motif)
    assert good.return_capacity is not None
    with pytest.raises(ValueError, match="coefficients"):
        PeriodicTail6305Ring(
            source, motif, good.gain + 2, good.offset, good.steps, good.return_capacity
        )
    with pytest.raises(ValueError, match="capacity"):
        PeriodicTail6305Ring(
            source, motif, good.gain, good.offset, good.steps, good.return_capacity + 1
        )
    with pytest.raises(ValueError, match="coefficient budget"):
        PeriodicTail6305Ring.guard_residue((4096, 4096 - 1), 1)


def test_zero_defect_is_explicitly_unbounded_not_a_large_sentinel() -> None:
    assert periodic_return_capacity(0, 5) is None
    assert periodic_return_capacity(32, 5) == 0


@pytest.mark.parametrize("motif", ((0, 1), (1, 2), (1, 2, 1)))
def test_long_phase_orbit_minimizes_exact_modular_counts(
    motif: tuple[int, ...],
) -> None:
    groups = 128
    ring, endpoint, sources = _long_orbit(motif, groups)
    assert endpoint == ring.endpoint(groups)
    for radix in (3, 6, 10, 64):
        spectrum = ring.demanded_position_harmonics(groups, radix, 1, walsh64=True)
        counts = [0] * radix
        for value in sources[:-1]:
            counts[(value // radix) % radix] += 1
        assert spectrum.counts == tuple(counts)
        assert spectrum.evaluated_cells < groups * len(motif)
