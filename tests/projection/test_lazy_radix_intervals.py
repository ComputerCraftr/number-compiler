"""Radix views may share only the one bounded exact microblock facility."""

from typing import Never

import pytest

from number_compiler.projection.lazy_radix import collatz_radix_digit
from number_compiler.projection.microblock_cache import MicroblockKey
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from tests.support.reference_arithmetic import collatz_literal as _collatz


def test_single_radix_query_has_no_range_or_prefix_replay_store() -> None:
    seed = (1 << 95) + 0x123456789ABCDEF12345
    term = PoweredCollatzTerm(seed, 11)
    expected = _collatz(seed, 11)
    assert collatz_radix_digit(term, 3, 1) == (expected // 3) % 3
    projection = term._radix_projections[3]
    assert not any(
        hasattr(projection, name)
        for name in ("_ranges", "_transfers", "_point", "_range", "_evaluate")
    )
    assert term._microblocks.payload_bytes <= term._microblocks.MAX_PAYLOAD_BYTES
    assert all(type(key) is MicroblockKey for key in term._microblocks.blocks)


@pytest.mark.validation  # Wide source through four public radix applications.
def test_collective_radices_share_one_accounted_exact_cache() -> None:
    seed = (1 << 95) + 0x123456789ABCDEF12345
    term = PoweredCollatzTerm(seed, 11)
    expected = _collatz(seed, 11)
    for radix in (3, 5, 6, 12):
        assert collatz_radix_digit(term, radix, 1) == (expected // radix) % radix
    projections = tuple(term._radix_projections.values())
    assert projections
    assert all(
        projection._microblocks is term._microblocks for projection in projections
    )
    cache = term._microblocks
    assert len(cache) <= cache.MAX_ENTRIES
    assert cache.payload_bytes <= cache.MAX_PAYLOAD_BYTES
    assert {key.radix for key in cache.blocks} <= {2, 3, 5, 6, 12}
    assert term._ledger.counters.get("radix_microblock_source_bits", 0) == 0
    assert term._ledger.counters.get("radix_microblock_source_fills", 0) == 0
    assert not {key for key in cache.blocks if key.kind == "binary"}
    assert term.metrics().resource_audit_complete == 1


def test_scalar_radix_observation_does_not_compute_the_complete_width(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = PoweredCollatzTerm(27, 3)
    expected = _collatz(27, 3)

    def forbidden(_self: PoweredCollatzTerm) -> Never:
        raise AssertionError("scalar radix observation computed the complete width")

    monkeypatch.setattr(PoweredCollatzTerm, "width", forbidden)
    assert collatz_radix_digit(term, 3, 0) == expected % 3
    exterior = 0
    remaining = expected
    while remaining:
        remaining //= 3
        exterior += 1
    with pytest.raises(IndexError):
        collatz_radix_digit(term, 3, exterior)


def test_huge_exterior_coordinate_never_constructs_the_radix_power() -> None:
    term = PoweredCollatzTerm(27, 3)
    # The low-level modular projection has historically zero-padded exterior
    # coordinates; the admitted public point wrapper turns that into IndexError.
    assert term.radix_digit(3, 10**100) == 0
    assert term._ledger.counters["collatz_radix_exterior_shortcuts"] == 1


def test_scalar_points_never_construct_the_complete_affine_numerator(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = PoweredCollatzTerm(27, 3)

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("scalar point constructed the complete numerator")

    monkeypatch.setattr(PoweredCollatzTerm, "_source_numerator", forbidden)
    assert term.digit(0) == 0
    assert collatz_radix_digit(term, 3, 0) == 1
    assert collatz_radix_digit(term, 3, 4) == 1
    with pytest.raises(IndexError):
        collatz_radix_digit(term, 3, 5)


def test_nonbinary_full_stream_lowers_once_on_first_demand(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.api.number_api import PoweredCollatzTermPayload

    term = PoweredCollatzTerm(27, 3)
    payload = PoweredCollatzTermPayload(term, 3)
    original = PoweredCollatzTerm.materialize
    calls = 0

    def counted(self: PoweredCollatzTerm, *, max_bits: int) -> int:
        nonlocal calls
        calls += 1
        return original(self, max_bits=max_bits)

    monkeypatch.setattr(PoweredCollatzTerm, "materialize", counted)
    stream = payload.iter_digits()
    assert calls == 0
    assert tuple(stream) == (1, 2, 1, 1, 1)
    assert calls == 1


@pytest.mark.parametrize("steps", (0, 1, 2, 11))
@pytest.mark.validation  # Complete multi-step, multi-radix output matrix.
def test_radix_points_remain_exact_with_all_explicit_lowering_poisoned(
    steps: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    seed = 27
    term = PoweredCollatzTerm(seed, steps)
    expected = _collatz(seed, steps)

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("radix point called explicit endpoint lowering")

    monkeypatch.setattr(PoweredCollatzTerm, "materialize", forbidden)
    monkeypatch.setattr(PoweredCollatzTerm, "digits", forbidden)
    monkeypatch.setattr(PoweredCollatzTerm, "iter_digits", forbidden)
    for radix in (3, 6, 12):
        index = 0
        while expected // radix**index:
            assert (
                collatz_radix_digit(term, radix, index)
                == (expected // radix**index) % radix
            )
            index += 1
        with pytest.raises(IndexError):
            collatz_radix_digit(term, radix, index)
        projection = term._radix_projections[radix]
        assert not any(
            hasattr(projection, name) for name in ("_programs", "_ranges", "_transfers")
        )
