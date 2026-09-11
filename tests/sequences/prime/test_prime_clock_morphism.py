from __future__ import annotations

from math import gcd
from typing import Never

import pytest

from number_compiler.sequences.prime.wheel_cyclotomic import (
    PrimeRecursiveWheelIndex,
    PrimeWheelCircularQuotient,
    PrimeWheelExtensionMorphism,
    PrimeWheelPhaseBlock,
    extend_prime_wheel_gaps,
)


def _direct_gaps(modulus: int) -> tuple[int, ...]:
    residues = [n for n in range(1, modulus + 1) if gcd(n, modulus) == 1]
    return tuple(
        residues[(i + 1) % len(residues)]
        + (modulus if i + 1 == len(residues) else 0)
        - residues[i]
        for i in range(len(residues))
    )


def test_prime_wheel_circular_phi_quotient_is_lossless_and_rotation_exact() -> None:
    hist = (37, 36, 38, 37, 37, 37, 36, 37, 37, 37, 38, 36, 37)
    q = PrimeWheelCircularQuotient.from_histogram(hist)
    assert q.histogram() == hist
    assert q.rotate(3).histogram() == tuple(
        hist[(i - 3) % len(hist)] for i in range(len(hist))
    )
    assert q.max_deviation <= 2


def test_prime_wheel_phase_block_composition_power_and_difference_radix_are_exact() -> (
    None
):
    gaps = (6, 4, 2, 4, 2, 4, 6, 2)
    q = 7
    alpha = 3
    direct = PrimeWheelPhaseBlock.from_gaps(gaps, prime=q, alpha=alpha)
    split = PrimeWheelPhaseBlock.from_gaps(gaps[:3], prime=q, alpha=alpha).then(
        PrimeWheelPhaseBlock.from_gaps(gaps[3:], prime=q, alpha=alpha)
    )
    assert split.canonical_key == direct.canonical_key
    differences = tuple(gaps[i + 1] - gaps[i] for i in range(len(gaps) - 1))
    by_difference = PrimeWheelPhaseBlock.from_endpoint_differences(
        gaps[0],
        differences,
        prime=q,
        alpha=alpha,
    )
    assert by_difference.canonical_key == direct.canonical_key
    half = PrimeWheelPhaseBlock.from_gaps(
        tuple(g // 2 for g in gaps), prime=q, alpha=2 * alpha
    )
    assert half.phase_shift == direct.phase_shift
    assert half.circular == direct.circular
    powered = direct.power_block(q)
    assert powered.phase_shift == 0
    assert powered.circular.histogram() == (len(gaps),) * q


def test_prime_wheel_extension_uses_gap_phase_morphism_not_old_residue_vector() -> None:
    modulus = 2
    gaps: tuple[int, ...] = (2,)
    for q in (3, 5, 7, 11, 13):
        morphism = PrimeWheelExtensionMorphism.from_gaps(
            gaps, old_modulus=modulus, new_prime=q
        )
        new, block, initial_copy = extend_prime_wheel_gaps(
            gaps, old_modulus=modulus, new_prime=q
        )
        assert new == _direct_gaps(modulus * q)
        assert block == morphism.phase
        assert initial_copy == morphism.initial_copy
        assert sum(morphism.deletion_counts()) == len(gaps)
        assert block.phase_shift == q - 1
        assert 0 <= initial_copy < q
        if len(gaps) > 1:
            assert new[0] == gaps[0] + gaps[1]
        modulus *= q
        gaps = new


def test_prime_wheel_extension_index_rank_select_avoids_q_times_n_bitmap() -> None:
    from number_compiler.sequences.prime.wheel_cyclotomic import (
        index_prime_wheel_extension,
    )

    modulus = 2 * 3 * 5 * 7
    gaps = _direct_gaps(modulus)
    q = 11
    index = index_prime_wheel_extension(gaps, old_modulus=modulus, new_prime=q)
    direct = _direct_gaps(modulus * q)
    assert index.length == len(direct)
    assert index.retained_positions == len(
        gaps
    )  # exactly one deletion slot per old vertex
    assert index.raw_length == q * len(gaps)
    assert tuple(index.gap_at(i) for i in range(index.length)) == direct
    residues = [1]
    for gap in direct[:-1]:
        residues.append(residues[-1] + gap)
    for rank in (0, 1, 7, len(residues) // 2, len(residues) - 1):
        assert index.residue_at(rank) == residues[rank]
        assert index.rank_before(residues[rank]) == rank


def test_prime_wheel_phase_count_does_not_lift_full_histogram(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    q = PrimeWheelCircularQuotient.from_histogram((3, 5, 4, 6, 2, 7, 1))
    block = PrimeWheelPhaseBlock(7, 3, q.total, 2, q)

    def forbidden(_self: object) -> Never:
        raise AssertionError("full histogram lift used for one coefficient")

    monkeypatch.setattr(PrimeWheelCircularQuotient, "histogram", forbidden)
    assert block.count_phase(4, entering_phase=2) == (3, 5, 4, 6, 2, 7, 1)[2]


def test_recursive_wheel_rank_select_never_needs_parent_gap_materialization() -> None:
    primes = (2, 3, 5, 7, 11)
    index = PrimeRecursiveWheelIndex.from_primes(primes)
    modulus = 1
    for p in primes:
        modulus *= p
    direct = [n for n in range(1, modulus) if gcd(n, modulus) == 1]
    assert index.modulus == modulus
    assert index.length == len(direct)
    assert tuple(index.residue_at(r) for r in range(index.length)) == tuple(direct)
    for x in range(0, modulus + 2, 17):
        assert index.rank_before(x) == sum(v < x for v in direct)
    direct_gaps = tuple(
        direct[(i + 1) % len(direct)]
        + (modulus if i + 1 == len(direct) else 0)
        - direct[i]
        for i in range(len(direct))
    )
    assert tuple(index.gap_at(r) for r in range(index.length)) == direct_gaps


def test_recursive_wheel_extension_is_descriptor_only() -> None:
    parent = PrimeRecursiveWheelIndex.from_primes((2, 3, 5, 7))
    child = parent.with_prime(11).with_prime(13)
    assert child.primes == (2, 3, 5, 7, 11, 13)
    assert child.description_bits < child.length.bit_length() * 8
    # A few distant selects prove later extensions do not require an old gap cycle.
    for rank in (0, 1, child.length // 3, child.length // 2, child.length - 1):
        residue = child.residue_at(rank)
        assert gcd(residue, child.modulus) == 1
        assert child.rank_before(residue) == rank
