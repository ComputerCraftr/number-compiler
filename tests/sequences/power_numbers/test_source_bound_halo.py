"""Source-guarded low-port demands for Fermat and Mersenne inner sources."""

from __future__ import annotations

import random

import pytest

from number_compiler.arithmetic.polynomials.primary_jet import PrimaryJetAffineMorphism
from number_compiler.sequences.power_numbers.numbers import (
    FermatNumberSpec,
    MersenneNumberSpec,
)
from number_compiler.sequences.power_numbers.source_halo import (
    StableUnwrappedHaloBlock,
    compose_last_four_source_tangents,
    demand_unwrapped_inner_halo_port,
)
from number_compiler.sequences.power_numbers.source_matrix import (
    MAX_SPARSE_DIGIT_POSITIONS,
    SmallModulusWork,
    UnwrappedInnerDigitStencil,
    demand_unwrapped_inner_digit_stencil,
    demand_unwrapped_inner_radix_port,
    source_no_wrap_guard,
)
from tests.support.power_number_source_oracle import (
    literal_power_number_radix_port,
    literal_power_number_sparse_digits,
)


@pytest.mark.parametrize(
    "family,parameter",
    (("fermat", 12), ("mersenne", 4096)),
)
def test_radix_ports_match_literal_source_algebra(family: str, parameter: int) -> None:
    for level in range(9):
        assert source_no_wrap_guard(family, parameter, level)
        reference = literal_power_number_radix_port(family, level, 10)
        port = demand_unwrapped_inner_radix_port(family, parameter, level, 10)
        assert (port.source_prefix, port.target_prefix) == (
            reference.source_prefix,
            reference.target_prefix,
        )
        assert (port.carry, port.borrow, port.xor) == (
            reference.carry,
            reference.borrow,
            reference.xor,
        )
        assert tuple(
            port.digit_at(i) for i in range(6)
        ) == literal_power_number_sparse_digits(family, level, 10, tuple(range(6)))


def test_sparse_nonadjacent_digits_and_typed_source_spec_adapters() -> None:
    for family, parameter, spec in (
        ("fermat", 20, FermatNumberSpec(20)),
        ("mersenne", 1 << 20, MersenneNumberSpec(1 << 20)),
    ):
        level, base, positions = 14, 3, (0, 2, 7, 11)
        expected = literal_power_number_sparse_digits(family, level, base, positions)
        stencil = spec.demand_unwrapped_inner_digit_stencil(level, base, positions)
        assert stencil.digits == expected
        assert stencil.coordinate_values == tuple(zip(positions, expected, strict=True))

        port = spec.demand_unwrapped_inner_radix_port(level, 7)
        assert (
            port.target_prefix
            == (port.source_prefix**2 - (2 if family == "mersenne" else 0)) % 7**6
        )

    empty = demand_unwrapped_inner_digit_stencil("fermat", 20, 14, 2, ())
    assert empty.digits == ()
    assert empty.work.factor_trial_candidates == 0
    with pytest.raises(ValueError, match="duplicate"):
        demand_unwrapped_inner_digit_stencil("fermat", 20, 14, 2, (1, 1))
    with pytest.raises(ValueError, match="budget"):
        demand_unwrapped_inner_digit_stencil("fermat", 20, 14, 2, (100,))


def test_sparse_digit_request_count_is_capped_before_stencil_work() -> None:
    positions = (0,) * (MAX_SPARSE_DIGIT_POSITIONS + 1)
    with pytest.raises(ValueError, match="sparse-digit-request-budget-exceeded"):
        demand_unwrapped_inner_digit_stencil("fermat", 20, 14, 2, positions)

    # The public frozen value object enforces the same cap when directly
    # constructed, before it scans coordinates or derives the radix modulus.
    with pytest.raises(ValueError, match="sparse-digit-request-budget-exceeded"):
        UnwrappedInnerDigitStencil(
            "fermat",
            20,
            14,
            2,
            positions,
            (0,) * len(positions),
            SmallModulusWork(2, 0, 0, 0),
        )


def test_guarded_refusals_and_stationary_powering() -> None:
    with pytest.raises(ValueError, match="wrap"):
        FermatNumberSpec(4).demand_unwrapped_inner_radix_port(4, 7)
    with pytest.raises(ValueError, match="wrap"):
        MersenneNumberSpec(13).demand_unwrapped_inner_radix_port(4, 7)
    with pytest.raises(ValueError, match="budget"):
        FermatNumberSpec(10**9).demand_unwrapped_inner_radix_port(4, 100)
    with pytest.raises(ValueError, match="stable"):
        StableUnwrappedHaloBlock("fermat", 4096, 3, 8)

    mersenne_short = MersenneNumberSpec(1 << 10).power_stable_unwrapped_inner_halo(2, 1)
    mersenne_next = MersenneNumberSpec(1 << 10).power_stable_unwrapped_inner_halo(3, 2)
    assert mersenne_short.then(mersenne_next) == MersenneNumberSpec(
        1 << 10
    ).power_stable_unwrapped_inner_halo(2, 3)
    assert (
        mersenne_short.single_output.semantic_observation
        == mersenne_next.single_output.semantic_observation
    )
    with pytest.raises(ValueError, match="stable"):
        FermatNumberSpec(4096).power_stable_unwrapped_inner_halo(3, 1)

    block = FermatNumberSpec(10**9).power_stable_unwrapped_inner_halo(4, 100_000_000)
    assert block.span == 100_000_000
    assert len(block.observation_runs) == 1
    assert block.observation_runs[0][1] == block.span
    assert block.single_output.digit_at(0) == 1
    assert block.last_four_halo == ((0, 0, 0, 0, 0),) * 4
    assert block.power_duration(block.span) == block

    mersenne = MersenneNumberSpec(1 << 2048).power_stable_unwrapped_inner_halo(2, 1024)
    assert mersenne.single_output.carry == (-1, -1, 0, 0, 0)
    assert mersenne.last_four_halo == ((-1, -1, 0, 0, 0),) * 4
    with pytest.raises(ValueError, match="wrap"):
        mersenne.square()


def test_last_four_mod16_consumer_is_separate_from_halo_forcing() -> None:
    randomizer = random.Random(0xB0AB)
    for _ in range(1_024):
        actions = tuple(
            PrimaryJetAffineMorphism.square_tangent(
                (randomizer.randrange(16), randomizer.randrange(16)),
                (randomizer.randrange(16), randomizer.randrange(16)),
                degree=2,
                modulus=16,
            )
            for _ in range(4)
        )
        full = PrimaryJetAffineMorphism.identity(degree=2, modulus=16)
        for action in actions:
            full = full.then(action)
        suffix = compose_last_four_source_tangents(actions)
        assert suffix == full
        assert suffix.source_annihilated
        assert suffix.apply((3, 15)) == full.apply((3, 15))

    halo = demand_unwrapped_inner_halo_port("fermat", 20, 4)
    first = PrimaryJetAffineMorphism.square_tangent(
        (1, 0), (0, 0), degree=2, modulus=16
    )
    second = PrimaryJetAffineMorphism.square_tangent(
        (1, 0), (1, 0), degree=2, modulus=16
    )
    left = compose_last_four_source_tangents((first,) * 4)
    right = compose_last_four_source_tangents((first, first, first, second))
    assert (
        halo.semantic_observation
        == demand_unwrapped_inner_halo_port("fermat", 20, 5).semantic_observation
    )
    assert left.kernel == right.kernel == (0, 0)
    assert left.offset != right.offset
