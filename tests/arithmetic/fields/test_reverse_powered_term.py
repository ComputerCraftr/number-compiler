from __future__ import annotations

import random
from typing import Never

import pytest

from number_compiler.api.number_api import NumberCompiler
from number_compiler.arithmetic.fields.radix import digits_lsd, value_from_lsd_digits
from number_compiler.sequences.reverse_add.extent import ReverseAddExtent
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from tests.support.power_assertions import assert_binary_power_bound


def _reverse_add(value: int, base: int) -> int:
    digits = digits_lsd(value, base)
    return value + value_from_lsd_digits(reversed(digits), base)


@pytest.mark.validation  # Complete 25-generation materialization/point matrix.
def test_binary_powered_196_term_matches_scalar_orbit_and_random_digits() -> None:
    value = 196
    for generation in range(25):
        if generation:
            value = _reverse_add(value, 10)
        term = ReverseAddPoweredTerm(196, generation, base=10)
        assert term.materialize(max_bits=10_000) == value
        digits = digits_lsd(value, 10)
        assert term.width() == len(digits)
        for position in {0, len(digits) // 2, len(digits) - 1}:
            assert term.digit(position) == digits[position]


@pytest.mark.validation  # All 308 seeded multibase generation endpoints.
def test_binary_powered_term_is_exact_across_small_radices_and_seeds() -> None:
    rng = random.Random(0x196B1A)
    for base in range(2, 13):
        for _ in range(4):
            seed = rng.randrange(1, base**4)
            value = seed
            for generation in range(7):
                if generation:
                    value = _reverse_add(value, base)
                term = ReverseAddPoweredTerm(seed, generation, base=base)
                assert term.materialize(max_bits=10_000) == value


def test_huge_nth_term_construction_is_logarithmic_and_does_not_project() -> None:
    generation = 10**18
    term = ReverseAddPoweredTerm(196, generation, base=10)
    metrics = term.metrics()
    assert metrics.point_queries == 0
    assert metrics.run_action_cache_entries == 0
    assert_binary_power_bound(metrics, generation)
    assert metrics.descriptor_bits <= 2 * generation.bit_length()


def test_number_api_keeps_reverse_add_width_exact_and_lazy() -> None:
    term = NumberCompiler().project_nth("196", 10**12)
    assert isinstance(term.metrics.width, ReverseAddExtent)
    assert term.metrics.projection_work == 0
    assert term.metrics.construction_steps < 2 * (10**12).bit_length()
    from number_compiler.api.number_api import PoweredReverseAddTermPayload

    assert isinstance(term.payload, PoweredReverseAddTermPayload)
    payload_metrics = term.payload.power_metrics()
    assert payload_metrics.point_queries == 0


def test_direct_digit_projection_has_no_ordinary_temporal_successor_loop(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.sequences.reverse_add.digits as reverse_digits

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("ordinary successor entered powered digit projection")

    monkeypatch.setattr(reverse_digits, "successor", forbidden)
    compiler = NumberCompiler()
    # 196[16] = 897100798, LSD first => position 4 is 0.
    assert compiler.project_digit("196", 16, 4) == 0
