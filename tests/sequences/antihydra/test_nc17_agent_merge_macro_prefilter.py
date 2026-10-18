"""Proof-scoped speculative-work refusal for the integrated CLI branch."""

from __future__ import annotations

from random import Random
from unittest.mock import patch

import pytest

from number_compiler.sequences.antihydra.mahler_odd_prefilter import (
    PREFILTER_BITS,
    might_have_odd_macro_low_suffix,
    source_might_have_odd_macro,
)
from number_compiler.sequences.antihydra.mahler_odd_source_transfer import (
    select_source_certified_odd_macro,
)
from tests.support.mahler_harmonic_reference import source_for_motif


def test_2adic_filter_never_rejects_a_source_issued_macro() -> None:
    rng = Random(71017)
    sources = list(range(1, 1800))
    sources += [
        rng.getrandbits(64 + 37 * j) | 1 for j in range(1, 7) for _ in range(32)
    ]
    for source in sources:
        low = source & ((1 << PREFILTER_BITS) - 1)
        for extent in (65, 128, 256):
            maybe = might_have_odd_macro_low_suffix(
                low, remaining_steps=extent, max_residual_steps=64
            )
            if not maybe:
                assert (
                    select_source_certified_odd_macro(
                        source,
                        remaining_steps=extent,
                        max_extent=extent,
                        max_residual_steps=64,
                    )
                    is None
                )


@pytest.mark.parametrize("motif", ((1, 2), (1, 1, 2), (2, 3)))
def test_known_repetitions_survive_prefilter(motif: tuple[int, ...]) -> None:
    source = source_for_motif(motif, 48)
    assert source_might_have_odd_macro(source)
    assert might_have_odd_macro_low_suffix(
        source & ((1 << PREFILTER_BITS) - 1),
        remaining_steps=128,
        max_residual_steps=64,
    )


def test_negative_fiber_shared_across_unbounded_high_bits() -> None:
    assert not source_might_have_odd_macro(1)
    for index in range(1, 24):
        source = 1 + (index << 80)
        assert source & 1
        assert not source_might_have_odd_macro(source)


def test_unknown_high_valuation_must_not_be_a_rejection() -> None:
    # 3D+1 is divisible by 2**64 for this odd residue. The next event may
    # depend on a higher source bit; it cannot be rejected from this suffix.
    residue = -pow(3, -1, 1 << 64) % (1 << 64)
    assert residue & 1
    assert source_might_have_odd_macro(residue)


def test_invalid_prefilter_requests_fail_closed() -> None:
    with pytest.raises(ValueError):
        might_have_odd_macro_low_suffix(0, bits=0)
    with pytest.raises(ValueError):
        might_have_odd_macro_low_suffix(0, max_events=32)
    with pytest.raises(ValueError):
        might_have_odd_macro_low_suffix(0, remaining_steps=-1)


def test_real_antihydra_128_does_not_call_expensive_selector() -> None:
    from devtools.benchmarks.public_query_comparison import cli_sample
    from number_compiler.api.number_api import NumberCompiler

    # Seed-8 return 128 has no admitted macro with <=64 residual steps.
    # Poison the *entire* large-integer motif issuer to prove the new
    # prefilter rejects before it runs, while preserving the public CLI.
    NumberCompiler.clear_shared_cache()
    with patch(
        "number_compiler.sequences.antihydra.arithmetic_images.select_source_certified_odd_macro",
        side_effect=AssertionError("cold speculative odd selector must not run"),
    ):
        _, result = cli_sample(
            ["antihydra", "--nth", "128", "--info", "metrics", "--format", "json"],
            fresh=False,
        )
    assert result["value"] is not None
    NumberCompiler.clear_shared_cache()
