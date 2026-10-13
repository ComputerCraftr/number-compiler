"""Public nonbinary points share the same no-lowering execution boundary."""

from __future__ import annotations

from typing import Never

import pytest

from devtools.verification.lazy_collatz import LazyCollatzApplication
from number_compiler.api.number_api import NumberCompiler, PoweredCollatzTermPayload
from number_compiler.api.query_types import CollatzTermQuery
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from tests.support.performance_assertions import performance_bound


@pytest.mark.parametrize("radix", (3, 6, 12))
@pytest.mark.parametrize("seed,steps", ((27, 32), (54, 7), ((1 << 253) + 127, 1)))
@pytest.mark.validation  # Cross-radix deep/large-source public boundary matrix.
def test_public_nonbinary_points_poison_every_lowering_layer(
    monkeypatch: pytest.MonkeyPatch, radix: int, seed: int, steps: int
) -> None:
    with performance_bound(
        35, f"nonbinary boundary for seed {seed}, steps {steps}, radix {radix}"
    ):
        _check_public_nonbinary_points(monkeypatch, radix, seed, steps)


def _check_public_nonbinary_points(
    monkeypatch: pytest.MonkeyPatch, radix: int, seed: int, steps: int
) -> None:
    expected = seed
    for _ in range(steps):
        expected = 3 * expected + 1 if expected & 1 else expected // 2
    number = NumberCompiler().project(CollatzTermQuery(steps, seed=seed, radix=radix))

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("nonbinary point attempted endpoint lowering")

    for cls in (PoweredCollatzTerm, PoweredCollatzTermPayload):
        for method in ("digits", "iter_digits", "materialize"):
            monkeypatch.setattr(cls, method, forbidden)
    monkeypatch.setattr(LazyCollatzApplication, "materialize_bits", forbidden)
    for position in (0, 1, 3):
        if expected < radix**position:
            with pytest.raises(IndexError):
                number.digit(position)
        else:
            assert number.digit(position) == expected // radix**position % radix
    assert number.digit(0) == expected % radix
