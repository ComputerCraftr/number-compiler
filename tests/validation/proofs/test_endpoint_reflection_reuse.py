"""Explicit symmetric endpoints reuse already emitted final coordinates."""

import pytest

from devtools.verification.block_power import apply_block_power, power_block_effect
from tests.support.reverse_pair_oracle import reference_successor


@pytest.mark.parametrize("source", ((7, 18, 7), (1, 2, 2, 1), (4, 4), (18,)))
def test_reverse_pair_endpoint_uses_certified_reflection(
    source: tuple[int, int, int, int]
    | tuple[int, int, int]
    | tuple[int, int]
    | tuple[int],
) -> None:
    expected: tuple[int, ...] = source
    for _ in range(8):
        expected = reference_successor(expected, 10)
    result = apply_block_power(power_block_effect(base=10, exponent=8), source)
    assert result.values == expected
    assert result.runtime_stats["endpoint_mirror_reuses"] == len(expected) // 2
    assert result.runtime_stats["explicitly_lowered_digits"] == len(expected)
    assert result.intermediate_pair_words == result.elementary_generations == 0


def test_nonsymmetric_word_does_not_enable_endpoint_reflection() -> None:
    result = apply_block_power(power_block_effect(base=10, exponent=2), (7, 12, 4))
    assert result.values == (10, 9, 18)
    assert result.runtime_stats.get("endpoint_mirror_reuses", 0) == 0


def test_explicit_endpoint_preserves_semantic_reuse_between_coordinates(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.hashlife.execution.continuations.higher_values import (
        RuntimeValueArena,
    )

    def forbidden_clear(_self: object) -> None:
        pytest.fail("a coordinate discarded the index's canonical boundary reuse")

    monkeypatch.setattr(RuntimeValueArena, "clear", forbidden_clear)
    expected: tuple[int, ...] = (7, 18, 7)
    for _ in range(64):
        expected = reference_successor(expected, 10)
    result = apply_block_power(
        power_block_effect(
            base=10,
            exponent=64,
            max_context_nodes=2_000_000,
            max_cache_entries=2_000_000,
        ),
        (7, 18, 7),
    )
    assert result.values == expected
    assert result.runtime_stats["higher_concrete_apply_evaluations"] < 10_000
    assert result.runtime_stats["explicitly_lowered_digits"] == len(expected)
    assert result.intermediate_pair_words == result.elementary_generations == 0
