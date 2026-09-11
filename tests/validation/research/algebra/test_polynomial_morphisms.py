from __future__ import annotations

from typing import Never

import pytest

from devtools.experiments.algebra.polynomial_morphisms import (
    NewtonPrecisionMorphism,
    ProgressionProductArena,
    ProgressionProductMorphism,
)
from devtools.experiments.algebra.residue_refined_bend import fast_multipoint_bend_audit


def _mul_mod(
    left: tuple[int, ...] | tuple[int], right: tuple[int, ...], modulus: int
) -> tuple[int, ...]:
    out = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            out[i + j] = (out[i + j] + a * b) % modulus
    return tuple(out)


def test_progression_product_is_an_exact_translated_product_morphism() -> None:
    modulus = 1009
    block = ProgressionProductMorphism(modulus, 0, -1, 4)
    doubled = block.doubled()
    assert doubled == ProgressionProductMorphism(modulus, 0, -1, 8)
    left, right = doubled.split()
    assert left.then(right) == doubled
    assert right.root_start == left.end_root
    assert doubled.description_bits < 64

    arena = ProgressionProductArena()
    poly = arena.materialize(
        doubled,
        multiply=lambda a, b: _mul_mod(a, b, modulus),
    )
    expected: tuple[int, ...] = (1,)
    for j in range(8):
        expected = _mul_mod(expected, (j, 1), modulus)
    assert poly == expected


def test_progression_materialization_is_interned_not_rebuilt() -> None:
    modulus = 221
    block = ProgressionProductMorphism(modulus, 7, 13, 32)
    arena = ProgressionProductArena()
    first = arena.materialize(block, multiply=lambda a, b: _mul_mod(a, b, modulus))
    misses = arena.misses
    second = arena.materialize(block, multiply=lambda a, b: _mul_mod(a, b, modulus))
    assert first is second
    assert arena.hits >= 1
    assert arena.misses == misses
    assert arena.size > 1  # semantic split blocks were interned too


def test_newton_precision_schedule_is_explicit_doubling_morphism() -> None:
    stage = NewtonPrecisionMorphism(1)
    widths = []
    while stage.precision < 37:
        stage = stage.doubled(limit=37)
        widths.append(stage.precision)
    assert widths == [2, 4, 8, 16, 32, 37]
    assert stage.description_bits == 6


def test_special_bsgs_uses_progression_morphisms_without_root_lists() -> None:
    audit = fast_multipoint_bend_audit("fermat", 5, start=1, span=511)
    assert audit.exact and audit.bend_support_gcd == 641
    assert audit.baby_morphism_description_bits > 0
    assert audit.giant_morphism_description_bits > 0
    assert audit.morphism_cache_hits > 0
    assert audit.morphism_cache_misses > 0
    assert audit.morphism_cached_coefficient_slots > 0
    assert not audit.progression_root_lists_materialized
    assert audit.newton_precision_morphismized
    assert not audit.polylogarithmic_in_span


def test_progression_cache_normalizes_translation_and_unit_scale_before_lowering() -> (
    None
):
    modulus = 1009
    arena = ProgressionProductArena()
    blocks = [
        ProgressionProductMorphism(modulus, 7 + 19 * i, 13, 32) for i in range(8)
    ] + [ProgressionProductMorphism(modulus, 5 + 23 * i, 17, 32) for i in range(8)]
    shapes = []
    actions = []
    for block in blocks:
        shape, action = arena.canonicalize(block)
        shapes.append(shape.canonical_key)
        actions.append(action)
    # Translation and any invertible root step are coordinate actions.  The
    # expensive algebraic structure is one width-32 shape.
    assert len(set(shapes)) == 1
    assert arena.raw_state_count == len(blocks)
    assert arena.algebraic_shape_count == 1
    assert arena.algebraic_compression_ratio == len(blocks)
    assert len(set(actions)) == len(blocks)


def test_bsgs_balanced_tree_hits_algebraic_shape_cache_before_absolute_lowering() -> (
    None
):
    audit = fast_multipoint_bend_audit("fermat", 5, start=1, span=511)
    assert audit.exact
    assert audit.raw_progression_states > audit.algebraic_progression_shapes
    assert audit.algebraic_progression_shapes <= 2 * audit.baby_width.bit_length()
    assert audit.algebraic_progression_compression > 4
    assert audit.algebraic_shape_cache_hits > audit.algebraic_shape_cache_misses
    # Coefficient lowering is still honestly charged separately.
    assert audit.morphism_cache_misses == audit.raw_progression_states
    assert not audit.polylogarithmic_in_span


def test_progression_lowering_does_not_recursively_call_public_materialize(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    arena = ProgressionProductArena()
    materialize = arena.materialize

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("recursive polynomial lowering")

    monkeypatch.setattr(ProgressionProductArena, "materialize", forbidden)
    block = ProgressionProductMorphism(101, 0, 1, 32)
    result = materialize(block, multiply=lambda left, right: _mul_mod(left, right, 101))
    assert len(result) == 33
    assert result[-1] == 1
