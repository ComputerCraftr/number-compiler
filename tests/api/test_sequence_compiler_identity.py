"""Sequence compilation validates semantic sorts before warm cache probes."""

from typing import cast

import pytest

from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler
from number_compiler.api.sequence_types import ReverseAddSequenceSpec


@pytest.mark.parametrize("alias", [0, 1, 0.0, 1.0, "false"])
def test_diagnostics_requires_an_actual_boolean_before_compilation(
    alias: object,
) -> None:
    compiler = CanonicalSequenceCompiler()
    with pytest.raises(TypeError, match="diagnostics must be a Boolean"):
        compiler.compile(
            ReverseAddSequenceSpec(1, steps=0), diagnostics=cast(bool, alias)
        )
    assert compiler.cache_size == 0


def test_foreign_spec_cannot_use_a_warm_semantic_key() -> None:
    compiler = CanonicalSequenceCompiler()
    spec = ReverseAddSequenceSpec(1, steps=0)
    expected = compiler.compile(spec)

    class Counterfeit:
        canonical_key = spec.canonical_key

    with pytest.raises(TypeError, match="exact sequence specification"):
        compiler.compile(cast(ReverseAddSequenceSpec, Counterfeit()))
    assert compiler.compile(spec) is expected
    assert compiler.cache_size == 1


def test_mutated_frozen_spec_rejects_before_warm_lookup() -> None:
    compiler = CanonicalSequenceCompiler()
    spec = ReverseAddSequenceSpec(1, steps=0)
    compiler.compile(spec)
    object.__setattr__(spec, "seed", True)
    with pytest.raises(TypeError, match="exact integers"):
        compiler.compile(spec)
    assert compiler.cache_size == 1


def test_special_theorem_integer_aliases_reject_before_warm_lookup() -> None:
    compiler = CanonicalSequenceCompiler()
    expected = compiler.resolve_special_theorem("fermat", 2)
    size = compiler.theorem_cache_size
    with pytest.raises(TypeError, match="special parameter"):
        compiler.resolve_special_theorem("fermat", True)
    with pytest.raises(TypeError, match="policies must be Booleans"):
        compiler.resolve_special_theorem("fermat", 2, use_factor_projection=1)  # type: ignore[arg-type]
    assert (
        compiler.resolve_special_theorem("fermat", 2).source_guard.failure_bit
        is expected.source_guard.failure_bit
    )
    assert compiler.theorem_cache_size == size


@pytest.mark.parametrize("alias", [True, 3.0, "3"])
def test_special_output_coordinates_reject_integer_aliases(alias: object) -> None:
    compiler = CanonicalSequenceCompiler()
    with pytest.raises(TypeError):
        compiler.project_special_branch_values("fermat", 2, alias, 7)  # type: ignore[arg-type]
    assert compiler.special_constraint_cache_size == 0
