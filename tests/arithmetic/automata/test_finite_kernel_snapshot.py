"""Finite definitions cannot change beneath warm or cold action caches."""

from __future__ import annotations

import gc
import weakref
from collections.abc import Callable
from typing import Never, cast

import pytest

import number_compiler.arithmetic.automata.symmetry_powering as shared_powering
from number_compiler.arithmetic.automata.symmetry_powering import (
    FiniteKernel,
    OrientedFiniteActionArena,
)


def test_kernel_snapshots_each_transition_once_and_releases_live_callback() -> None:
    class MutableTransition:
        def __init__(self) -> None:
            self.flip = 0
            self.calls: list[tuple[int, int]] = []

        def __call__(self, state: int, symbol: int) -> int:
            self.calls.append((state, symbol))
            return state ^ symbol ^ self.flip

    transition = MutableTransition()
    weak = weakref.ref(transition)
    kernel = FiniteKernel(2, 2, transition)
    assert transition.calls == [(0, 0), (0, 1), (1, 0), (1, 1)]
    arena = OrientedFiniteActionArena(kernel)
    warm = arena.leaf(0)
    transition.flip = 1
    cold = arena.leaf(1)
    assert tuple(arena.apply(warm, state) for state in range(2)) == (0, 1)
    assert tuple(arena.apply(cold, state) for state in range(2)) == (1, 0)
    assert kernel.transition_table == ((0, 1), (1, 0))
    assert len(transition.calls) == 4
    del transition
    gc.collect()
    assert weak() is None


def test_kernel_equality_is_extensional_and_verifies_digest_collisions(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    class ConstantDigest:
        def hexdigest(self) -> str:
            return "intentional-collision"

    monkeypatch.setattr(shared_powering, "sha256", lambda _data: ConstantDigest())
    first = FiniteKernel(2, 1, lambda state, _symbol: state, name="one")
    alias = FiniteKernel(2, 1, lambda state, _symbol: state, name="different-name")
    different = FiniteKernel(2, 1, lambda state, _symbol: 1 - state, name="one")
    assert first.semantic_digest == alias.semantic_digest == different.semantic_digest
    assert first == alias
    assert hash(first) == hash(alias)
    assert first != different
    assert len({first, alias, different}) == 2


@pytest.mark.parametrize("target", (-1, 2, 0.5))
def test_kernel_rejects_transitions_outside_its_finite_domain(
    target: float | int,
) -> None:
    with pytest.raises(ValueError, match="outside finite state domain"):
        FiniteKernel(
            2, 1, cast("Callable[[int, int], int]", lambda _state, _symbol: target)
        )


def test_conjugacy_proof_reads_frozen_table_after_callable_mutation() -> None:
    behavior = [0, 1]
    kernel = FiniteKernel(2, 1, lambda state, _symbol: behavior[state], (1, 0), (0,))
    behavior[:] = [0, 0]
    kernel.verify_conjugacy()
    assert (kernel.transition(0, 0), kernel.transition(1, 0)) == (0, 1)


def test_kernel_subclass_cannot_replace_frozen_execution_with_a_live_callable() -> None:
    with pytest.raises(TypeError, match="frozen table"):

        class MutableKernel(FiniteKernel):
            def transition(self, state: int, symbol: object) -> int:
                return 1 - state


@pytest.mark.parametrize(
    ("states", "alphabet"),
    ((True, 2), (2, False), (2.0, 2), (2, 2.0)),
)
def test_kernel_dimensions_reject_integer_aliases_before_reading_transition(
    states: bool | float | int, alphabet: bool | float | int
) -> None:
    calls = []

    def transition(state: int, symbol: int) -> int:
        calls.append((state, symbol))
        return 0

    with pytest.raises(TypeError, match="exact integers"):
        FiniteKernel(cast("int", states), cast("int", alphabet), transition)
    assert calls == []


def test_kernel_conjugacies_and_transition_results_reject_integer_aliases() -> None:
    with pytest.raises(TypeError, match="exact integers"):
        FiniteKernel(2, 1, lambda state, _symbol: state, (True, 0), (0,))
    with pytest.raises(ValueError, match="outside finite state domain"):
        FiniteKernel(2, 1, lambda _state, _symbol: False)


@pytest.mark.parametrize("limit", (True, 1.0, "1"))
def test_oriented_arena_cache_limit_rejects_integer_aliases(
    limit: bool | float | str,
) -> None:
    kernel = FiniteKernel(1, 1, lambda _state, _symbol: 0)
    with pytest.raises(TypeError, match="exact integer"):
        OrientedFiniteActionArena(kernel, compose_cache_limit=cast("int", limit))


def test_oriented_arena_rejects_negative_cache_limit_and_kernel_subtypes() -> None:
    kernel = FiniteKernel(1, 1, lambda _state, _symbol: 0)
    with pytest.raises(ValueError, match="nonnegative"):
        OrientedFiniteActionArena(kernel, compose_cache_limit=-1)

    class KernelProxy:
        def verify_conjugacy(self) -> Never:
            raise AssertionError("must reject before invoking proxy behavior")

    with pytest.raises(TypeError, match="exact frozen finite kernel"):
        OrientedFiniteActionArena(KernelProxy())  # type: ignore[arg-type]
