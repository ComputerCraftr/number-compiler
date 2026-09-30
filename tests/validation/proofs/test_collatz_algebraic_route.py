from __future__ import annotations

import random
from typing import Never

import pytest

from devtools.verification.collatz_symbolic_action import CollatzSymbolicActionArena
from devtools.verification.extensional_family_application import (
    ExtensionalFamilyApplication,
)
from devtools.verification.lazy_collatz import LazyCollatzApplication
from number_compiler.arithmetic.contracts.physical_collatz_kernel import (
    PhysicalCollatzFourBlockEffect,
)
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.collatz.germ_cache import CollatzGermTransitionCache
from tests.support.reference_arithmetic import (
    physical_collatz_literal as _physical_oracle,
)


def _observed_value(term: PoweredCollatzTerm) -> int:
    width = term.width()
    return sum(term.digit(position) << position for position in range(width))


@pytest.mark.parametrize("seed", (2, 4, 6, 8, 12, 28, 96, 140))
@pytest.mark.parametrize("steps", (1, 2, 3, 4, 7, 12))
def test_algebraic_route_is_exact_for_even_starts(seed: int, steps: int) -> None:
    term = PoweredCollatzTerm(seed, steps)
    assert _observed_value(term) == _physical_oracle(seed, steps)


@pytest.mark.parametrize("steps", range(13))
def test_algebraic_route_preserves_every_fixed_cycle_phase(steps: int) -> None:
    term = PoweredCollatzTerm(1, steps)
    assert _observed_value(term) == _physical_oracle(1, steps)


def test_algebraic_route_random_small_differential() -> None:
    randomizer = random.Random(0xC011A72)
    for _ in range(40):
        seed = randomizer.randrange(1, 1 << 10)
        steps = randomizer.randrange(0, 17)
        term = PoweredCollatzTerm(seed, steps)
        assert _observed_value(term) == _physical_oracle(seed, steps)


def _poison(*_args: object, **_kwargs: object) -> Never:
    raise AssertionError("retired Collatz execution route was reached")


@pytest.mark.representation
def test_public_collatz_route_does_not_load_c4_or_legacy_executors(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(PhysicalCollatzFourBlockEffect, "__post_init__", _poison)
    monkeypatch.setattr(ExtensionalFamilyApplication, "__init__", _poison)
    monkeypatch.setattr(ExtensionalFamilyApplication, "_apply_machine", _poison)
    monkeypatch.setattr(ExtensionalFamilyApplication, "_run_verified_rungs", _poison)
    monkeypatch.setattr(LazyCollatzApplication, "advance_physical", _poison)
    monkeypatch.setattr(CollatzGermTransitionCache, "advance", _poison)
    monkeypatch.setattr(CollatzGermTransitionCache, "advance_many", _poison)
    monkeypatch.setattr(CollatzSymbolicActionArena, "project", _poison)

    term = PoweredCollatzTerm(27, 19)
    assert _observed_value(term) == _physical_oracle(27, 19)
    metrics = term.metrics()
    work = metrics.resource_work_counters
    assert work.get("whole_word_sweeps", 0) == 0
    assert work.get("whole_word_symbol_visits", 0) == 0
    assert work.get("proof_machine_applications", 0) == 0
    assert work.get("sequential_generation_advances", 0) == 0
