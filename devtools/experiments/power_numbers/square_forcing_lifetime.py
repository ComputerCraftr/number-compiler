"""Bounded audit of finite-lifetime square forcing and surviving birth clocks.

The square tangent on a primary germ is ``J -> 2*X*J``.  Modulo 32, five
composed tangents kill every old source occurrence.  This module measures the
resulting action-key collapse on complete small Fermat/Mersenne residue rings
while keeping a separate odd cyclotomic clock for newly born forcing.

The fold controls explicitly show why valuation alone is not a sufficient
future response.  This is bounded research evidence, not a scheduler or prime
certificate.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache

from number_compiler.arithmetic.polynomials.arithmetic_tile import ArithmeticTileSpec
from number_compiler.arithmetic.polynomials.digit_convolution import (
    fold_cyclic,
    fold_negacyclic,
)
from number_compiler.arithmetic.polynomials.primary_jet import (
    PrimaryJetAffineMorphism,
)


@dataclass(frozen=True, slots=True)
class SquareForcingLifetimeAudit:
    family: str
    parameter: int
    source_states: int
    horizon: int
    raw_history_occurrences: int
    canonical_tangent_actions: int
    death_depth: int
    post_death_occurrences: int
    post_death_tangent_actions: int
    canonical_key_hits_after_death: int
    surviving_birth_actions_after_source_death: int
    production_interner_present: bool
    birth_clock_order: int
    birth_clock_period: int
    post_death_clock_phases: int
    scalar_differential_checks: int
    scalar_differential_exact: bool
    equal_valuation_fold_responses_distinct: bool
    valuation_only_identity_safe: bool
    clock_removed_from_birth_identity: bool
    scheduler_promotion_safe: bool


def _parameters() -> tuple[tuple[str, int], ...]:
    return (
        ("fermat", 2),
        ("fermat", 3),
        ("mersenne", 5),
        ("mersenne", 7),
    )


def _fold_control(family: str, width: int) -> bool:
    first = [0] * (width + 1)
    second = [0] * (width + 1)
    first[0] = 2
    if family == "fermat":
        # Equal-valuation low and wrapped-high forcing have opposite seam sign.
        second[width] = 2
        left = fold_negacyclic(first, width)
        right = fold_negacyclic(second, width)
    else:
        # Valuation also omits spatial phase within the cyclic fold.
        second[1] = 2
        left = fold_cyclic(first, width)
        right = fold_cyclic(second, width)
    return left != right


def _audit(
    family: str, parameter: int, *, horizon: int = 9
) -> SquareForcingLifetimeAudit:
    width = (1 << parameter) if family == "fermat" else parameter
    spec = getattr(ArithmeticTileSpec, family)(width)
    modulus = spec.modulus
    degree = death_depth = 5
    coefficient_modulus = 32
    clock_order = 5
    raw: set[tuple[int, int]] = set()
    actions: set[tuple[object, ...]] = set()
    post_actions: set[tuple[object, ...]] = set()
    post_clocks: set[int] = set()
    post_occurrences = 0
    differential_checks = 0
    differential_exact = True
    surviving_birth_actions: set[tuple[object, ...]] = set()

    for source in range(modulus):
        value = source
        action = PrimaryJetAffineMorphism.identity(degree, coefficient_modulus)
        raw.add((source, 0))
        actions.add(action.canonical_key)
        for depth in range(1, horizon + 1):
            base = (value % coefficient_modulus,) + (0,) * (degree - 1)
            action = action.then(
                PrimaryJetAffineMorphism.square_tangent(
                    base, degree=degree, modulus=coefficient_modulus
                )
            )
            raw.add((source, depth))
            actions.add(action.canonical_key)
            if depth >= death_depth:
                if not action.source_annihilated:
                    raise AssertionError((family, parameter, source, depth))
                post_occurrences += 1
                post_actions.add(action.canonical_key)
                post_clocks.add(pow(2, depth, clock_order))
            value = (value * value + spec.addend) % modulus

        # The exact scalar identity includes the quadratic term as a new birth.
        x = source % coefficient_modulus
        for delta in range(coefficient_modulus):
            left = ((x + delta) ** 2 - x * x) % coefficient_modulus
            right = (2 * x * delta + delta * delta) % coefficient_modulus
            differential_checks += 1
            differential_exact &= left == right

        born = PrimaryJetAffineMorphism.identity(degree, coefficient_modulus)
        base = (source % coefficient_modulus,) + (0,) * (degree - 1)
        for depth in range(1, death_depth + 1):
            birth = base if depth == death_depth else ()
            born = born.then(
                PrimaryJetAffineMorphism.square_tangent(
                    base,
                    birth,
                    degree=degree,
                    modulus=coefficient_modulus,
                )
            )
        if not born.source_annihilated:
            raise AssertionError((family, parameter, source, born.kernel))
        surviving_birth_actions.add(born.canonical_key)

    return SquareForcingLifetimeAudit(
        family,
        parameter,
        modulus,
        horizon,
        len(raw),
        len(actions),
        death_depth,
        post_occurrences,
        len(post_actions),
        post_occurrences - len(post_actions),
        len(surviving_birth_actions),
        False,
        clock_order,
        4,
        len(post_clocks),
        differential_checks,
        differential_exact,
        _fold_control(family, width),
        False,
        False,
        False,
    )


@lru_cache(maxsize=1)
def square_forcing_lifetime_audits() -> tuple[SquareForcingLifetimeAudit, ...]:
    return tuple(_audit(family, parameter) for family, parameter in _parameters())


__all__ = ["SquareForcingLifetimeAudit", "square_forcing_lifetime_audits"]
