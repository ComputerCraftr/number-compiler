"""Bounded fixed-root/tangent audit for the decimal carry jet cylinder.

The root is derived from the affine kernel and emitted forcing.  This module
keeps the complete pair payload for the successor oracle and reports the
smallest counterexample when a proposed tangent signature is not successor
closed.  It is proof/audit code; no production identity is changed.
"""

from __future__ import annotations

import json
from dataclasses import asdict, dataclass
from itertools import product

from number_compiler.arithmetic.carry.decimal_jet_cylinder import (
    _CLOCK_POWERS,
    DecimalCarryJetBlock,
)
from number_compiler.arithmetic.carry.event_memory import (
    _pair_step_with_carry,
    forcing_event,
    pair_step,
)
from number_compiler.arithmetic.fields.radix import reverse_pair_sums
from number_compiler.arithmetic.polynomials.primary_jet import (
    PrimaryJetAffineMorphism,
    _poly_add,
    _poly_mul,
    _poly_scale,
    primary_jet_from_digits,
)

DEGREE = 5
MODULUS = 32
_ZERO = (0,) * DEGREE
_Y = (0, 1) + (0,) * (DEGREE - 2)
_NEG_Z_INVERSE = (1,) * DEGREE


def _jet(values: tuple[int, ...]) -> tuple[int, ...]:
    return primary_jet_from_digits(values, degree=DEGREE, modulus=MODULUS).jet


def _kernel(growth: int) -> tuple[int, ...]:
    if growth not in (0, 1):
        raise ValueError(growth)
    return (2,) + (0,) * (DEGREE - 1) if not growth else _Y


def _fixed_root(growth: int, birth: tuple[int, ...]) -> tuple[int, ...]:
    """Return ``-B`` for no-growth and ``-z^-1 B`` for growth."""
    if growth == 0:
        return _poly_scale(birth, -1, MODULUS)
    return _poly_mul(_NEG_Z_INVERSE, birth, MODULUS)


def _port_event(
    pair: tuple[int, ...], incoming: int
) -> tuple[tuple[int, ...], int, tuple[int, ...]]:
    """Exact physical counterfactual step for either incoming carry port."""
    return _pair_step_with_carry(pair, 10, incoming=incoming)


def _signature(pair: tuple[int, ...]) -> tuple[object, ...]:
    """Phase-typed exact root-normalized tangent signature for both ports."""
    source = _jet(pair)
    block = DecimalCarryJetBlock.from_pair(pair)
    rows: list[tuple[int, tuple[int, ...]]] = []
    for port in (0, 1):
        target, growth, _carry = _port_event(pair, port)
        # The shared cylinder owns the outgoing port; the full pair payload
        # remains available to the exact oracle and is deliberately not keyed.
        if block.cylinder.rows[port].outgoing != growth:
            raise AssertionError((pair, port, block.cylinder.rows[port], growth))
        birth = _jet(forcing_event(pair, target, growth))
        root = _fixed_root(growth, birth)
        tangent = _poly_add(source, _poly_scale(root, -1, MODULUS), MODULUS)
        rows.append(
            (growth, _poly_mul(_CLOCK_POWERS[-len(pair) % 128], tangent, MODULUS))
        )
        morphism = PrimaryJetAffineMorphism.reverse_add_event(
            forcing_event(pair, target, growth),
            growth,
            degree=DEGREE,
            modulus=MODULUS,
        )
        if morphism.apply(source) != _jet(target):
            raise AssertionError((pair, port, target))
    return (len(pair) % 128, tuple(g for g, _ in rows), tuple(w for _, w in rows))


@dataclass(frozen=True, slots=True)
class DecimalRootTangentAudit:
    source_states: int
    port_actions: int
    fixed_point_checks: int
    fixed_point_failures: int
    temporal_rebase_checks: int
    temporal_rebase_failures: int
    phase_rebase_checks: int
    phase_rebase_failures: int
    alias_fibers: int
    exact_successor_conflict_fibers: int
    successor_conflict_fibers: int
    witness: tuple[tuple[int, ...], ...] | None


def _event_root(
    pair: tuple[int, ...], port: int
) -> tuple[tuple[int, ...], int, tuple[int, ...], tuple[int, ...]]:
    target, growth, _carry = _port_event(pair, port)
    birth = _jet(forcing_event(pair, target, growth))
    return target, growth, birth, _fixed_root(growth, birth)


def audit_decimal_root_tangent(
    pairs: tuple[tuple[int, ...], ...] | None = None,
) -> DecimalRootTangentAudit:
    """Audit exact roots and expose the finite successor-conflict witness."""
    if pairs is None:
        pairs = tuple(
            left + tuple(reversed(left)) for left in product(range(19), repeat=3)
        )
    fixed_checks = rebase_checks = fixed_failures = rebase_failures = 0
    phase_checks = phase_failures = 0
    by_signature: dict[tuple[object, ...], list[tuple[int, ...]]] = {}
    for pair in pairs:
        if (
            not pair
            or pair != tuple(reversed(pair))
            or any(not 0 <= v <= 18 for v in pair)
        ):
            raise ValueError("audit requires a nonempty symmetric decimal pair field")
        source = _jet(pair)
        block = DecimalCarryJetBlock.from_pair(pair)
        for port in (0, 1):
            target, growth, birth, root = _event_root(pair, port)
            fixed_checks += 1
            if (
                _poly_add(_poly_mul(_kernel(growth), root, MODULUS), birth, MODULUS)
                != root
            ):
                fixed_failures += 1
            if block.cylinder.rows[port].outgoing != growth:
                raise AssertionError((pair, port, growth))
            next_target, next_growth, next_birth, next_root = _event_root(target, port)
            left = _poly_add(_jet(target), _poly_scale(next_root, -1, MODULUS), MODULUS)
            right = _poly_add(
                _poly_mul(
                    _kernel(growth),
                    _poly_add(source, _poly_scale(root, -1, MODULUS), MODULUS),
                    MODULUS,
                ),
                _poly_add(root, _poly_scale(next_root, -1, MODULUS), MODULUS),
                MODULUS,
            )
            rebase_checks += 1
            if left != right:
                rebase_failures += 1
            phase_checks += 1
            old_phase = _CLOCK_POWERS[-len(pair) % 128]
            new_phase = _CLOCK_POWERS[-len(target) % 128]
            normalized_left = _poly_mul(new_phase, left, MODULUS)
            tangent = _poly_add(source, _poly_scale(root, -1, MODULUS), MODULUS)
            transport = _poly_mul(
                _CLOCK_POWERS[-growth % 128], _kernel(growth), MODULUS
            )
            normalized_right = _poly_add(
                _poly_mul(transport, _poly_mul(old_phase, tangent, MODULUS), MODULUS),
                _poly_mul(
                    new_phase,
                    _poly_add(root, _poly_scale(next_root, -1, MODULUS), MODULUS),
                    MODULUS,
                ),
                MODULUS,
            )
            if normalized_left != normalized_right:
                phase_failures += 1
        by_signature.setdefault(_signature(pair), []).append(pair)
    aliases = [fiber for fiber in by_signature.values() if len(fiber) > 1]
    conflicts: list[tuple[tuple[int, ...], ...]] = []
    exact_conflicts = 0
    for fiber in aliases:
        successors = {pair_step(pair, 10)[0] for pair in fiber}
        exact_conflicts += int(len(successors) > 1)
        if len({_signature(target) for target in successors}) > 1:
            conflicts.append(tuple(fiber))
    return DecimalRootTangentAudit(
        len(pairs),
        2 * len(pairs),
        fixed_checks,
        fixed_failures,
        rebase_checks,
        rebase_failures,
        phase_checks,
        phase_failures,
        len(aliases),
        exact_conflicts,
        len(conflicts),
        conflicts[0] if conflicts else None,
    )


__all__ = ["DecimalRootTangentAudit", "audit_decimal_root_tangent"]


def build_report() -> dict[str, object]:
    """Separate exhaustive spatial gates from a charged primitive trajectory."""
    audit = audit_decimal_root_tangent()
    interned: dict[tuple[object, ...], int] = {}
    hits = 0
    pair = reverse_pair_sums(196, 10)
    growth = []
    for generation in range(1, 1025):
        pair = pair_step(pair, 10)[0]
        key = _signature(pair)
        if key in interned:
            hits += 1
        else:
            interned[key] = len(interned)
        if generation in (16, 32, 64, 128, 256, 512, 1024):
            growth.append(
                {
                    "generation": generation,
                    "width": len(pair),
                    "retained_tangent_ids": len(interned),
                    "tangent_cache_hits": hits,
                    "primitive_successors": generation,
                }
            )
    return {
        "spatial_audit": asdict(audit),
        "seed_196_growth": growth,
        "production_identity_changed": False,
        "phase_transport_includes_inverse_growth_clock": True,
    }


if __name__ == "__main__":
    print(json.dumps(build_report(), indent=2, sort_keys=True))
