"""Exact bounded binary-power jumps for Fermat and Mersenne proof states.

This module owns only the **bounded finite proof carrier** and its binary
jump program.  The canonical prime/composite successor-image semantics live in
:mod:`number_compiler.arithmetic.polynomials.two_primary_filtration`.  In particular the pure
two-primary depth theorem is no longer duplicated here.

Mersenne uses the exact ``x ~ -x`` sign carrier; Fermat uses the exact radix
orbit carrier with the delayed target observer.  Both builders remain bounded
reference/differential constructors and report ``scalable_construction=False``.
They must never be mistaken for the missing higher-``2^k`` character reader.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import cache
from hashlib import sha256

from devtools.proofs.immutable_artifacts import REGISTRY, ArtifactKey
from number_compiler.arithmetic.functions.finite_unary import (
    UnaryQuotientMachine,
    analyze_observer,
    minimize_unary_moore,
    quotient_machine_from_moore,
)


@dataclass(frozen=True, slots=True)
class SpecialBinaryJumpApplication:
    family: str
    parameter: int
    requested_steps: int
    quotient_steps: int
    state_class: int | None
    target: bool
    construction_compositions: int
    specialization_raw_squarings: int

    @property
    def fast_specialization(self) -> bool:
        return self.specialization_raw_squarings == 0


@dataclass(frozen=True, slots=True)
class _SpecialCarrierProof:
    """Transient complete carrier used by bounded proof construction only."""

    family: str
    parameter: int
    offset: int
    representatives: tuple[int, ...]
    transition: tuple[int, ...]
    outputs: tuple[bool, ...]
    source_carrier: int
    raw_source_states: int
    proof_states_examined: int
    construction_raw_squarings: int
    construction_radix_shifts: int

    @property
    def classes(self) -> int:
        return len(self.transition)


@dataclass(frozen=True, slots=True)
class SpecialBinaryJumpProgram:
    family: str
    parameter: int
    offset: int
    source_class: int
    machine: UnaryQuotientMachine
    raw_source_states: int
    carrier_classes: int
    proof_states_examined: int
    construction_raw_squarings: int
    construction_radix_shifts: int
    construction_is_exhaustive: bool = True
    scalable_construction: bool = False

    def __post_init__(self) -> None:
        if self.family not in ("fermat", "mersenne"):
            raise ValueError(self.family)
        if self.parameter < 0 or self.offset < 0:
            raise ValueError((self.parameter, self.offset))
        if not 0 <= self.source_class < self.machine.classes:
            raise ValueError((self.source_class, self.machine.classes))

    @property
    def quotient_classes(self) -> int:
        return self.machine.classes

    @property
    def quotient_state_bits(self) -> int:
        return self.machine.state_bits

    @property
    def retained_transition_bits(self) -> int:
        return self.machine.classes * self.quotient_state_bits

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "special-binary-jump",
            self.family,
            self.parameter,
            self.offset,
            self.source_class,
            self.machine.transition,
            self.machine.outputs,
        )

    def _reference_target(self, steps: int) -> bool:
        steps = int(steps)
        if self.family == "fermat":
            width = 1 << self.parameter
            modulus = (1 << width) + 1
            value = 3 % modulus
            for _ in range(steps):
                value = value * value % modulus
            return value == modulus - 1
        modulus = (1 << self.parameter) - 1
        value = 4 % modulus
        for _ in range(steps):
            value = (value * value - 2) % modulus
        return value == 0

    def apply(self, steps: int) -> SpecialBinaryJumpApplication:
        """Answer the canonical-source target at ``steps`` exactly.

        Fermat requests before the proved delayed-observer offset are evaluated
        by the explicit reference loop and fully charged.  All Mersenne requests
        and Fermat requests at/after the offset use only the powered quotient.
        """
        steps = int(steps)
        if steps < 0:
            raise ValueError(steps)
        if steps < self.offset:
            target = self._reference_target(steps)
            return SpecialBinaryJumpApplication(
                self.family,
                self.parameter,
                steps,
                0,
                None,
                target,
                0,
                steps,
            )
        quotient_steps = steps - self.offset
        state, ops, _nodes = self.machine.power_state(self.source_class, quotient_steps)
        return SpecialBinaryJumpApplication(
            self.family,
            self.parameter,
            steps,
            quotient_steps,
            state,
            bool(self.machine.output(state)),
            ops,
            0,
        )


def mersenne_sign_representative(value: int, exponent: int) -> int:
    """Canonical representative of the exact ``x ~ -x`` / ``Phi_p mod 2`` quotient."""
    p = int(exponent)
    if p < 2:
        raise ValueError(p)
    modulus = (1 << p) - 1
    value = int(value) % modulus
    return min(value, (-value) % modulus)


def _carrier_artifact_key(family: str, parameter: int) -> ArtifactKey:
    recipe = repr(
        (
            "special-carrier-proof-v1",
            family,
            int(parameter),
            "sign-square-minus-two" if family == "mersenne" else "radix-orbit-square",
        )
    ).encode("ascii")
    return ArtifactKey("special-carrier-proof", sha256(recipe).hexdigest())


def build_mersenne_carrier_proof_uncached(
    exponent: int, *, max_exponent: int = 19
) -> _SpecialCarrierProof:
    p = int(exponent)
    max_exponent = int(max_exponent)
    if p < 3 or p > max_exponent:
        raise ValueError((p, max_exponent))
    modulus = (1 << p) - 1
    carrier_classes = (modulus + 1) // 2
    representatives = tuple(range(carrier_classes))
    transition = tuple(
        mersenne_sign_representative((state * state - 2) % modulus, p)
        for state in representatives
    )
    outputs = tuple(state == 0 for state in representatives)
    analysis = analyze_observer(tuple(range(carrier_classes)), transition, outputs)
    if not analysis.closed:
        raise AssertionError((p, analysis))
    source_carrier = mersenne_sign_representative(4, p)
    return _SpecialCarrierProof(
        "mersenne",
        p,
        0,
        representatives,
        transition,
        outputs,
        source_carrier,
        modulus,
        carrier_classes,
        carrier_classes,
        0,
    )


def _mersenne_carrier_proof(
    exponent: int, *, max_exponent: int = 19
) -> _SpecialCarrierProof:
    """Reuse one immutable proof recipe without sharing a live proof runtime."""
    p, bound = int(exponent), int(max_exponent)
    if p < 3 or p > bound:
        raise ValueError((p, bound))
    proof, _hit = REGISTRY.obtain(
        _carrier_artifact_key("mersenne", p),
        lambda: build_mersenne_carrier_proof_uncached(p, max_exponent=bound),
    )
    return proof


@cache
def build_mersenne_binary_jump(
    exponent: int, *, max_exponent: int = 13
) -> SpecialBinaryJumpProgram:
    """Compile the exact bounded ``Phi_p mod 2`` Lucas--Lehmer jump.

    The cyclotomic carrier is theorem-equivalent to the sign quotient, so the
    compiler enumerates the canonical sign representatives directly instead of
    rebuilding both members of every pair.  This halves proof construction
    work while preserving the same exact partition.
    """
    p = int(exponent)
    max_exponent = int(max_exponent)
    proof = _mersenne_carrier_proof(p, max_exponent=max_exponent)
    minimized = minimize_unary_moore(proof.transition, proof.outputs)
    machine = quotient_machine_from_moore(
        proof.transition, proof.outputs, minimized.class_ids
    )
    source_class = minimized.class_ids[proof.source_carrier]
    return SpecialBinaryJumpProgram(
        "mersenne",
        p,
        proof.offset,
        source_class,
        machine,
        proof.raw_source_states,
        proof.classes,
        proof.proof_states_examined,
        proof.construction_raw_squarings,
        proof.construction_radix_shifts,
        True,
        False,
    )


def _fermat_radix_orbit_representative_with_shifts(
    value: int, index: int
) -> tuple[int, int]:
    """Return exact orbit minimum and charged radix shifts.

    The radix-root element itself has order ``2^(n+1)``, but an individual
    zero-divisor orbit in a composite residue ring can have a proper divisor of
    that period.  Stop on the actual return to the source rather than assuming
    every residue has the full group-orbit size.
    """
    n = int(index)
    if n < 1:
        raise ValueError(n)
    width = 1 << n
    modulus = (1 << width) + 1
    value = int(value) % modulus
    if value == 0:
        return 0, 0
    order = 2 * width
    best = value
    current = value
    for shifts in range(1, order + 1):
        current = (current << 1) % modulus
        if current == value:
            return best, shifts
        best = min(best, current)
    raise AssertionError(("bad-fermat-radix-order", n, value, current))


def fermat_radix_orbit_representative(value: int, index: int) -> int:
    """Canonicalize under the exact negacyclic radix-root action ``x -> 2*x``."""
    return _fermat_radix_orbit_representative_with_shifts(value, index)[0]


def build_fermat_carrier_proof_uncached(
    index: int, *, max_width: int = 16
) -> _SpecialCarrierProof:
    n = int(index)
    max_width = int(max_width)
    if n < 1:
        raise ValueError(n)
    width = 1 << n
    if width > max_width:
        raise ValueError((width, max_width))
    modulus = (1 << width) + 1
    order = 2 * width
    seen: set[int] = set()
    representatives_list: list[int] = []
    enumeration_radix_shifts = 0
    for state in range(modulus):
        if state in seen:
            continue
        if state == 0:
            seen.add(0)
            representatives_list.append(0)
            continue
        current = state
        orbit: list[int] = []
        for _ in range(order):
            orbit.append(current)
            seen.add(current)
            current = (2 * current) % modulus
            enumeration_radix_shifts += 1
            if current == state:
                break
        else:
            raise AssertionError(("fermat-radix-orbit-period", n, state, current))
        if state != min(orbit):
            raise AssertionError(
                ("fermat-radix-orbit-representative", n, state, min(orbit))
            )
        representatives_list.append(state)
    representatives = tuple(representatives_list)
    carrier_by_rep = {rep: index for index, rep in enumerate(representatives)}
    transition_list: list[int] = []
    transition_radix_shifts = 0
    for rep in representatives:
        successor_rep, shifts = _fermat_radix_orbit_representative_with_shifts(
            rep * rep % modulus, n
        )
        transition_radix_shifts += shifts
        transition_list.append(carrier_by_rep[successor_rep])
    transition = tuple(transition_list)

    offset = n + 1
    outputs: list[bool] = []
    for representative in representatives:
        value = representative
        for _ in range(offset):
            value = value * value % modulus
        outputs.append(value == modulus - 1)

    source_rep, source_radix_shifts = _fermat_radix_orbit_representative_with_shifts(
        3, n
    )
    source_carrier = carrier_by_rep[source_rep]
    return _SpecialCarrierProof(
        "fermat",
        n,
        offset,
        representatives,
        transition,
        tuple(outputs),
        source_carrier,
        modulus,
        modulus,
        len(representatives) * (offset + 1),
        enumeration_radix_shifts + transition_radix_shifts + source_radix_shifts,
    )


def _fermat_carrier_proof(index: int, *, max_width: int = 16) -> _SpecialCarrierProof:
    """Reuse one immutable proof recipe without sharing a live proof runtime."""
    n, bound = int(index), int(max_width)
    if n < 1:
        raise ValueError(n)
    width = 1 << n
    if width > bound:
        raise ValueError((width, bound))
    proof, _hit = REGISTRY.obtain(
        _carrier_artifact_key("fermat", n),
        lambda: build_fermat_carrier_proof_uncached(n, max_width=bound),
    )
    return proof


@cache
def build_fermat_binary_jump(
    index: int, *, max_width: int = 16
) -> SpecialBinaryJumpProgram:
    """Compile the exact delayed radix-orbit Pepin residual for a bounded F_n."""
    n = int(index)
    max_width = int(max_width)
    proof = _fermat_carrier_proof(n, max_width=max_width)
    minimized = minimize_unary_moore(proof.transition, proof.outputs)
    machine = quotient_machine_from_moore(
        proof.transition, proof.outputs, minimized.class_ids
    )
    source_class = minimized.class_ids[proof.source_carrier]
    return SpecialBinaryJumpProgram(
        "fermat",
        n,
        proof.offset,
        source_class,
        machine,
        proof.raw_source_states,
        proof.classes,
        proof.proof_states_examined,
        proof.construction_raw_squarings,
        proof.construction_radix_shifts,
        True,
        False,
    )


__all__ = [
    "SpecialBinaryJumpApplication",
    "SpecialBinaryJumpProgram",
    "build_fermat_binary_jump",
    "build_fermat_carrier_proof_uncached",
    "build_mersenne_binary_jump",
    "build_mersenne_carrier_proof_uncached",
    "fermat_radix_orbit_representative",
    "mersenne_sign_representative",
]
