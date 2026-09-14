"""Bounded binary multiplication congruence for special-number carriers.

The experiment starts from the existing sign/radix-orbit carriers, verifies
their binary operation laws on complete small domains, and then refines the
actual carry-plus-harmonic consumer partition under multiplication.  Addition
is tested before refinement because neither carrier quotient is generally an
additive congruence.  No result here is a scheduler certificate.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from typing import Protocol

from devtools.proofs.oracles.special_binary_jump import (
    _fermat_carrier_proof,
    _mersenne_carrier_proof,
    fermat_radix_orbit_representative,
    mersenne_sign_representative,
)
from number_compiler.arithmetic.functions.finite_observer import (
    minimize_finite_observer,
)
from number_compiler.arithmetic.polynomials.arithmetic_tile import (
    ArithmeticTile,
    ArithmeticTileSpec,
)


@dataclass(frozen=True, slots=True)
class BinaryClosureWitness:
    operation: str
    lhs: int
    lhs_alias: int
    rhs: int
    rhs_alias: int
    first_target: int
    second_target: int


@dataclass(frozen=True, slots=True)
class CarrierBinaryClosureAudit:
    family: str
    parameter: int
    modulus: int
    carrier_classes: int
    multiplication_closed: bool
    addition_closed: bool
    multiplication_witness: BinaryClosureWitness | None
    addition_witness: BinaryClosureWitness | None


@dataclass(frozen=True, slots=True)
class MultiplicationPreflightAudit:
    family: str
    parameter: int
    carrier_classes: int
    multiplication_congruence_method: str
    addition_witness: BinaryClosureWitness
    cartesian_cells: int
    refinement_cell_budget: int
    refinement_admitted: bool


@dataclass(frozen=True, slots=True)
class MultiplicationRefinementWitness:
    source: int
    source_alias: int
    multiplier: int
    first_target_class: int
    second_target_class: int


@dataclass(frozen=True, slots=True)
class MultiplicationConsumerCongruenceAudit:
    family: str
    parameter: int
    carrier_classes: int
    initial_consumer_classes: int
    initial_multiplication_conflicts: int
    multiplication_cells_examined: int
    refinement_rounds: int
    refinement_cells_examined: int
    quotient_verification_cells: int
    stable_classes: int
    multiplication_well_defined: bool
    square_well_defined: bool
    noninjective: bool
    quotient_table_published: bool
    quotient_multiplication_table: tuple[tuple[int, ...], ...] | None
    quotient_square_table: tuple[int, ...] | None
    first_refinement_witness: MultiplicationRefinementWitness | None
    addition_available: bool
    scheduler_promotion_safe: bool


class _CarrierProof(Protocol):
    @property
    def representatives(self) -> tuple[int, ...]: ...

    @property
    def classes(self) -> int: ...


def _carrier(family: str, parameter: int) -> tuple[_CarrierProof, int, tuple[int, ...]]:
    family, parameter = str(family), int(parameter)
    proof = (
        _fermat_carrier_proof(parameter)
        if family == "fermat"
        else _mersenne_carrier_proof(parameter)
    )
    width = (1 << parameter) if family == "fermat" else parameter
    modulus = (1 << width) - (-1 if family == "fermat" else 1)
    return proof, modulus, proof.representatives


def _representative(family: str, parameter: int, value: int) -> int:
    if family == "fermat":
        return fermat_radix_orbit_representative(value, parameter)
    return mersenne_sign_representative(value, parameter)


def _members(
    family: str, parameter: int, modulus: int, representatives: tuple[int, ...]
) -> tuple[tuple[int, ...], ...]:
    index = {value: i for i, value in enumerate(representatives)}
    out: list[list[int]] = [[] for _ in representatives]
    for value in range(modulus):
        out[index[_representative(family, parameter, value)]].append(value)
    return tuple(tuple(row) for row in out)


def _operation_witness(
    family: str,
    parameter: int,
    members: tuple[tuple[int, ...], ...],
    *,
    operation: str,
    modulus: int,
) -> BinaryClosureWitness | None:
    for left in members:
        for right in members:
            target: int | None = None
            first: tuple[int, int] | None = None
            for x in left:
                for y in right:
                    value = x * y if operation == "multiply" else x + y
                    image = _representative(family, parameter, value % modulus)
                    if target is None:
                        target, first = image, (x, y)
                    elif image != target:
                        assert first is not None
                        return BinaryClosureWitness(
                            operation,
                            first[0],
                            x,
                            first[1],
                            y,
                            target,
                            image,
                        )
    return None


@lru_cache(maxsize=1)
def carrier_binary_closure_audits() -> tuple[CarrierBinaryClosureAudit, ...]:
    rows: list[CarrierBinaryClosureAudit] = []
    for family, parameter in (
        ("fermat", 2),
        ("fermat", 3),
        ("mersenne", 5),
        ("mersenne", 7),
    ):
        proof, modulus, representatives = _carrier(family, parameter)
        members = _members(family, parameter, modulus, representatives)
        multiplication = _operation_witness(
            family,
            parameter,
            members,
            operation="multiply",
            modulus=modulus,
        )
        addition = _operation_witness(
            family,
            parameter,
            members,
            operation="add",
            modulus=modulus,
        )
        rows.append(
            CarrierBinaryClosureAudit(
                family,
                parameter,
                modulus,
                proof.classes,
                multiplication is None,
                addition is None,
                multiplication,
                addition,
            )
        )
    return tuple(rows)


@lru_cache(maxsize=1)
def multiplication_preflight_audits() -> tuple[MultiplicationPreflightAudit, ...]:
    """Exact algebraic admission gate before any Cartesian refinement."""
    rows: list[MultiplicationPreflightAudit] = []
    budget = 4096
    for family, parameter in (
        ("fermat", 2),
        ("fermat", 3),
        ("fermat", 4),
        ("mersenne", 5),
        ("mersenne", 7),
        ("mersenne", 11),
        ("mersenne", 13),
    ):
        proof, modulus, _representatives = _carrier(family, parameter)
        if family == "fermat":
            alias = 2
            method = "radix-orbit:(2^a*x)(2^b*y)=2^(a+b)*xy"
        else:
            alias = modulus - 1
            method = "sign-orbit:(-x)y=-(xy)"
        first = _representative(family, parameter, 1 + 1)
        second = _representative(family, parameter, alias + 1)
        if first == second:
            raise AssertionError((family, parameter, first, second))
        witness = BinaryClosureWitness(
            "add",
            1,
            alias,
            1,
            1,
            first,
            second,
        )
        cells = proof.classes * proof.classes
        rows.append(
            MultiplicationPreflightAudit(
                family,
                parameter,
                proof.classes,
                method,
                witness,
                cells,
                budget,
                cells <= budget,
            )
        )
    return tuple(rows)


def _consumer_keys(
    family: str, parameter: int, representatives: tuple[int, ...]
) -> tuple[tuple[object, ...], ...]:
    width = (1 << parameter) if family == "fermat" else parameter
    spec = getattr(ArithmeticTileSpec, family)(width)
    intervals = tuple(
        ArithmeticTile.from_value(spec, value).step_with_carry_interval()[1]
        for value in representatives
    )
    lo = min(interval[0] for interval in intervals)
    hi = max(interval[1] for interval in intervals)
    keys = []
    for value in representatives:
        step, harmonic = ArithmeticTile.from_value(
            spec, value
        ).step_with_harmonic_consumer(
            incoming_min=lo,
            incoming_max=hi,
            order=4,
            modulus=2,
        )
        carry = step.boundary_action(incoming_min=lo, incoming_max=hi)
        keys.append((carry.canonical_key, harmonic.canonical_key))
    return tuple(keys)


def _class_ids(keys: tuple[object, ...]) -> tuple[int, ...]:
    classes: dict[object, int] = {}
    return tuple(classes.setdefault(key, len(classes)) for key in keys)


def _multiplication_table(
    family: str,
    parameter: int,
    representatives: tuple[int, ...],
    modulus: int,
) -> tuple[tuple[int, ...], ...]:
    index = {value: i for i, value in enumerate(representatives)}
    return tuple(
        tuple(
            index[_representative(family, parameter, (x * y) % modulus)]
            for y in representatives
        )
        for x in representatives
    )


def _first_conflict(
    ids: tuple[int, ...], table: tuple[tuple[int, ...], ...]
) -> tuple[int, MultiplicationRefinementWitness | None]:
    rows: dict[int, tuple[int, ...]] = {}
    sources: dict[int, int] = {}
    conflicts = 0
    witness = None
    for source, class_id in enumerate(ids):
        row = tuple(ids[target] for target in table[source])
        previous = rows.setdefault(class_id, row)
        previous_source = sources.setdefault(class_id, source)
        if row == previous:
            continue
        conflicts += 1
        if witness is None:
            multiplier = next(
                i for i, pair in enumerate(zip(previous, row)) if pair[0] != pair[1]
            )
            witness = MultiplicationRefinementWitness(
                previous_source,
                source,
                multiplier,
                previous[multiplier],
                row[multiplier],
            )
    return conflicts, witness


def _refine_multiplication(
    initial: tuple[int, ...], table: tuple[tuple[int, ...], ...]
) -> tuple[tuple[int, ...], int]:
    result = minimize_finite_observer(table, initial)
    return result.class_ids, result.rounds


def _quotient_table(
    ids: tuple[int, ...], table: tuple[tuple[int, ...], ...]
) -> tuple[tuple[int, ...], ...] | None:
    classes = max(ids) + 1
    members = tuple(
        tuple(i for i, value in enumerate(ids) if value == c) for c in range(classes)
    )
    out = []
    for left in members:
        row = []
        for right in members:
            targets = {ids[table[x][y]] for x in left for y in right}
            if len(targets) != 1:
                return None
            row.append(next(iter(targets)))
        out.append(tuple(row))
    return tuple(out)


@lru_cache(maxsize=1)
def multiplication_consumer_congruence_audits() -> tuple[
    MultiplicationConsumerCongruenceAudit, ...
]:
    closure = {
        (row.family, row.parameter): row for row in carrier_binary_closure_audits()
    }
    rows: list[MultiplicationConsumerCongruenceAudit] = []
    admitted = {
        (row.family, row.parameter)
        for row in multiplication_preflight_audits()
        if row.refinement_admitted
    }
    for (family, parameter), closure_row in closure.items():
        if (family, parameter) not in admitted:
            continue
        proof, modulus, representatives = _carrier(family, parameter)
        initial = _class_ids(_consumer_keys(family, parameter, representatives))
        table = _multiplication_table(family, parameter, representatives, modulus)
        conflicts, witness = _first_conflict(initial, table)
        stable, rounds = _refine_multiplication(initial, table)
        quotient = _quotient_table(stable, table)
        classes = max(stable) + 1
        noninjective = classes < proof.classes
        if quotient is not None and noninjective:
            published = True
            published_table = quotient
            square = tuple(quotient[i][i] for i in range(classes))
        else:
            published = False
            published_table = None
            square = None
        rows.append(
            MultiplicationConsumerCongruenceAudit(
                family,
                parameter,
                proof.classes,
                max(initial) + 1,
                conflicts,
                proof.classes * proof.classes,
                rounds,
                (rounds + 1) * proof.classes * proof.classes,
                proof.classes * proof.classes,
                classes,
                quotient is not None,
                square is not None,
                noninjective,
                published,
                published_table,
                square,
                witness,
                closure_row.addition_closed,
                False,
            )
        )
    return tuple(rows)


__all__ = [
    "BinaryClosureWitness",
    "CarrierBinaryClosureAudit",
    "MultiplicationConsumerCongruenceAudit",
    "MultiplicationPreflightAudit",
    "MultiplicationRefinementWitness",
    "carrier_binary_closure_audits",
    "multiplication_consumer_congruence_audits",
    "multiplication_preflight_audits",
]
