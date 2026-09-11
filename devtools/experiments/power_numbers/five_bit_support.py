"""Bounded factor-truth audit for the five-bit folded-square observer.

This module is research scaffolding.  The CRT sheets below are assembled from
supplied, complete factorizations already owned by
``special_source_certificate``.  They test what the arithmetic observer sees;
they do not provide a candidate-derived support query or a primality
certificate.

The two supplied F9 divisors are deliberately excluded from the classification
corpus because they are not a complete factorization.  Their only role here is
to keep that evidence boundary visible.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations, product
from math import gcd, prod

from devtools.experiments.algebra.dyadic_difference_germ_core import (
    ambient_capacity_truth,
    mixed_capacity_controls,
)
from devtools.experiments.power_numbers.special_source_certificate import (
    _FERMAT_FACTORS,
    _MERSENNE_FACTORS,
)
from devtools.experiments.power_numbers.special_germ_descent import _crt_pairwise
from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.arithmetic.polynomials.folded_square_packet import (
    FoldedSquarePacket,
    FoldedSquareProjection,
    folded_square_packet,
)
from number_compiler.arithmetic.polynomials.digit_convolution import (
    adaptive_square_convolution,
    fold_cyclic,
    fold_negacyclic,
)
from number_compiler.sequences.power_numbers.numbers import (
    fermat_number,
    mersenne_number,
)
from number_compiler.sequences.prime.set import jacobi_symbol


@dataclass(frozen=True, slots=True)
class SuppliedFactorSheet:
    family: str
    parameter: int
    modulus: int
    factors: tuple[int, ...]
    sign: int
    coefficient_width: int
    complete_factorization: bool = True
    source: str = "supplied-complete-factor-truth"


@dataclass(frozen=True, slots=True)
class OrientationPacketRow:
    sheet: SuppliedFactorSheet
    orientations: tuple[int, ...]
    representative: int
    defect: int
    coefficients: tuple[int, ...]
    projection: FoldedSquareProjection

    @property
    def all_pass(self) -> bool:
        return all(value == 1 for value in self.orientations)

    @property
    def matches_sheet_all_pass(self) -> bool:
        """Whether the packet recognizes all supplied sheet components."""
        return self.projection.vanishes == self.all_pass

    @property
    def five_bits(self) -> tuple[int, int, int, int, int]:
        return (
            self.projection.r1_mod4 & 1,
            (self.projection.r1_mod4 >> 1) & 1,
            self.projection.r2_mod8 & 1,
            (self.projection.r2_mod8 >> 1) & 1,
            (self.projection.r2_mod8 >> 2) & 1,
        )


@dataclass(frozen=True, slots=True)
class DenseDifferential:
    packet: FoldedSquarePacket
    dense_r1: int
    dense_r2: int

    @property
    def exact(self) -> bool:
        return self.packet.canonical_key == (self.dense_r1 % 4, self.dense_r2 % 8)


@dataclass(frozen=True, slots=True)
class MinimumBitAudit:
    corpus_rows: int
    minimum_bits: int
    sufficient_masks: tuple[tuple[int, ...], ...]
    minimum_power_modulus_bits: int
    sufficient_power_moduli: tuple[tuple[int, int], ...]
    bit_names: tuple[str, ...] = (
        "r1_mod4.bit0",
        "r1_mod4.bit1",
        "r2_mod8.bit0",
        "r2_mod8.bit1",
        "r2_mod8.bit2",
    )


@dataclass(frozen=True, slots=True)
class PacketCollision:
    family: str
    parameter: int
    packet: FoldedSquarePacket
    left_orientations: tuple[int, ...]
    right_orientations: tuple[int, ...]
    left_dense_coefficients: tuple[int, int]
    right_dense_coefficients: tuple[int, int]


@dataclass(frozen=True, slots=True)
class TemporalFirstHoleAudit:
    family: str
    parameter: int
    local_depths: tuple[int, ...]
    first_hole_level: int
    rows: tuple[OrientationPacketRow, ...]

    @property
    def exact(self) -> bool:
        return all(row.projection.vanishes for row in self.rows[:-1]) and (
            not self.rows[-1].projection.vanishes
        )


@dataclass(frozen=True, slots=True)
class EvidenceBoundary:
    excluded_family: str
    excluded_parameter: int
    supplied_divisors: tuple[int, ...]
    divisors_verified: bool
    complete_factorization: bool = False
    status: str = "unverified-requested-case"


@dataclass(frozen=True, slots=True)
class ProjectionCostAudit:
    family: str
    parameter: int
    sheet_rows: int
    maximum_coefficient_reads: int
    maximum_pair_visits: int
    maximum_scalar_products: int


@dataclass(frozen=True, slots=True)
class UnrestrictedSheetCounterexample:
    row: OrientationPacketRow
    local_depths: tuple[int, ...]
    nontrivial_defect_gcd: int
    status: str = "unrestricted-sheet-generalization-failure"


def supplied_factor_sheets() -> tuple[SuppliedFactorSheet, ...]:
    """Return only tables whose listed factors multiply to the candidate."""
    rows: list[SuppliedFactorSheet] = []
    for parameter, factors in sorted(_FERMAT_FACTORS.items()):
        modulus = fermat_number(parameter)
        if prod(factors) != modulus:
            raise AssertionError(("incomplete-fermat-sheet", parameter))
        rows.append(
            SuppliedFactorSheet(
                "fermat", parameter, modulus, factors, -1, 1 << parameter
            )
        )
    for parameter, factors in sorted(_MERSENNE_FACTORS.items()):
        modulus = mersenne_number(parameter)
        if prod(factors) != modulus:
            raise AssertionError(("incomplete-mersenne-sheet", parameter))
        rows.append(
            SuppliedFactorSheet("mersenne", parameter, modulus, factors, 1, parameter)
        )
    return tuple(rows)


def partial_f9_sheet() -> SuppliedFactorSheet:
    """Return the two-divisor F9 local sheet, explicitly not the whole candidate."""
    control = next(
        row
        for row in mixed_capacity_controls()
        if row.family == "fermat" and row.parameter == 9
    )
    if not control.factor_witnesses_valid:
        raise AssertionError(control)
    factors = control.supplied_factors
    return SuppliedFactorSheet(
        "fermat",
        9,
        prod(factors),
        factors,
        -1,
        1 << 9,
        False,
        "supplied-partial-divisor-truth",
    )


def _crt_orientation(
    modulus: int, factors: tuple[int, ...], orientations: tuple[int, ...]
) -> int:
    if (
        len(factors) != len(orientations)
        or not factors
        or prod(factors) != modulus
        or any(orientation not in (-1, 1) for orientation in orientations)
    ):
        raise ValueError((factors, orientations))
    representative = _crt_pairwise(orientations, factors)
    if any(representative % q != orientation % q for q, orientation in zip(
        factors, orientations, strict=True
    )):
        raise AssertionError((representative, orientations))
    return representative


def orientation_packet_row(
    sheet: SuppliedFactorSheet, orientations: tuple[int, ...]
) -> OrientationPacketRow:
    representative = _crt_orientation(sheet.modulus, sheet.factors, orientations)
    defect = (representative - 1) % sheet.modulus
    coefficients = tuple(
        (defect >> position) & 1 for position in range(sheet.coefficient_width)
    )
    projection = folded_square_packet(coefficients, sign=sheet.sign)
    return OrientationPacketRow(
        sheet, orientations, representative, defect, coefficients, projection
    )


def orientation_sheet(sheet: SuppliedFactorSheet) -> tuple[OrientationPacketRow, ...]:
    return tuple(
        orientation_packet_row(sheet, tuple(orientations))
        for orientations in product((-1, 1), repeat=len(sheet.factors))
    )


def assembled_factor_truth_corpus() -> tuple[OrientationPacketRow, ...]:
    """All orientation sheets over the actual complete supplied corpus."""
    return tuple(row for sheet in supplied_factor_sheets() for row in orientation_sheet(sheet))


def assembled_local_support_corpus() -> tuple[OrientationPacketRow, ...]:
    """Complete sheets plus the four explicitly local F9 two-divisor rows."""
    return assembled_factor_truth_corpus() + orientation_sheet(partial_f9_sheet())


def dense_folded_square_differential(row: OrientationPacketRow) -> DenseDifferential:
    """Compare the packet with the canonical complete-convolution owner."""
    full, _metrics = adaptive_square_convolution(row.coefficients)
    fold = fold_cyclic if row.sheet.sign == 1 else fold_negacyclic
    dense = fold(full, len(row.coefficients))
    return DenseDifferential(
        row.projection.packet,
        dense[1],
        dense[2],
    )


def minimum_bit_audit(
    corpus: tuple[OrientationPacketRow, ...] | None = None,
) -> MinimumBitAudit:
    """Find the smallest packet-bit subsets that classify this exact corpus."""
    rows = assembled_local_support_corpus() if corpus is None else tuple(corpus)
    if not rows:
        raise ValueError("the minimum-bit audit needs at least one row")
    for count in range(6):
        sufficient: list[tuple[int, ...]] = []
        for mask in combinations(range(5), count):
            outcomes: dict[tuple[int, ...], bool] = {}
            for row in rows:
                key = tuple(row.five_bits[index] for index in mask)
                prior = outcomes.setdefault(key, row.all_pass)
                if prior != row.all_pass:
                    break
            else:
                sufficient.append(mask)
        if sufficient:
            break
    else:
        raise AssertionError("the complete five-bit packet must classify its own corpus")

    dense_rows = tuple((row, dense_folded_square_differential(row)) for row in rows)
    power_moduli: list[tuple[int, int]] = []
    minimum_power_bits = -1
    # This is the actual arithmetic question: which smaller 2-power residue
    # pair still makes simultaneous vanishing equivalent to local all-pass?
    for total in range(12):
        for r1_bits in range(total + 1):
            r2_bits = total - r1_bits
            if all(
                (
                    dense.dense_r1 % (1 << r1_bits) == 0
                    and dense.dense_r2 % (1 << r2_bits) == 0
                )
                == row.all_pass
                for row, dense in dense_rows
            ):
                power_moduli.append((r1_bits, r2_bits))
        if power_moduli:
            minimum_power_bits = total
            break
    if minimum_power_bits < 0:
        raise AssertionError("no bounded power-of-two support observer found")
    return MinimumBitAudit(
        len(rows),
        count,
        tuple(sufficient),
        minimum_power_bits,
        tuple(power_moduli),
    )


def packet_collisions(family: str, parameter: int) -> tuple[PacketCollision, ...]:
    sheet = next(
        row
        for row in supplied_factor_sheets()
        if row.family == family and row.parameter == int(parameter)
    )
    seen: dict[tuple[int, int], OrientationPacketRow] = {}
    collisions: list[PacketCollision] = []
    for row in orientation_sheet(sheet):
        key = row.projection.packet.canonical_key
        prior = seen.setdefault(key, row)
        if prior.orientations != row.orientations:
            left = dense_folded_square_differential(prior)
            right = dense_folded_square_differential(row)
            collisions.append(
                PacketCollision(
                    family,
                    int(parameter),
                    row.projection.packet,
                    prior.orientations,
                    row.orientations,
                    (left.dense_r1, left.dense_r2),
                    (right.dense_r1, right.dense_r2),
                )
            )
    return tuple(collisions)


def temporal_first_hole_audit(family: str, parameter: int) -> TemporalFirstHoleAudit:
    """Evaluate the bounded factor-truth sheet through its first failed level."""
    truth = ambient_capacity_truth(family, int(parameter))
    sheet = next(
        row
        for row in supplied_factor_sheets()
        if row.family == family and row.parameter == int(parameter)
    )
    if truth.local_factors != sheet.factors:
        raise AssertionError((truth.local_factors, sheet.factors))
    first_hole = truth.minimum_local_depth + 1
    rows = tuple(
        orientation_packet_row(
            sheet,
            tuple(1 if depth >= level else -1 for depth in truth.local_lift_depths),
        )
        for level in range(1, first_hole + 1)
    )
    return TemporalFirstHoleAudit(
        family, int(parameter), truth.local_lift_depths, first_hole, rows
    )


def partial_f9_first_hole_audit() -> TemporalFirstHoleAudit:
    """First failure among the two supplied F9 divisors, not all of F9."""
    control = next(
        row
        for row in mixed_capacity_controls()
        if row.family == "fermat" and row.parameter == 9
    )
    sheet = partial_f9_sheet()
    first_hole = min(control.local_lift_depths) + 1
    rows = tuple(
        orientation_packet_row(
            sheet,
            tuple(
                1 if depth >= level else -1
                for depth in control.local_lift_depths
            ),
        )
        for level in range(1, first_hole + 1)
    )
    return TemporalFirstHoleAudit(
        "fermat", 9, control.local_lift_depths, first_hole, rows
    )


def projection_cost_audits() -> tuple[ProjectionCostAudit, ...]:
    """Worst demanded-observer work on each supplied sheet."""
    audits: list[ProjectionCostAudit] = []
    for sheet in supplied_factor_sheets() + (partial_f9_sheet(),):
        rows = orientation_sheet(sheet)
        audits.append(
            ProjectionCostAudit(
                sheet.family,
                sheet.parameter,
                len(rows),
                max(row.projection.coefficient_reads for row in rows),
                max(row.projection.pair_visits for row in rows),
                max(row.projection.scalar_products for row in rows),
            )
        )
    return tuple(audits)


def unrestricted_m53_counterexample() -> UnrestrictedSheetCounterexample:
    """A zero-packet M53 orientation outside the temporal truth patterns.

    This refutes extending the bounded 64-row local-sheet observation to every
    CRT orientation.  The orientation ``(+,+,-)`` is not generated by a common
    lift threshold for local depths ``(1,0,0)``, so it is not a counterexample
    to the tested temporal first-hole rows.
    """
    factors = (6361, 69431, 20394401)
    modulus = mersenne_number(53)
    if prod(factors) != modulus:
        raise AssertionError((factors, modulus))
    sheet = SuppliedFactorSheet(
        "mersenne",
        53,
        modulus,
        factors,
        1,
        53,
        True,
        "supplied-adversarial-complete-factor-truth",
    )
    row = orientation_packet_row(sheet, (1, 1, -1))
    common = gcd(row.defect, modulus)
    if not 1 < common < modulus:
        raise AssertionError((row.defect, modulus, common))
    depths = tuple(
        max(0, v2_positive(factor - jacobi_symbol(12, factor)) - 2)
        for factor in factors
    )
    return UnrestrictedSheetCounterexample(row, depths, common)


def incomplete_factor_evidence() -> tuple[EvidenceBoundary, ...]:
    """Expose supplied divisor-only controls without treating them as sheets."""
    rows: list[EvidenceBoundary] = []
    for control in mixed_capacity_controls():
        if control.family == "fermat" and control.parameter == 9:
            rows.append(
                EvidenceBoundary(
                    control.family,
                    control.parameter,
                    control.supplied_factors,
                    control.factor_witnesses_valid,
                )
            )
    return tuple(rows)


__all__ = [
    "DenseDifferential",
    "EvidenceBoundary",
    "MinimumBitAudit",
    "OrientationPacketRow",
    "PacketCollision",
    "ProjectionCostAudit",
    "SuppliedFactorSheet",
    "TemporalFirstHoleAudit",
    "UnrestrictedSheetCounterexample",
    "assembled_factor_truth_corpus",
    "assembled_local_support_corpus",
    "dense_folded_square_differential",
    "incomplete_factor_evidence",
    "minimum_bit_audit",
    "orientation_packet_row",
    "orientation_sheet",
    "packet_collisions",
    "partial_f9_first_hole_audit",
    "partial_f9_sheet",
    "projection_cost_audits",
    "supplied_factor_sheets",
    "temporal_first_hole_audit",
    "unrestricted_m53_counterexample",
]
