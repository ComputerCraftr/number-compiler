"""Bounded radix-64 mirror refinement of the five-bit support experiment.

The 72 rows here are supplied factor truth: 60 complete orientation-sheet rows,
four rows over the two known F9 divisors, and all eight orientations of the
supplied complete M53 factorization.  The F9 sheet remains local evidence only.
The M53 orientations include states that no common temporal depth produces.
Consequently this module audits an arithmetic observer; it is not a
candidate-derived support or primality classifier.
"""

from __future__ import annotations

from dataclasses import dataclass

from devtools.experiments.algebra.dyadic_difference_germ_core import (
    ambient_capacity_truth,
    mixed_capacity_controls,
)
from devtools.experiments.power_numbers.five_bit_support import (
    OrientationPacketRow,
    SuppliedFactorSheet,
    assembled_local_support_corpus,
    orientation_packet_row,
    orientation_sheet,
    partial_f9_sheet,
    supplied_factor_sheets,
    unrestricted_m53_counterexample,
)
from number_compiler.arithmetic.polynomials.digit_convolution import (
    adaptive_square_convolution,
    fold_cyclic,
    fold_negacyclic,
)
from number_compiler.arithmetic.polynomials.radix64_mirror import (
    FoldedFifthProjection,
    folded_fifth_residue,
)


@dataclass(frozen=True, slots=True)
class MirrorRefinementRow:
    source: OrientationPacketRow
    fifth: FoldedFifthProjection
    dense_fifth: int

    @property
    def exact(self) -> bool:
        return self.fifth.residue == self.dense_fifth % 16

    @property
    def refined_vanishes(self) -> bool:
        return self.fifth.vanishes


@dataclass(frozen=True, slots=True)
class RefinedClassCount:
    family: str
    parameter: int
    sheet_rows: int
    fifth_residue_classes: int


@dataclass(frozen=True, slots=True)
class RefinementCorpusAudit:
    rows: tuple[MirrorRefinementRow, ...]
    legacy_false_positives: int
    legacy_false_negatives: int
    refined_false_positives: int
    refined_false_negatives: int
    fifth_residue_classes: int
    class_counts: tuple[RefinedClassCount, ...]


@dataclass(frozen=True, slots=True)
class SingleCoefficientWitness:
    position: int
    modulus_bits: int


@dataclass(frozen=True, slots=True)
class SingleCoefficientSearchAudit:
    position_start: int
    position_stop: int
    modulus_bits_start: int
    modulus_bits_stop: int
    search_order: str
    minimum_modulus_bits: int
    minimum_witnesses: tuple[SingleCoefficientWitness, ...]
    all_witnesses: tuple[SingleCoefficientWitness, ...]


@dataclass(frozen=True, slots=True)
class TemporalMirrorAudit:
    family: str
    parameter: int
    local_depths: tuple[int, ...]
    last_level: int
    partial_factor_sheet: bool
    rows: tuple[MirrorRefinementRow, ...]


def refinement_source_rows() -> tuple[OrientationPacketRow, ...]:
    """Return the exact 60 + 4 + 8 bounded orientation rows."""
    m53_sheet = unrestricted_m53_counterexample().row.sheet
    return assembled_local_support_corpus() + orientation_sheet(m53_sheet)


def _dense_folded_field(row: OrientationPacketRow) -> tuple[int, ...]:
    full, _metrics = adaptive_square_convolution(row.coefficients)
    fold = fold_cyclic if row.sheet.sign == 1 else fold_negacyclic
    return fold(full, len(row.coefficients))


def _dense_folded_coefficient(row: OrientationPacketRow, position: int) -> int:
    return _dense_folded_field(row)[int(position)]


def mirror_refinement_row(row: OrientationPacketRow) -> MirrorRefinementRow:
    fifth = folded_fifth_residue(row.coefficients, sign=row.sheet.sign)
    return MirrorRefinementRow(row, fifth, _dense_folded_coefficient(row, 5))


def refinement_corpus() -> tuple[MirrorRefinementRow, ...]:
    return tuple(mirror_refinement_row(row) for row in refinement_source_rows())


def refinement_corpus_audit() -> RefinementCorpusAudit:
    rows = refinement_corpus()
    legacy_false_positives = sum(
        row.source.projection.vanishes and not row.source.all_pass for row in rows
    )
    legacy_false_negatives = sum(
        not row.source.projection.vanishes and row.source.all_pass for row in rows
    )
    refined_false_positives = sum(
        row.refined_vanishes and not row.source.all_pass for row in rows
    )
    refined_false_negatives = sum(
        not row.refined_vanishes and row.source.all_pass for row in rows
    )
    groups: dict[tuple[str, int], list[MirrorRefinementRow]] = {}
    for row in rows:
        key = row.source.sheet.family, row.source.sheet.parameter
        groups.setdefault(key, []).append(row)
    counts = tuple(
        RefinedClassCount(
            family,
            parameter,
            len(group),
            len({row.fifth.residue for row in group}),
        )
        for (family, parameter), group in sorted(groups.items())
    )
    return RefinementCorpusAudit(
        rows,
        legacy_false_positives,
        legacy_false_negatives,
        refined_false_positives,
        refined_false_negatives,
        len({row.fifth.residue for row in rows}),
        counts,
    )


def single_coefficient_search(
    *,
    position_start: int = 0,
    position_stop: int = 10,
    modulus_bits_start: int = 1,
    modulus_bits_stop: int = 12,
) -> SingleCoefficientSearchAudit:
    """Search one folded coefficient, ordered by bits and then position.

    Both bounds are inclusive.  A witness must have residue zero exactly on
    the all-``+1`` row of every supplied sheet.  It is tested independently;
    the legacy five-bit packet is not silently conjoined with it.
    """
    bounds = (
        int(position_start),
        int(position_stop),
        int(modulus_bits_start),
        int(modulus_bits_stop),
    )
    if bounds[0] < 0 or bounds[1] < bounds[0] or bounds[2] < 1 or bounds[3] < bounds[2]:
        raise ValueError(bounds)
    source = refinement_source_rows()
    if bounds[1] >= min(len(row.coefficients) for row in source):
        raise ValueError("the coefficient search exceeds the smallest sheet width")
    dense = tuple(
        (
            row,
            _dense_folded_field(row)[bounds[0] : bounds[1] + 1],
        )
        for row in source
    )
    witnesses: list[SingleCoefficientWitness] = []
    minimum = -1
    minimum_witnesses: list[SingleCoefficientWitness] = []
    for bits in range(bounds[2], bounds[3] + 1):
        modulus = 1 << bits
        for position in range(bounds[0], bounds[1] + 1):
            offset = position - bounds[0]
            if all(
                (coefficients[offset] % modulus == 0) == row.all_pass
                for row, coefficients in dense
            ):
                witness = SingleCoefficientWitness(position, bits)
                witnesses.append(witness)
                if minimum < 0:
                    minimum = bits
                if bits == minimum:
                    minimum_witnesses.append(witness)
    if minimum < 0:
        raise AssertionError("no witness occurs inside the declared search bounds")
    return SingleCoefficientSearchAudit(
        bounds[0],
        bounds[1],
        bounds[2],
        bounds[3],
        "modulus-bits-then-coefficient-position",
        minimum,
        tuple(minimum_witnesses),
        tuple(witnesses),
    )


def _complete_sheet(family: str, parameter: int) -> SuppliedFactorSheet:
    return next(
        sheet
        for sheet in supplied_factor_sheets()
        if sheet.family == family and sheet.parameter == parameter
    )


def temporal_mirror_audit(family: str, parameter: int) -> TemporalMirrorAudit:
    """Follow common-depth orientations beyond the first bounded hole."""
    family, parameter = str(family), int(parameter)
    partial = family == "fermat" and parameter == 9
    if partial:
        control = next(
            row
            for row in mixed_capacity_controls()
            if row.family == family and row.parameter == parameter
        )
        depths = control.local_lift_depths
        sheet = partial_f9_sheet()
        last_level = max(depths) + 3
    else:
        truth = ambient_capacity_truth(family, parameter)
        depths = truth.local_lift_depths
        sheet = _complete_sheet(family, parameter)
        if truth.local_factors != sheet.factors:
            raise AssertionError((truth.local_factors, sheet.factors))
        last_level = (
            max(depths) + 3
            if family == "mersenne" and parameter == 29
            else min(depths) + 3
        )
    rows = tuple(
        mirror_refinement_row(
            orientation_packet_row(
                sheet,
                tuple(1 if depth >= level else -1 for depth in depths),
            )
        )
        for level in range(1, last_level + 1)
    )
    return TemporalMirrorAudit(
        family, parameter, depths, last_level, partial, rows
    )


__all__ = [
    "MirrorRefinementRow",
    "RefinedClassCount",
    "RefinementCorpusAudit",
    "SingleCoefficientSearchAudit",
    "SingleCoefficientWitness",
    "TemporalMirrorAudit",
    "mirror_refinement_row",
    "refinement_corpus",
    "refinement_corpus_audit",
    "refinement_source_rows",
    "single_coefficient_search",
    "temporal_mirror_audit",
]
