"""Finite source-selected carry rows for the physical Fermat 3X action.

The input is the existing bilateral ``SourceWeightedTriplingAction`` owner.
Rows retain all conditional next digits, while the pointed row is selected by
that owner's exact low cyclotomic source. The record covers only the requested
finite positions and physical ticks; it says nothing about a global carry
period or the Fermat signed-fold predicate.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import fermat as _fermat_keys
from number_compiler.sequences.power_numbers._harmonic_authority import (
    harmonic_verified,
    issue_harmonic,
    new_harmonic_issuer,
)
from number_compiler.sequences.power_numbers.source_matrix import FermatMultiradixPort
from number_compiler.sequences.power_numbers.three_power_signed_border_action import (
    SourceWeightedTriplingAction,
)
from number_compiler.sequences.power_numbers.three_power_two_sided_cylinder import (
    FermatTwoSidedSourceCylinder,
)

MAX_CAUSAL_PHYSICAL_STEPS = 4096
MAX_CAUSAL_DIGIT_POSITION = 256
MAX_CAUSAL_WORK_UNITS = 25_000_000
MAX_CAUSAL_ROW_STORAGE_CELLS = 123_000
_SUPPORTED_BASES = frozenset((2, 5, 7, 10))

if TYPE_CHECKING:
    from number_compiler.sequences.power_numbers.numbers import FermatNumberSpec


@dataclass(frozen=True, slots=True)
class FermatCausalCarryRow:
    """One exact conditional digit row and its ordered carries."""

    base: int
    position: int
    source_digit: int
    source_residue: int
    physical_steps: int
    digits: tuple[int, ...]
    carries_in: tuple[int, ...]
    carries_out: tuple[int, ...]
    endpoint_residue: int

    def __post_init__(self) -> None:
        if (
            type(self.base) is not int
            or self.base not in _SUPPORTED_BASES
            or type(self.position) is not int
            or not 0 <= self.position <= MAX_CAUSAL_DIGIT_POSITION
            or type(self.source_digit) is not int
            or not 0 <= self.source_digit < self.base
            or type(self.physical_steps) is not int
            or not 1 <= self.physical_steps <= MAX_CAUSAL_PHYSICAL_STEPS
            or type(self.source_residue) is not int
            or type(self.endpoint_residue) is not int
            or len(self.digits) != self.physical_steps + 1
            or len(self.carries_in) != self.physical_steps
            or len(self.carries_out) != self.physical_steps
        ):
            raise ValueError("malformed finite Fermat causal carry row")
        modulus = self.base ** (self.position + 1)
        if (
            not 0 <= self.source_residue < modulus
            or not 0 <= self.endpoint_residue < modulus
        ):
            raise ValueError("causal row source lies outside its positional modulus")
        if self.digits[0] != self.source_digit:
            raise ValueError(
                "conditional row does not start at its selected source digit"
            )
        for tick, (before, after, carry_in, carry_out) in enumerate(
            zip(
                self.digits[:-1],
                self.digits[1:],
                self.carries_in,
                self.carries_out,
                strict=True,
            )
        ):
            expected = 3 * before + carry_in
            if (
                type(carry_in) is not int
                or type(carry_out) is not int
                or carry_in not in range(3)
                or carry_out not in range(3)
                or after != expected % self.base
                or carry_out != expected // self.base
            ):
                raise ArithmeticError(f"invalid source carry recurrence at tick {tick}")


@dataclass(frozen=True, slots=True, weakref_slot=True)
class FermatCausalBorderMatrix:
    """Source-selected finite carry transfer at one radix position."""

    source: SourceWeightedTriplingAction = field(repr=False)
    cylinder: FermatTwoSidedSourceCylinder = field(repr=False)
    base: int
    position: int
    physical_steps: int
    source_residue: int
    rows: tuple[FermatCausalCarryRow, ...]
    selected_digit: int
    work_units: int
    row_cells: int
    construction_peak_cells: int
    _issuer: object = field(default=None, init=False, repr=False, compare=False)

    def _payload(self) -> tuple[object, ...]:
        return (
            self.source._payload(),
            self.cylinder._payload(),
            self.base,
            self.position,
            self.physical_steps,
            self.source_residue,
            self.rows,
            self.selected_digit,
            self.work_units,
            self.row_cells,
            self.construction_peak_cells,
        )

    @property
    def producer_verified(self) -> bool:
        return (
            self.source.producer_verified
            and self.cylinder.producer_verified
            and self.cylinder.source is self.source
            and harmonic_verified(self, self._payload(), issuer=_MATRIX_ISSUER)
        )

    @property
    def selected_row(self) -> FermatCausalCarryRow:
        if not self.producer_verified:
            raise ValueError("unissued Fermat causal border matrix")
        return self.rows[self.selected_digit]

    def packet(self, *, include_rows: bool = False) -> dict[str, object]:
        if not self.producer_verified:
            raise ValueError("unissued Fermat causal border matrix")
        packet: dict[str, object] = {
            "source_authority": "bilateral Fermat source plus low cyclotomic residue",
            "source_level": self.source.level,
            "radix": self.base,
            "digit_position": self.position,
            "physical_steps": self.physical_steps,
            "source_residue": self.source_residue,
            "selected_source_digit": self.selected_digit,
            "selected_digit_path": self.selected_row.digits,
            "selected_carry_in": self.selected_row.carries_in,
            "selected_carry_out": self.selected_row.carries_out,
            "selected_endpoint_residue": self.selected_row.endpoint_residue,
            "conditional_rows": len(self.rows),
            "source_cylinder_verified": True,
            "complete_signed_fold_certified": False,
            "causal_row_work_units": self.work_units,
            "causal_row_cells": self.row_cells,
            "causal_construction_peak_cells": self.construction_peak_cells,
            "causal_work_budget": MAX_CAUSAL_WORK_UNITS,
        }
        if include_rows:
            packet["rows"] = tuple(
                {
                    "source_digit": row.source_digit,
                    "digits": row.digits,
                    "carry_in": row.carries_in,
                    "carry_out": row.carries_out,
                    "endpoint_residue": row.endpoint_residue,
                }
                for row in self.rows
            )
        return packet


def _exact_source_point(cylinder: FermatTwoSidedSourceCylinder) -> int | None:
    interval = cylinder.exact_interval
    if interval is None:
        return None
    first = interval.lower + (
        (cylinder.combined_residue - interval.lower) % cylinder.combined_modulus
    )
    if first >= interval.upper:
        return None
    if first + cylinder.combined_modulus < interval.upper:
        return None
    return first


def _source_residue(
    source: SourceWeightedTriplingAction,
    cylinder: FermatTwoSidedSourceCylinder,
    base: int,
    places: int,
) -> int:
    modulus = base**places
    raw_level = source.level
    if type(raw_level) is not int or raw_level < 0:
        raise ValueError("issued Fermat source has an invalid level")
    level = int(raw_level)
    residue = int(pow(3, 1 << level, modulus))
    binary = source.origin.binary_phase_bank
    decimal = source.origin.decimal_phase_bank
    if base == 2:
        if binary is not None and binary.depth >= places:
            checked = binary.source_prefix % modulus
        else:
            exact = _exact_source_point(cylinder)
            if exact is None:
                raise ValueError(
                    "binary causal source exceeds the issued low phase depth"
                )
            checked = exact % modulus
        if residue != checked:
            raise ArithmeticError(
                "binary causal source differs from the issued cyclotomic bank"
            )
    elif base in (5, 10):
        check_modulus = 5**places if base == 5 else modulus
        if decimal is not None and decimal.depth >= places:
            checked = decimal.source_prefix % check_modulus
        else:
            exact = _exact_source_point(cylinder)
            if exact is None:
                raise ValueError(
                    "decimal causal source exceeds the issued low phase depth"
                )
            checked = exact % check_modulus
        if residue % check_modulus != checked:
            raise ArithmeticError(
                "radix causal source differs from the issued decimal bank"
            )
    return residue


def _row(
    *,
    base: int,
    position: int,
    source_digit: int,
    lower_residue: int,
    physical_steps: int,
    ledger: ResourceLedger,
) -> FermatCausalCarryRow:
    low_modulus = base**position
    modulus = low_modulus * base
    current = lower_residue + source_digit * low_modulus
    source_residue = current
    digits = [source_digit]
    carries_in: list[int] = []
    carries_out: list[int] = []
    for _ in range(physical_steps):
        incoming = 3 * (current % low_modulus) // low_modulus if position else 0
        digit = current // low_modulus
        outgoing = (3 * digit + incoming) // base
        next_digit = (3 * digit + incoming) % base
        carries_in.append(incoming)
        carries_out.append(outgoing)
        ledger.bump(_fermat_keys.FERMAT_CAUSAL_CARRY_CELL_UPDATES)
        ledger.bump(_fermat_keys.FERMAT_CAUSAL_OPERAND_BITS, modulus.bit_length() * 6)
        current = 3 * current % modulus
        if current // low_modulus != next_digit:
            raise ArithmeticError("causal carry does not match the modular successor")
        digits.append(next_digit)
    return FermatCausalCarryRow(
        base,
        position,
        source_digit,
        source_residue,
        physical_steps,
        tuple(digits),
        tuple(carries_in),
        tuple(carries_out),
        current,
    )


def compile_causal_border_matrix(
    source: SourceWeightedTriplingAction,
    physical_steps: int,
    *,
    base: int = 10,
    position: int = 0,
    multiradix_port: FermatMultiradixPort | None = None,
    max_work_units: int = MAX_CAUSAL_WORK_UNITS,
) -> FermatCausalBorderMatrix:
    """Compile a bounded causal matrix from an existing production source."""
    if type(source) is not SourceWeightedTriplingAction or not source.producer_verified:
        raise TypeError("causal Fermat matrix requires an issued production source")
    if (
        type(physical_steps) is not int
        or not 1 <= physical_steps <= MAX_CAUSAL_PHYSICAL_STEPS
        or type(base) is not int
        or base not in _SUPPORTED_BASES
        or type(position) is not int
        or not 0 <= position <= MAX_CAUSAL_DIGIT_POSITION
        or type(max_work_units) is not int
        or not 1 <= max_work_units <= MAX_CAUSAL_WORK_UNITS
    ):
        raise ValueError("Fermat causal matrix request exceeds its finite dimensions")
    places = position + 1
    row_cells = base * physical_steps
    work_units = row_cells * places
    construction_peak_cells = base * (3 * physical_steps + 1)
    if work_units > max_work_units:
        raise BlockContextBudgetExceeded("Fermat causal row work budget exceeded")
    if construction_peak_cells > MAX_CAUSAL_ROW_STORAGE_CELLS:
        raise BlockContextBudgetExceeded("Fermat causal row storage budget exceeded")
    if base == 7 and (
        type(multiradix_port) is not FermatMultiradixPort
        or not multiradix_port.producer_verified
        or (
            multiradix_port.index,
            multiradix_port.level,
            multiradix_port.base,
            multiradix_port.places,
        )
        != (source.index, source.level, base, position + 1)
    ):
        raise ValueError("7-adic causal matrix requires its production multiradix port")
    cylinder = source.demand_two_sided_source_cylinder()
    if not cylinder.producer_verified:
        raise ValueError("production source did not issue its two-sided cylinder")
    residue = (
        multiradix_port.source_residue
        if base == 7 and multiradix_port is not None
        else _source_residue(source, cylinder, base, places)
    )
    modulus = base**places
    if type(residue) is not int or not 0 <= residue < modulus:
        raise ValueError("admitted Fermat source residue is outside its radix modulus")
    low = residue % (base**position)
    ledger = ResourceLedger(max_nodes=MAX_CAUSAL_ROW_STORAGE_CELLS)
    owner = ledger.register("fermat-causal-row-construction", "execution_stack")
    ledger.bump(_fermat_keys.FERMAT_CAUSAL_CARRY_WORK_UNITS, work_units)
    ledger.bump(_fermat_keys.FERMAT_CAUSAL_ROW_CELLS, row_cells)
    ledger.bump(
        _fermat_keys.FERMAT_CAUSAL_CONSTRUCTION_PEAK_CELLS,
        construction_peak_cells,
    )
    try:
        # This temporary reservation bounds row construction. The immutable
        # returned rows have their own explicit size cap; they are not claimed
        # as a live ResourceLedger-owned allocation after this scope ends.
        with ledger.reservation(owner, nodes=construction_peak_cells):
            rows = tuple(
                _row(
                    base=base,
                    position=position,
                    source_digit=digit,
                    lower_residue=low,
                    physical_steps=physical_steps,
                    ledger=ledger,
                )
                for digit in range(base)
            )
    finally:
        ledger.mark_disposed(owner)
    selected = residue // (base**position)
    if rows[selected].source_residue != residue:
        raise ArithmeticError("source-selected causal row lost the production digit")
    result = FermatCausalBorderMatrix(
        source,
        cylinder,
        base,
        position,
        physical_steps,
        residue,
        rows,
        selected,
        work_units,
        row_cells,
        construction_peak_cells,
    )
    issue_harmonic(result, result._payload(), issuer=_MATRIX_ISSUER)
    if not result.producer_verified:
        raise ArithmeticError("failed to issue causal Fermat matrix")
    return result


def demand_fermat_causal_border_matrix(
    spec: FermatNumberSpec,
    level: int,
    physical_steps: int,
    *,
    base: int = 10,
    position: int = 0,
    max_work_units: int | None = None,
) -> FermatCausalBorderMatrix:
    """Validate a source demand before constructing its admitted owners."""
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )
    from number_compiler.sequences.power_numbers.numbers import FermatNumberSpec

    if type(spec) is not FermatNumberSpec:
        raise TypeError("causal Fermat demand requires FermatNumberSpec")
    if type(spec.index) is not int or not 1 <= spec.index <= 16:
        raise ValueError("Fermat causal source index exceeds its production bound")
    if type(level) is not int or not 1 <= level < (1 << spec.index):
        raise ValueError("Fermat causal source level exceeds its production horizon")
    if (
        type(physical_steps) is not int
        or not 1 <= physical_steps <= MAX_CAUSAL_PHYSICAL_STEPS
    ):
        raise ValueError("Fermat causal physical span exceeds 4096")
    if type(position) is not int or not 0 <= position <= MAX_CAUSAL_DIGIT_POSITION:
        raise ValueError("Fermat causal digit position exceeds 256")
    if type(base) is not int or base not in _SUPPORTED_BASES:
        raise ValueError("unsupported Fermat causal radix")
    if base == 7 and position >= 19:
        raise ValueError("7-adic causal source exceeds its 19-place producer bound")
    if max_work_units is not None and (
        type(max_work_units) is not int or max_work_units < 1
    ):
        raise ValueError("Fermat causal work budget must be a positive exact integer")
    work_budget = MAX_CAUSAL_WORK_UNITS if max_work_units is None else max_work_units
    if work_budget > MAX_CAUSAL_WORK_UNITS:
        raise ValueError("Fermat causal work budget exceeds its hard maximum")
    required_work = base * physical_steps * (position + 1)
    if required_work > work_budget:
        raise BlockContextBudgetExceeded("Fermat causal row work budget exceeded")

    source = spec.demand_three_power_signed_border_action(
        level,
        phase_binary_places=max(64, position + 1 if base == 2 else 64),
        phase_decimal_places=max(6, position + 1 if base in (5, 10) else 6),
        low_binary_places=1,
        low_decimal_places=1,
        high_binary_places=1,
        high_decimal_places=1,
    )
    multiradix_port = (
        spec.demand_three_power_multiradix_port(level, base, position + 1)
        if base == 7
        else None
    )
    return compile_causal_border_matrix(
        source,
        physical_steps,
        base=base,
        position=position,
        multiradix_port=multiradix_port,
        max_work_units=work_budget,
    )


_MATRIX_ISSUER = new_harmonic_issuer(FermatCausalBorderMatrix)


__all__ = [
    "MAX_CAUSAL_DIGIT_POSITION",
    "MAX_CAUSAL_PHYSICAL_STEPS",
    "MAX_CAUSAL_WORK_UNITS",
    "FermatCausalBorderMatrix",
    "FermatCausalCarryRow",
    "compile_causal_border_matrix",
    "demand_fermat_causal_border_matrix",
]
