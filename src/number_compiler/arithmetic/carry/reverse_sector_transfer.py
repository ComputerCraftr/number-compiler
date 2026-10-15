"""Bounded carry-domain projections for one reverse/add spatial interval.

The record is a spatial monoid summary.  It retains the Boolean carry action
and fixed cyclotomic residues of the carry boundaries for both possible input
carries.  It contains no digit word, carry row, source identity, or temporal
history.  The forcing observation is derived from the normalization equations
only after the interval carry action determines its growth bit.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Final

from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    apply_carry_fn,
    compose_carry_fn,
    value_carry_fn,
)

_MODULUS = 32
_CLASSES = (1, 2, 4, 8)
_MAX_BASE = 1 << 31
REVERSE_CARRY_SECTOR_TRANSFER_TAG: Final[str] = "reverse-carry-sector-transfer-v1"
_TRANSFER_ISSUER = object()


def _residue_add(
    left: tuple[int, ...],
    right: tuple[int, ...],
) -> tuple[int, ...]:
    if len(left) != len(right):
        raise ValueError("sector residues have different arity")
    return tuple((a + b) % _MODULUS for a, b in zip(left, right, strict=True))


def _shift_residue(values: tuple[int, ...], offset: int) -> tuple[int, ...]:
    """Multiply by ``z**offset`` modulo ``(z**m+1, 32)``."""
    if type(offset) is not int or offset < 0:
        raise ValueError("sector shift requires a nonnegative exact integer")
    classes = len(values)
    out = [0] * classes
    for index, value in enumerate(values):
        quotient, target = divmod(index + offset, classes)
        sign = -1 if quotient & 1 else 1
        out[target] = (out[target] + sign * value) % _MODULUS
    return tuple(out)


def _reflect_residue(
    values: tuple[int, ...],
    degree: int,
) -> tuple[int, ...]:
    """Return ``z**degree f(z**-1)`` in the same bounded sector."""
    if type(degree) is not int or degree < 0:
        raise ValueError("sector reflection requires a nonnegative degree")
    classes = len(values)
    out = [0] * classes
    for index, value in enumerate(values):
        exponent = degree - index
        quotient, target = divmod(exponent, classes)
        sign = -1 if quotient & 1 else 1
        out[target] = (out[target] + sign * value) % _MODULUS
    return tuple(out)


@dataclass(frozen=True, slots=True)
class SectorCarrySums:
    """Projected source and carry sums for both possible input bits."""

    classes: int
    symbols: tuple[int, ...]
    before: tuple[tuple[int, ...], tuple[int, ...]]
    after: tuple[tuple[int, ...], tuple[int, ...]]

    def __post_init__(self) -> None:
        if type(self.classes) is not int or self.classes not in _CLASSES:
            raise ValueError("reverse carry sector must have 1, 2, 4, or 8 classes")
        if (
            type(self.symbols) is not tuple
            or len(self.symbols) != self.classes
            or any(type(value) is not int for value in self.symbols)
            or any(not 0 <= value < _MODULUS for value in self.symbols)
        ):
            raise ValueError("sector source residue is not canonical modulo 32")
        for rows in (self.before, self.after):
            if type(rows) is not tuple or len(rows) != 2:
                raise TypeError("sector carries require two immutable input rows")
            for row in rows:
                if (
                    type(row) is not tuple
                    or len(row) != self.classes
                    or any(type(value) is not int for value in row)
                    or any(not 0 <= value < _MODULUS for value in row)
                ):
                    raise ValueError("sector carry row is not canonical modulo 32")


@dataclass(frozen=True, slots=True)
class SectorForcingResidue:
    """Source transport, forcing, and exact successor sector residue."""

    classes: int
    source: tuple[int, ...]
    linear: tuple[int, ...]
    forward: tuple[int, ...]
    reflected: tuple[int, ...]
    full: tuple[int, ...]
    output: tuple[int, ...]

    def __post_init__(self) -> None:
        if type(self.classes) is not int or self.classes not in _CLASSES:
            raise ValueError("reverse forcing has an unsupported sector")
        for residue in (
            self.source,
            self.linear,
            self.forward,
            self.reflected,
            self.full,
            self.output,
        ):
            if (
                type(residue) is not tuple
                or len(residue) != self.classes
                or any(type(value) is not int for value in residue)
                or any(not 0 <= value < _MODULUS for value in residue)
            ):
                raise ValueError("reverse forcing residue is not canonical")
        if self.full != _residue_add(self.forward, self.reflected):
            raise ValueError("full forcing differs from its directional components")
        if self.output != _residue_add(self.linear, self.full):
            raise ValueError("successor residue differs from transport plus forcing")


@dataclass(frozen=True, slots=True)
class ReverseForcingResidues:
    """One growth observation and all fixed bounded forcing sectors."""

    incoming: int
    growth: int
    sectors: tuple[SectorForcingResidue, ...]

    def __post_init__(self) -> None:
        if type(self.incoming) is not int or self.incoming not in (0, 1):
            raise ValueError("reverse forcing input must be a carry bit")
        if type(self.growth) is not int or self.growth not in (0, 1):
            raise ValueError("reverse forcing growth must be a carry bit")
        if type(self.sectors) is not tuple or any(
            type(sector) is not SectorForcingResidue for sector in self.sectors
        ):
            raise TypeError("reverse forcing requires canonical sector records")
        if tuple(sector.classes for sector in self.sectors) != _CLASSES:
            raise ValueError("reverse forcing requires the four fixed sectors")


@dataclass(frozen=True, slots=True, init=False)
class ReverseCarrySectorTransfer:
    """Closed two-input carry transfer with fixed mod-32 sector projections."""

    base: int
    width: int
    active_width: int
    carry: CarryFn
    sectors: tuple[SectorCarrySums, ...]
    _issuer: object = field(repr=False, compare=False, hash=False)

    @classmethod
    def _issued(
        cls,
        base: int,
        width: int,
        active_width: int,
        carry: CarryFn,
        sectors: tuple[SectorCarrySums, ...],
    ) -> ReverseCarrySectorTransfer:
        result = object.__new__(cls)
        for name, value in (
            ("base", base),
            ("width", width),
            ("active_width", active_width),
            ("carry", carry),
            ("sectors", sectors),
            ("_issuer", _TRANSFER_ISSUER),
        ):
            object.__setattr__(result, name, value)
        result.__post_init__()
        return result

    def __post_init__(self) -> None:
        if getattr(self, "_issuer", None) is not _TRANSFER_ISSUER:
            raise TypeError(
                "reverse carry transfers require a verified leaf or composition"
            )
        if type(self.base) is not int or not 2 <= self.base <= _MAX_BASE:
            raise ValueError("reverse carry transfer requires an exact radix")
        if type(self.width) is not int or self.width < 1:
            raise ValueError("reverse carry transfer requires positive exact width")
        if (
            type(self.active_width) is not int
            or not 0 <= self.active_width <= self.width
        ):
            raise ValueError("reverse carry transfer has invalid active extent")
        if type(self.carry) is not CarryFn:
            raise TypeError("reverse carry transfer requires a CarryFn")
        if type(self.sectors) is not tuple or any(
            type(sector) is not SectorCarrySums for sector in self.sectors
        ):
            raise TypeError("reverse carry transfer requires canonical sectors")
        if tuple(sector.classes for sector in self.sectors) != _CLASSES:
            raise ValueError("reverse carry transfer requires the four fixed sectors")
        if not self.active_width and (
            self.carry is not CarryFn.ID
            or any(
                any(sector.symbols)
                or any(
                    value
                    for rows in (sector.before, sector.after)
                    for row in rows
                    for value in row
                )
                for sector in self.sectors
            )
        ):
            raise ValueError("blank-only carry transfer must be algebraically neutral")
        for incoming in (0, 1):
            outgoing = apply_carry_fn(self.carry, incoming)
            # Evaluation at z=1 modulo two recovers carry-count parity and
            # catches forged leaf/parent exits without retaining a carry word.
            for sector in self.sectors:
                if sector.classes == 1:
                    if (
                        sector.before[incoming][0] % 2
                        != incoming * self.active_width % 2
                        and self.active_width == self.width == 1
                    ):
                        # The z=-1 sector does not expose ordinary parity for a
                        # parent, so only its leaf boundary values are checked.
                        raise ValueError("leaf incoming carry projection is forged")
                    if (
                        self.active_width == self.width == 1
                        and sector.after[incoming][0] != outgoing
                    ):
                        raise ValueError("leaf outgoing carry projection is forged")

    @classmethod
    def leaf(cls, base: int, symbol: int) -> ReverseCarrySectorTransfer:
        """Create one cell, deriving its LT/EQ/GT action from its pair symbol."""
        if type(base) is not int or not 2 <= base <= _MAX_BASE:
            raise ValueError("reverse carry leaf requires an exact radix")
        if type(symbol) is not int:
            raise TypeError("reverse carry leaf requires an exact pair symbol")
        blank = 2 * base - 1
        if not 0 <= symbol <= blank:
            raise ValueError("reverse carry leaf symbol lies outside its alphabet")
        active = symbol != blank
        carry = value_carry_fn(symbol, base) if active else CarryFn.ID
        before_rows: tuple[tuple[int, ...], tuple[int, ...]] = (
            (0,),
            ((1 if active else 0),),
        )
        after_rows: tuple[tuple[int, ...], tuple[int, ...]] = (
            ((apply_carry_fn(carry, 0) if active else 0),),
            ((apply_carry_fn(carry, 1) if active else 0),),
        )
        sectors = tuple(
            SectorCarrySums(
                classes,
                ((symbol % _MODULUS) if active else 0,) + (0,) * (classes - 1),
                (
                    before_rows[0] + (0,) * (classes - 1),
                    before_rows[1] + (0,) * (classes - 1),
                ),
                (
                    after_rows[0] + (0,) * (classes - 1),
                    after_rows[1] + (0,) * (classes - 1),
                ),
            )
            for classes in _CLASSES
        )
        return cls._issued(base, 1, int(active), carry, sectors)

    def then(
        self,
        right: ReverseCarrySectorTransfer,
    ) -> ReverseCarrySectorTransfer:
        """Concatenate ``right`` after ``self`` in physical carry order."""
        self.__post_init__()
        if type(right) is not ReverseCarrySectorTransfer:
            raise TypeError("carry transfer composition requires another transfer")
        right.__post_init__()
        if self.base != right.base:
            raise ValueError("carry transfers use different radices")
        if self.active_width < self.width and right.active_width:
            raise ValueError("reverse source activity must be one contiguous prefix")
        sectors: list[SectorCarrySums] = []
        midpoints = (
            apply_carry_fn(self.carry, 0),
            apply_carry_fn(self.carry, 1),
        )
        for left_sector, right_sector in zip(self.sectors, right.sectors, strict=True):
            before: list[tuple[int, ...]] = []
            after: list[tuple[int, ...]] = []
            for incoming in (0, 1):
                midpoint = midpoints[incoming]
                before.append(
                    _residue_add(
                        left_sector.before[incoming],
                        _shift_residue(
                            right_sector.before[midpoint], self.active_width
                        ),
                    )
                )
                after.append(
                    _residue_add(
                        left_sector.after[incoming],
                        _shift_residue(right_sector.after[midpoint], self.active_width),
                    )
                )
            sectors.append(
                SectorCarrySums(
                    left_sector.classes,
                    _residue_add(
                        left_sector.symbols,
                        _shift_residue(right_sector.symbols, self.active_width),
                    ),
                    (before[0], before[1]),
                    (after[0], after[1]),
                )
            )
        return ReverseCarrySectorTransfer._issued(
            self.base,
            self.width + right.width,
            self.active_width + right.active_width,
            compose_carry_fn(right.carry, self.carry),
            tuple(sectors),
        )

    def forcing(self, incoming: int = 0) -> ReverseForcingResidues:
        """Project one whole symmetric pair field's normalization forcing.

        This observation is valid for the complete contiguous active pair
        field, after trailing tile padding has been ignored.  It is not a
        normalization law for an arbitrary nonsymmetric subinterval.  The
        incoming-one case is the algebraic boundary extension of the endpoint
        formulas; ordinary reverse/add begins with incoming zero.
        """
        self.__post_init__()
        if type(incoming) is not int or incoming not in (0, 1):
            raise ValueError("forcing observation requires a carry bit")
        if not self.active_width:
            raise ValueError("blank-only tiles have no reverse forcing field")
        growth = apply_carry_fn(self.carry, incoming)
        degree = self.active_width if growth else self.active_width - 1
        outputs: list[SectorForcingResidue] = []
        for sector in self.sectors:
            forward = tuple(
                (before - self.base * after) % _MODULUS
                for before, after in zip(
                    sector.before[incoming],
                    sector.after[incoming],
                    strict=True,
                )
            )
            if growth:
                forward = (
                    (forward[0] + 1 - incoming) % _MODULUS,
                    *forward[1:],
                )
            reflected = _reflect_residue(forward, degree)
            linear = (
                _residue_add(sector.symbols, _shift_residue(sector.symbols, 1))
                if growth
                else tuple(2 * value % _MODULUS for value in sector.symbols)
            )
            full = _residue_add(forward, reflected)
            outputs.append(
                SectorForcingResidue(
                    sector.classes,
                    sector.symbols,
                    linear,
                    forward,
                    reflected,
                    full,
                    _residue_add(linear, full),
                )
            )
        return ReverseForcingResidues(incoming, growth, tuple(outputs))

    def interval_forcing(
        self,
        reflected: ReverseCarrySectorTransfer,
        *,
        incoming: int,
        reflected_incoming: int,
        growth: int,
        predecessor: ReverseCarrySectorTransfer | None = None,
    ) -> ReverseForcingResidues:
        """Project one geometry-aligned local successor interval.

        ``self`` supplies the source coefficients and the forward carry
        differences for the requested output interval. ``reflected`` is an
        equal-width physical carry interval whose reversed differences are the
        other normalization input.  In the growth branch it must already be
        shifted one source cell by the scheduler's halo geometry, and
        ``predecessor`` supplies the equally aligned ``S[i-1]`` coefficients.

        The method deliberately does not infer symmetry, endpoints, or halo
        positions.  A consumer profile must establish those geometric facts
        before selecting these bounded operands.  In particular, an interval
        containing either special growth endpoint is not represented by this
        interior law.
        """
        self.__post_init__()
        if type(reflected) is not ReverseCarrySectorTransfer:
            raise TypeError("local reverse forcing requires a reflected transfer")
        reflected.__post_init__()
        for name, value in (
            ("incoming", incoming),
            ("reflected incoming", reflected_incoming),
            ("growth", growth),
        ):
            if type(value) is not int or value not in (0, 1):
                raise ValueError(f"local reverse forcing {name} requires a carry bit")
        if (
            self.base != reflected.base
            or self.width != reflected.width
            or self.active_width != self.width
            or reflected.active_width != reflected.width
        ):
            raise ValueError(
                "local reverse forcing requires equal fully active aligned intervals"
            )
        if growth:
            if type(predecessor) is not ReverseCarrySectorTransfer:
                raise ValueError(
                    "growth forcing requires an aligned predecessor interval"
                )
            predecessor.__post_init__()
            if (
                predecessor.base != self.base
                or predecessor.width != self.width
                or predecessor.active_width != predecessor.width
            ):
                raise ValueError(
                    "growth predecessor must be one fully active aligned interval"
                )
        elif predecessor is not None:
            raise ValueError("no-growth forcing cannot consume a predecessor interval")

        outputs: list[SectorForcingResidue] = []
        predecessor_sectors = None if predecessor is None else predecessor.sectors
        for index, (source, partner) in enumerate(
            zip(self.sectors, reflected.sectors, strict=True)
        ):
            forward = tuple(
                (before - self.base * after) % _MODULUS
                for before, after in zip(
                    source.before[incoming],
                    source.after[incoming],
                    strict=True,
                )
            )
            partner_forward = tuple(
                (before - self.base * after) % _MODULUS
                for before, after in zip(
                    partner.before[reflected_incoming],
                    partner.after[reflected_incoming],
                    strict=True,
                )
            )
            reflected_term = _reflect_residue(partner_forward, self.width - 1)
            if predecessor_sectors is None:
                linear = tuple(2 * value % _MODULUS for value in source.symbols)
            else:
                linear = _residue_add(
                    source.symbols,
                    predecessor_sectors[index].symbols,
                )
            full = _residue_add(forward, reflected_term)
            outputs.append(
                SectorForcingResidue(
                    source.classes,
                    source.symbols,
                    linear,
                    forward,
                    reflected_term,
                    full,
                    _residue_add(linear, full),
                )
            )
        return ReverseForcingResidues(incoming, growth, tuple(outputs))

    @staticmethod
    def retained_slots() -> int:
        """Return fixed inline arithmetic slots: one function and 75 limbs."""
        return 1 + 5 * sum(_CLASSES)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            REVERSE_CARRY_SECTOR_TRANSFER_TAG,
            self.base,
            self.width,
            self.active_width,
            self.carry,
            self.sectors,
        )


__all__ = [
    "ReverseCarrySectorTransfer",
    "ReverseForcingResidues",
    "SectorCarrySums",
    "SectorForcingResidue",
]
