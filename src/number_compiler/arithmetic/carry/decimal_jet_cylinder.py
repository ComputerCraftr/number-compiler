"""Decimal carry/forcing views of one two-port primary-jet cylinder.

Only the spatial occurrence retains width. Carries, signed reset and the
physical reverse/add forcing jet are views of the same occupancy emission.
This finite observation intentionally does not own exact value successors.
"""

from __future__ import annotations

from collections.abc import Iterable
from dataclasses import dataclass

from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    apply_carry_fn,
    carry_fn_from_outputs,
    value_carry_fn,
)
from number_compiler.arithmetic.carry.jet_cylinder import JetPortCylinder, JetPortRow
from number_compiler.arithmetic.contracts.exact_tree_context import (
    require_endpoint_construction,
)
from number_compiler.arithmetic.polynomials.primary_jet import (
    PrimaryJetBlock,
    _poly_add,
    _poly_mul,
    _poly_scale,
)

ZERO = (0,) * 5
ONE = (1, 0, 0, 0, 0)
INVERSE_Z = (31,) * 5
# Exact order 128 in (Z/32)[y]/y^5: fixed algebra, not occurrence-cache state.
_CLOCK_POWERS = tuple(
    PrimaryJetBlock.digit(0, degree=5, modulus=32).power_block(phase).power
    for phase in range(128)
)


def _reflected(jet: tuple[int, ...], clock: tuple[int, ...]) -> tuple[int, ...]:
    """Evaluate ``z^L P(z^-1)`` within the existing primary algebra."""
    substitution = _poly_add(INVERSE_Z, ONE, 32)
    result: tuple[int, ...] = ZERO
    for coefficient in reversed(jet):
        result = _poly_add(
            _poly_mul(result, substitution, 32),
            (coefficient, 0, 0, 0, 0),
            32,
        )
    return _poly_mul(clock, result, 32)


@dataclass(frozen=True, slots=True)
class DecimalCarryJetBlock:
    width: int
    cylinder: JetPortCylinder

    def __post_init__(self) -> None:
        require_endpoint_construction()
        if type(self.width) is not int or self.width < 0:
            raise ValueError("carry-jet occurrence width must be nonnegative and exact")
        if type(self.cylinder) is not JetPortCylinder or (
            self.cylinder.modulus,
            self.cylinder.degree,
            len(self.cylinder.rows),
        ) != (32, 5, 2):
            raise ValueError(
                "decimal carry cylinder needs two five-component mod32 rows"
            )
        if self.cylinder.outputs not in ((0, 0), (0, 1), (1, 1)):
            raise ValueError("decimal carry cylinder must be monotone")

    @property
    def clock(self) -> tuple[int, ...]:
        return _CLOCK_POWERS[self.width % 128]

    @property
    def domain(self) -> CarryFn:
        return carry_fn_from_outputs(self.cylinder.outputs)

    @classmethod
    def identity(cls) -> DecimalCarryJetBlock:
        return cls(0, JetPortCylinder.identity(2))

    @classmethod
    def digit(cls, pair_symbol: int) -> DecimalCarryJetBlock:
        domain = value_carry_fn(pair_symbol, 10)
        return cls(
            1,
            JetPortCylinder(
                32,
                tuple(
                    JetPortRow(apply_carry_fn(domain, c), (c, 0, 0, 0, 0))
                    for c in (0, 1)
                ),
            ),
        )

    def then(self, after: DecimalCarryJetBlock) -> DecimalCarryJetBlock:
        return DecimalCarryJetBlock(
            self.width + after.width, self.cylinder.then(after.cylinder, self.clock)
        )

    @classmethod
    def from_pair(cls, pair: Iterable[int]) -> DecimalCarryJetBlock:
        result = cls.identity()
        for symbol in pair:
            result = result.then(cls.digit(symbol))
        return result

    def following_jet(self, incoming: int) -> tuple[int, ...]:
        """J5(C[i+1]) from J5(C[i]), the input port and exit projection."""
        if type(incoming) is not int or incoming not in (0, 1):
            raise ValueError("decimal cylinder port must be Boolean")
        row = self.cylinder.rows[incoming]
        numerator = _poly_add(row.jet, _poly_scale(ONE, -incoming, 32), 32)
        numerator = _poly_add(numerator, _poly_scale(self.clock, row.outgoing, 32), 32)
        return _poly_mul(INVERSE_Z, numerator, 32)

    def reset_jet(self, incoming: int) -> tuple[int, ...]:
        following = self.following_jet(incoming)
        return _poly_add(
            following, _poly_scale(self.cylinder.rows[incoming].jet, -1, 32), 32
        )

    def normalization_jet(self, incoming: int) -> tuple[int, ...]:
        following = self.following_jet(incoming)
        return _poly_add(
            self.cylinder.rows[incoming].jet, _poly_scale(following, -10, 32), 32
        )

    def forcing_jet(self) -> tuple[int, ...]:
        """Physical incoming-zero E jet; reflection/edge are clock views."""
        if not self.width:
            raise ValueError("reverse/add forcing requires a nonempty occurrence")
        growth = self.cylinder.rows[0].outgoing
        clock = self.clock
        normalization = self.normalization_jet(0)
        reflection_clock = clock if growth else _poly_mul(clock, INVERSE_Z, 32)
        result = _poly_add(
            normalization, _reflected(normalization, reflection_clock), 32
        )
        return _poly_add(result, _poly_add(ONE, clock, 32), 32) if growth else result
