"""Bounded Fermat/Mersenne projections through the shared arithmetic tile.

The canonical state is the tile's ``CyclotomicDigitBlock``.  Each recurrence
uses the common convolution, quotient-ring reduction, and end-around carry
owners.  The nonlinear iteration count remains explicit because no
successor-congruent temporal square action has been certified for the shared
scheduler.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.fields.radix import bit_width
from number_compiler.arithmetic.polynomials.arithmetic_tile import (
    ArithmeticTile,
    ArithmeticTileSpec,
)
from number_compiler.sequences.power_numbers.numbers import FermatNumberSpec


@dataclass(frozen=True, slots=True)
class DigitPowerProjectionResult:
    family: str
    parameter: int
    modulus_bits: int
    iterations: int
    residue: int
    passes: bool
    karatsuba_scalar_multiplications: int
    naive_scalar_products: int
    coefficient_additions: int
    recursive_nodes: int
    max_boundary_bits: int
    exceptional_minus_one_steps: int
    karatsuba_steps: int = 0
    schoolbook_steps: int = 0
    sign_quotient_steps: int = 0
    sign_quotient_nonzero_digits_saved: int = 0
    arithmetic_tile_steps: int = 0
    legacy_digit_convolution_calls: int = 0
    scheduler_compositions: int = 0

    def __post_init__(self) -> None:
        if self.arithmetic_tile_steps != self.iterations:
            raise ValueError((self.arithmetic_tile_steps, self.iterations))
        if self.legacy_digit_convolution_calls or self.scheduler_compositions:
            raise ValueError("digit projection reported unavailable execution work")

    @property
    def scalar_reduction(self) -> float:
        if self.karatsuba_scalar_multiplications == 0:
            return float("inf") if self.naive_scalar_products else 1.0
        return self.naive_scalar_products / self.karatsuba_scalar_multiplications

    @property
    def description_bits(self) -> int:
        return (
            sum(
                bit_width(v)
                for v in (
                    self.parameter,
                    self.modulus_bits,
                    self.iterations,
                    self.karatsuba_scalar_multiplications,
                    self.coefficient_additions,
                    self.recursive_nodes,
                    self.max_boundary_bits,
                )
            )
            + bit_width(abs(self.residue))
            + bit_width(self.sign_quotient_steps)
            + bit_width(self.sign_quotient_nonzero_digits_saved)
            + bit_width(self.arithmetic_tile_steps)
        )


def lucas_lehmer_digit_field(
    exponent: int, *, max_exponent: int = 127
) -> DigitPowerProjectionResult:
    """Run Lucas--Lehmer entirely through cyclic digit fields."""
    p = int(exponent)
    max_exponent = int(max_exponent)
    if p < 2 or p > max_exponent:
        raise ValueError((p, max_exponent))
    if p == 2:
        return DigitPowerProjectionResult(
            "mersenne", p, p, 0, 0, True, 0, 0, 0, 0, 0, 0
        )
    iterations = p - 2
    run = ArithmeticTile.from_value(ArithmeticTileSpec.mersenne(p), 4).run(iterations)
    residue = run.residue
    metrics = run.metrics
    return DigitPowerProjectionResult(
        "mersenne",
        p,
        p,
        iterations,
        residue,
        residue == 0,
        metrics.scalar_multiplications,
        metrics.naive_scalar_products,
        metrics.coefficient_additions,
        metrics.recursive_nodes,
        metrics.max_boundary_bits,
        metrics.exceptional_minus_one_steps,
        metrics.karatsuba_steps,
        metrics.schoolbook_steps,
        metrics.sign_quotient_steps,
        metrics.sign_quotient_nonzero_digits_saved,
        metrics.primitive_steps,
    )


def pepin_digit_field(
    index: int, *, base: int = 3, max_width: int = 64
) -> DigitPowerProjectionResult:
    """Run Pepin entirely through negacyclic digit fields."""
    n = int(index)
    base = int(base)
    max_width = int(max_width)
    if n < 1 or base <= 1:
        raise ValueError((n, base))
    spec = FermatNumberSpec(n)
    width = spec.exponent
    if width > max_width:
        raise ValueError((width, max_width))
    modulus = (1 << width) + 1
    iterations = width - 1
    run = ArithmeticTile.from_value(ArithmeticTileSpec.fermat(width), base).run(
        iterations
    )
    residue = run.residue
    metrics = run.metrics
    return DigitPowerProjectionResult(
        "fermat",
        n,
        width + 1,
        iterations,
        residue,
        residue == modulus - 1,
        metrics.scalar_multiplications,
        metrics.naive_scalar_products,
        metrics.coefficient_additions,
        metrics.recursive_nodes,
        metrics.max_boundary_bits,
        metrics.exceptional_minus_one_steps,
        metrics.karatsuba_steps,
        metrics.schoolbook_steps,
        metrics.sign_quotient_steps,
        metrics.sign_quotient_nonzero_digits_saved,
        metrics.primitive_steps,
    )


__all__ = [
    "DigitPowerProjectionResult",
    "lucas_lehmer_digit_field",
    "pepin_digit_field",
]
