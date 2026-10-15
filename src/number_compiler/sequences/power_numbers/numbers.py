"""Canonical Fermat / Mersenne carriers and exact bounded projectors.

These families share the same cyclotomic, radix-word, factor-set, and powered
operator machinery used by reverse-add, Collatz, and the prime projector:

* ``F_n = 2**(2**n)+1 = Phi_(2**(n+1))(2)`` is a pure 2-power cyclotomic /
  negacyclic channel.  Subtracting one conjugates generation to squaring.
* ``M_p = 2**p-1 = Phi_p(2)`` when ``p`` is prime is an odd cyclotomic /
  cyclic channel.  The trace-square map ``x -> x*x-2`` conjugates to exponent
  doubling in the norm-one quadratic unit ``2+sqrt(3)``.

These generator identities do not construct the candidate's primality bit.
Production classification requires a separately proved candidate-derived
observation; missing recovery remains unresolved.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import gcd
from typing import TYPE_CHECKING

from number_compiler.arithmetic.fields.symbolic_extent import DyadicExtent
from number_compiler.sequences.prime.set import is_prime_u64, smallest_factor

if TYPE_CHECKING:
    from number_compiler.sequences.power_numbers.fermat_pumped_radial_unit import (
        FermatPumpedRadialUnit,
    )
    from number_compiler.sequences.power_numbers.signed_terminal_halo import (
        SignedFoldBirthWindow,
    )
    from number_compiler.sequences.power_numbers.source_halo import (
        StableUnwrappedHaloBlock,
    )
    from number_compiler.sequences.power_numbers.source_matrix import (
        FermatMultiradixPort,
        UnwrappedInnerDigitStencil,
        UnwrappedInnerRadixPort,
    )
    from number_compiler.sequences.power_numbers.terminal_source_demand import (
        SourceTerminalDemand,
    )
    from number_compiler.sequences.power_numbers.three_dyadic_pivot_moore import (
        DyadicPivotMoore,
    )
    from number_compiler.sequences.power_numbers.three_power_joint_quotient import (
        ThreePowerJointQuotient,
    )


@dataclass(frozen=True, slots=True)
class FermatNumberSpec:
    index: int

    def __post_init__(self) -> None:
        if self.index < 0:
            raise ValueError(self.index)

    @property
    def exponent_extent(self) -> DyadicExtent:
        return DyadicExtent(self.index)

    @property
    def bit_length_extent(self) -> DyadicExtent:
        return DyadicExtent(self.index, 1)

    @property
    def cyclotomic_order_extent(self) -> DyadicExtent:
        return DyadicExtent(self.index + 1)

    @property
    def exponent(self) -> int:
        # Compatibility/materialization view.  Production source compilation
        # uses exponent_extent and never calls this property.
        return self.exponent_extent.materialize(max_power=self.index)

    @property
    def cyclotomic_order(self) -> int:
        return self.cyclotomic_order_extent.materialize(max_power=self.index + 1)

    @property
    def bit_length(self) -> int:
        return self.bit_length_extent.materialize(max_power=self.index)

    @property
    def description_bits(self) -> int:
        return max(1, self.index.bit_length())

    def materialize(self, *, max_bits: int = 1_000_000) -> int:
        max_bits = int(max_bits)
        if max_bits <= 0 or self.bit_length_extent > max_bits:
            raise ValueError((self.bit_length_extent, max_bits))
        # The guard above proves the exponent is small enough for the requested
        # materialization budget before any dyadic boundary is lowered.
        exponent = self.exponent_extent.materialize(max_power=max_bits.bit_length())
        return (1 << exponent) + 1

    def terminal_source_demand(self) -> SourceTerminalDemand:
        """Return a lazy, candidate-bound source obligation, never a proof bit."""
        from number_compiler.sequences.power_numbers.terminal_source_demand import (
            SourceTerminalDemand,
        )

        return SourceTerminalDemand.for_candidate("fermat", self.index)

    def demand_joint_three_power_quotient(
        self,
        level: int,
        demands: tuple[tuple[int, int], ...] = (
            (2, 16),
            (3, 10),
            (5, 8),
            (7, 6),
            (10, 6),
            (11, 5),
            (13, 5),
            (27, 4),
        ),
        *,
        moving_width: int = 12,
    ) -> ThreePowerJointQuotient:
        """Share one unwrapped source across finite CRT, pivot and Walsh demands.

        The packet does not evaluate the Fermat candidate modulus or issue a
        primality status. Walsh transforms are computed only when requested
        from the returned packet.
        """
        from number_compiler.sequences.power_numbers.three_power_joint_quotient import (
            demand_three_power_joint_quotient,
        )

        return demand_three_power_joint_quotient(
            self.index, level, demands, moving_width=moving_width
        )

    def demand_pumped_radial_unit(self, level: int) -> FermatPumpedRadialUnit:
        """Retain the exact symbolic radial/unit split at one nested level.

        This is a source description only. It does not evaluate the unit
        modulo the Fermat candidate or contribute a primality decision.
        """
        from number_compiler.sequences.power_numbers.fermat_pumped_radial_unit import (
            FermatPumpedRadialUnit,
        )

        return FermatPumpedRadialUnit(self.index, level)

    def demand_dyadic_pivot_moore(
        self, level: int, offsets: tuple[int, ...] = (0, 1, 2, 3, 5, 6)
    ) -> DyadicPivotMoore:
        """Demand bounded local pivot ports inside this Fermat source horizon.

        The returned Moore observer retains ``level`` as occurrence metadata;
        its finite state is not a candidate-primality observation.
        """
        if type(self.index) is not int or self.index < 1:
            raise ValueError(("Fermat source index", self.index))
        if type(level) is not int or level < 1:
            raise ValueError(("dyadic source level", level))
        if not self.exponent_extent.contains_index(level):
            raise ValueError(("level-exceeds-Fermat-source", level, self.index))
        from number_compiler.sequences.power_numbers.three_dyadic_pivot_moore import (
            DyadicPivotMoore,
        )

        return DyadicPivotMoore(level, offsets)

    def demand_three_power_multiradix_port(
        self, level: int, base: int, places: int
    ) -> FermatMultiradixPort:
        """Demand bounded low-radix carry/borrow wires of ``3**(2**level)``.

        The small-modulus source observation is separate from candidate
        reduction and is not a terminal remainder or primality certificate.
        """
        from number_compiler.sequences.power_numbers.source_matrix import (
            demand_three_power_multiradix_port,
        )

        return demand_three_power_multiradix_port(self.index, level, base, places)

    def demand_unwrapped_inner_radix_port(
        self, level: int, base: int
    ) -> UnwrappedInnerRadixPort:
        """Demand bounded source carry/borrow/digit wires under the no-wrap guard."""
        from number_compiler.sequences.power_numbers.source_matrix import (
            demand_unwrapped_inner_radix_port,
        )

        return demand_unwrapped_inner_radix_port("fermat", self.index, level, base)

    def demand_unwrapped_inner_digit_stencil(
        self, level: int, base: int, positions: tuple[int, ...]
    ) -> UnwrappedInnerDigitStencil:
        """Demand only selected digits of the raw inner square source."""
        from number_compiler.sequences.power_numbers.source_matrix import (
            demand_unwrapped_inner_digit_stencil,
        )

        return demand_unwrapped_inner_digit_stencil(
            "fermat", self.index, level, base, positions
        )

    def power_stable_unwrapped_inner_halo(
        self, source_level: int, span: int
    ) -> StableUnwrappedHaloBlock:
        """Power an explicitly requested stationary no-wrap binary halo."""
        from number_compiler.sequences.power_numbers.source_halo import (
            StableUnwrappedHaloBlock,
        )

        return StableUnwrappedHaloBlock("fermat", self.index, source_level, span)

    def project_signed_fold_birth_window(
        self, source: object, *, start: int = 0, length: int = 64
    ) -> SignedFoldBirthWindow:
        """Project an already supplied negacyclic fold, conditionally."""
        from number_compiler.arithmetic.carry.signed_weighted_carry import (
            WideSignedCarryAction,
        )
        from number_compiler.sequences.power_numbers.signed_terminal_halo import (
            demand_signed_birth_window,
        )

        if type(source) is not WideSignedCarryAction:
            raise TypeError("signed-fold projection requires a carry SLP")
        if (
            source.sign != -1
            or source.width & (source.width - 1)
            or source.width.bit_length() - 1 != self.index
        ):
            raise ValueError("Fermat signed-fold width or negacyclic seam mismatch")
        return demand_signed_birth_window(source, start=start, length=length)


@dataclass(frozen=True, slots=True)
class MersenneNumberSpec:
    exponent: int

    def __post_init__(self) -> None:
        if self.exponent <= 0:
            raise ValueError(self.exponent)

    @property
    def bit_length(self) -> int:
        return self.exponent

    @property
    def description_bits(self) -> int:
        return max(1, self.exponent.bit_length())

    def materialize(self, *, max_bits: int = 1_000_000) -> int:
        max_bits = int(max_bits)
        if max_bits <= 0 or self.bit_length > max_bits:
            raise ValueError((self.bit_length, max_bits))
        return (1 << self.exponent) - 1

    def terminal_source_demand(self) -> SourceTerminalDemand:
        """Return a lazy cyclic trace demand, not a Lucas-Lehmer certificate."""
        from number_compiler.sequences.power_numbers.terminal_source_demand import (
            SourceTerminalDemand,
        )

        return SourceTerminalDemand.for_candidate("mersenne", self.exponent)

    def project_signed_fold_birth_window(
        self, source: object, *, start: int = 0, length: int = 64
    ) -> SignedFoldBirthWindow:
        """Project an already supplied cyclic fold, conditionally."""
        from number_compiler.arithmetic.carry.signed_weighted_carry import (
            WideSignedCarryAction,
        )
        from number_compiler.sequences.power_numbers.signed_terminal_halo import (
            demand_signed_birth_window,
        )

        if type(source) is not WideSignedCarryAction:
            raise TypeError("signed-fold projection requires a carry SLP")
        if source.sign != 1 or source.width != self.exponent:
            raise ValueError("Mersenne signed-fold width or cyclic seam mismatch")
        return demand_signed_birth_window(source, start=start, length=length)

    def demand_unwrapped_inner_radix_port(
        self, level: int, base: int
    ) -> UnwrappedInnerRadixPort:
        """Demand bounded source carry/borrow/digit wires under the no-wrap guard."""
        from number_compiler.sequences.power_numbers.source_matrix import (
            demand_unwrapped_inner_radix_port,
        )

        return demand_unwrapped_inner_radix_port("mersenne", self.exponent, level, base)

    def demand_unwrapped_inner_digit_stencil(
        self, level: int, base: int, positions: tuple[int, ...]
    ) -> UnwrappedInnerDigitStencil:
        """Demand only selected digits of the raw norm-one trace square."""
        from number_compiler.sequences.power_numbers.source_matrix import (
            demand_unwrapped_inner_digit_stencil,
        )

        return demand_unwrapped_inner_digit_stencil(
            "mersenne", self.exponent, level, base, positions
        )

    def power_stable_unwrapped_inner_halo(
        self, source_level: int, span: int
    ) -> StableUnwrappedHaloBlock:
        """Power an explicitly requested stationary no-wrap binary halo."""
        from number_compiler.sequences.power_numbers.source_halo import (
            StableUnwrappedHaloBlock,
        )

        return StableUnwrappedHaloBlock("mersenne", self.exponent, source_level, span)


@dataclass(frozen=True, slots=True)
class CyclotomicRadixWordSpec:
    """Symbolic reinterpretation of a sparse binary special-number word.

    ``family='fermat'`` means the digit word ``1 0^(2^n-1) 1`` evaluated in
    ``radix``; ``family='mersenne'`` means ``1^p`` evaluated in ``radix``.
    These are respectively ``Phi_(2^(n+1))(radix)`` and, for prime ``p``,
    ``Phi_p(radix)``.  The digit program stays compact even when the evaluated
    integer is enormous.
    """

    family: str
    parameter: int
    radix: int

    def __post_init__(self) -> None:
        if (
            self.family not in ("fermat", "mersenne")
            or self.parameter < 0
            or self.radix < 2
        ):
            raise ValueError(self)
        if self.family == "mersenne" and self.parameter <= 0:
            raise ValueError(self)

    @property
    def cyclotomic_order_extent(self) -> DyadicExtent | int:
        return (
            DyadicExtent(self.parameter + 1)
            if self.family == "fermat"
            else self.parameter
        )

    @property
    def digit_length_extent(self) -> DyadicExtent | int:
        return (
            DyadicExtent(self.parameter, 1)
            if self.family == "fermat"
            else self.parameter
        )

    @property
    def cyclotomic_order(self) -> int:
        value = self.cyclotomic_order_extent
        return (
            value.materialize(max_power=value.power)
            if isinstance(value, DyadicExtent)
            else int(value)
        )

    @property
    def digit_length(self) -> int:
        value = self.digit_length_extent
        return (
            value.materialize(max_power=value.power)
            if isinstance(value, DyadicExtent)
            else int(value)
        )

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "cyclotomic-radix-word",
            self.family,
            int(self.parameter),
            int(self.radix),
        )

    @property
    def description_bits(self) -> int:
        return max(1, self.parameter.bit_length()) + max(1, self.radix.bit_length()) + 1

    def materialize(self, *, max_digits: int = 100_000) -> int:
        max_digits = int(max_digits)
        extent = self.digit_length_extent
        if (
            (extent > max_digits)
            if isinstance(extent, DyadicExtent)
            else (int(extent) > max_digits)
        ):
            raise ValueError((extent, max_digits))
        if self.family == "fermat":
            exponent = DyadicExtent(self.parameter).materialize(
                max_power=max_digits.bit_length()
            )
            return int(pow(self.radix, exponent)) + 1
        return (int(pow(self.radix, self.parameter)) - 1) // (self.radix - 1)


def fermat_radix_reinterpretation(index: int, radix: int) -> CyclotomicRadixWordSpec:
    return CyclotomicRadixWordSpec("fermat", int(index), int(radix))


def mersenne_radix_reinterpretation(
    exponent: int, radix: int
) -> CyclotomicRadixWordSpec:
    return CyclotomicRadixWordSpec("mersenne", int(exponent), int(radix))


def fermat_number(index: int) -> int:
    return FermatNumberSpec(int(index)).materialize()


def mersenne_number(exponent: int) -> int:
    return MersenneNumberSpec(int(exponent)).materialize()


def fermat_successor(value: int) -> int:
    """Polynomial generation recurrence ``F_(n+1)=(F_n-1)^2+1``."""
    value = int(value)
    if value < 3:
        raise ValueError(value)
    return (value - 1) * (value - 1) + 1


def mersenne_successor(value: int) -> int:
    """Exponent-by-one recurrence ``M_(n+1)=2*M_n+1``."""
    value = int(value)
    if value < 1:
        raise ValueError(value)
    return 2 * value + 1


def fermat_previous_product(index: int) -> int:
    """Return ``prod(F_0..F_(n-1)) = F_n-2`` for bounded materialized ``n``."""
    index = int(index)
    if index < 0:
        raise ValueError(index)
    return FermatNumberSpec(index).materialize() - 2


def mersenne_gcd_spec(first_exponent: int, second_exponent: int) -> MersenneNumberSpec:
    """Symbolic form of ``gcd(M_a,M_b)=M_gcd(a,b)``."""
    a, b = int(first_exponent), int(second_exponent)
    if a <= 0 or b <= 0:
        raise ValueError((a, b))
    return MersenneNumberSpec(gcd(a, b))


def special_modulus_matches(family: str, parameter: int, modulus: int) -> bool:
    """Validate a concrete Fermat/Mersenne modulus without duplicate huge powers."""
    family, parameter, modulus = str(family), int(parameter), int(modulus)
    if family == "fermat":
        m = modulus - 1
        exponent = m.bit_length() - 1 if m > 0 else -1
        return (
            parameter >= 0
            and m > 0
            and not (m & (m - 1))
            and exponent > 0
            and not (exponent & (exponent - 1))
            and exponent.bit_length() - 1 == parameter
        )
    if family == "mersenne":
        m = modulus + 1
        return (
            parameter >= 2
            and m > 0
            and not (m & (m - 1))
            and m.bit_length() - 1 == parameter
        )
    raise ValueError(family)


def verified_special_divisor(
    family: str, parameter: int, modulus: int, defect: int
) -> int:
    """Check an admitted integer witness against the exact candidate source."""
    if not special_modulus_matches(family, parameter, modulus):
        raise ValueError("defect modulus does not match the requested special source")
    support = gcd(modulus, defect)
    if not 1 < support < modulus:
        raise ValueError("unissued defect must exhibit a proper candidate divisor")
    return support


def mersenne_exponent_is_prime(exponent: int) -> bool:
    """Decide the exponent gate without producing an unnecessary factor.

    Mersenne primality only reaches the number-level theorem when the exponent
    itself is prime.  For machine-word exponents the repository already has an
    exact deterministic Miller--Rabin predicate, so do not trial-divide all the
    way to sqrt(p) merely to learn the same Boolean.  Larger Python integers
    retain the exact historical factor-producing fallback.
    """
    n = int(exponent)
    if n < 2:
        return False
    if n < (1 << 64):
        return is_prime_u64(n)
    return smallest_factor(n) is None


def mersenne_composite_exponent_factor(
    exponent: int, *, max_divisor: int | None = None
) -> MersenneNumberSpec | None:
    """Return a symbolic proper Mersenne divisor when the exponent is composite."""
    n = int(exponent)
    if n <= 1:
        raise ValueError(n)
    factor = smallest_factor(n, max_divisor=max_divisor)
    return None if factor is None else MersenneNumberSpec(factor)


def fermat_factor_stride(index: int) -> int:
    """Stride forced on prime divisors of ``F_n`` for ``n>=2``."""
    index = int(index)
    if index < 2:
        raise ValueError(index)
    return 1 << (index + 2)


def mersenne_factor_stride(exponent: int) -> int:
    """Every prime divisor of ``2**p-1`` for prime ``p`` is ``1 mod 2p``."""
    exponent = int(exponent)
    if exponent < 2:
        raise ValueError(exponent)
    return 2 * exponent


__all__ = [
    "CyclotomicRadixWordSpec",
    "FermatNumberSpec",
    "MersenneNumberSpec",
    "fermat_factor_stride",
    "fermat_number",
    "fermat_previous_product",
    "fermat_radix_reinterpretation",
    "fermat_successor",
    "mersenne_composite_exponent_factor",
    "mersenne_exponent_is_prime",
    "mersenne_factor_stride",
    "mersenne_gcd_spec",
    "mersenne_number",
    "mersenne_radix_reinterpretation",
    "mersenne_successor",
    "special_modulus_matches",
    "verified_special_divisor",
]
