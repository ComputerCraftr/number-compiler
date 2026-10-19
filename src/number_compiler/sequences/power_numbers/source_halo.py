"""Stationary source-bounded low ports and a mod-16 terminal consumer.

The binary six-bit halo stabilizes for Fermat sources at level four and for
Mersenne norm-one traces at level two.  This module exposes only intervals
whose every square is guarded below the cyclic/negacyclic candidate seam.
Powered intervals are constant RLE emissions; they are not prime proofs or
future-language quotients.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.polynomials.primary_jet import PrimaryJetAffineMorphism
from number_compiler.sequences.power_numbers.source_matrix import (
    PORT_BOUNDARIES,
    SmallModulusWork,
    UnwrappedInnerRadixPort,
    radix_port_from_source_residue,
    require_source_no_wrap,
)

HALO_BOUNDARIES = PORT_BOUNDARIES


def _stable_source_mod64(family: str, level: int) -> int:
    if family == "fermat":
        # 3 has order 16 in the units mod 64.  Clamping the exponent index
        # avoids constructing 2**level for arbitrarily large source levels.
        return pow(3, 1 << min(level, 4), 64)
    if family == "mersenne":
        # The exact trace sequence starts 4, 14, 194; 2 is a fixed point of
        # x -> x**2-2 modulo 64 from level two onward.
        return 4 if level == 0 else 14 if level == 1 else 2
    raise ValueError(family)


def demand_unwrapped_inner_halo_port(
    family: str, parameter: int, level: int
) -> UnwrappedInnerRadixPort:
    """Demand the fixed five carry/borrow wires and six normalized bits."""
    require_source_no_wrap(family, parameter, level)
    source = _stable_source_mod64(family, level)
    return radix_port_from_source_residue(
        family,
        parameter,
        level,
        2,
        source,
        SmallModulusWork(64, 0, 0, 0),
    )


@dataclass(frozen=True, slots=True)
class StableUnwrappedHaloBlock:
    """A powered constant source emission over a guarded interval."""

    family: str
    parameter: int
    source_level: int
    span: int

    def __post_init__(self) -> None:
        minimum_level = (
            4 if self.family == "fermat" else 2 if self.family == "mersenne" else None
        )
        if minimum_level is None:
            raise ValueError(self.family)
        if type(self.source_level) is not int or self.source_level < minimum_level:
            raise ValueError(("stable-halo-start-level-required", self.source_level))
        if type(self.span) is not int or self.span < 1:
            raise ValueError(("positive-halo-span-required", self.span))
        require_source_no_wrap(
            self.family, self.parameter, self.source_level + self.span - 1
        )

    @property
    def end_level_exclusive(self) -> int:
        return self.source_level + self.span

    @property
    def single_output(self) -> UnwrappedInnerRadixPort:
        return demand_unwrapped_inner_halo_port(
            self.family, self.parameter, self.source_level
        )

    @property
    def semantic_key(self) -> tuple[object, ...]:
        return (
            "stable-inner-source-halo",
            self.family,
            self.single_output.semantic_observation,
            "source-guarded-no-wrap-interval",
        )

    @property
    def observation_runs(
        self,
    ) -> tuple[tuple[tuple[object, ...], int], ...]:
        return ((self.single_output.semantic_observation, self.span),)

    def then(self, downstream: StableUnwrappedHaloBlock) -> StableUnwrappedHaloBlock:
        if type(downstream) is not StableUnwrappedHaloBlock:
            raise TypeError(type(downstream))
        if (
            (self.family, self.parameter) != (downstream.family, downstream.parameter)
            or self.end_level_exclusive != downstream.source_level
            or self.semantic_key != downstream.semantic_key
        ):
            raise ValueError("halo source guard or adjacent interval mismatch")
        return StableUnwrappedHaloBlock(
            self.family, self.parameter, self.source_level, self.span + downstream.span
        )

    def square(self) -> StableUnwrappedHaloBlock:
        """Double interval length and recheck every source bound structurally."""
        return StableUnwrappedHaloBlock(
            self.family, self.parameter, self.source_level, self.span * 2
        )

    def power_duration(self, duration: int) -> StableUnwrappedHaloBlock:
        """Create a constant RLE emission without visiting its time leaves."""
        return StableUnwrappedHaloBlock(
            self.family, self.parameter, self.source_level, duration
        )

    @property
    def last_four_halo(self) -> tuple[tuple[int, ...], ...]:
        if self.span < 4:
            raise ValueError("four-birth halo requires at least four source levels")
        row = self.single_output.carry
        return (row, row, row, row)


def compose_last_four_source_tangents(
    tangents: tuple[PrimaryJetAffineMorphism, ...],
) -> PrimaryJetAffineMorphism:
    """Consume four supplied ``(2*X_t,B_t)`` actions modulo 16.

    The shared primary-jet affine algebra proves that their old-source kernel
    vanishes.  This consumer never derives an unknown ``B_t`` from a halo port;
    callers must supply exact forcing births from an independent source proof.
    """
    if type(tangents) is not tuple or len(tangents) != 4:
        raise ValueError("four chronological mod-16 source tangents are required")
    if any(
        type(action) is not PrimaryJetAffineMorphism
        or action.degree != 2
        or action.modulus != 16
        or any(coefficient & 1 for coefficient in action.kernel)
        for action in tangents
    ):
        raise ValueError("four even degree-two source tangents modulo 16 are required")
    result = PrimaryJetAffineMorphism.identity(degree=2, modulus=16)
    for action in tangents:
        result = result.then(action)
    if not result.source_annihilated:
        raise ArithmeticError(
            "four even primary kernels failed to annihilate the old jet"
        )
    return result


__all__ = [
    "HALO_BOUNDARIES",
    "StableUnwrappedHaloBlock",
    "compose_last_four_source_tangents",
    "demand_unwrapped_inner_halo_port",
]
