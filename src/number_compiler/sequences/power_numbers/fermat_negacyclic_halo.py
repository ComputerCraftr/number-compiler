"""Source-issued fixed-tripling projection in a bounded Fermat ring.

The quotient is relative to the canonical residue at the selected source
seam. It is not a raw integer carry or a certificate for a squaring orbit.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from number_compiler.arithmetic.automata.affine_port_action import AffinePortAction
from number_compiler.sequences.power_numbers._harmonic_authority import (
    harmonic_verified,
    issue_harmonic,
    new_harmonic_issuer,
)
from number_compiler.sequences.power_numbers.fermat_boundary_macros import (
    FermatAlgebraicRoot,
    issue_algebraic_root,
)

MAX_HALO_INDEX = 8
MAX_HALO_WRAP_BITS = 256
MAX_HALO_STEPS = 4096


@dataclass(frozen=True, slots=True, weakref_slot=True)
class FermatNegacyclicHalo:
    """Issued bounded projection of the exact source under ordinary tripling."""

    source: FermatAlgebraicRoot = field(repr=False)
    width: int
    physical_steps: int
    wrap_bits: int
    source_residue: int
    endpoint_residue: int
    canonical_source_wrap: int | None
    inlet_low: int
    inlet_high_correction: int
    _issuer: object = field(default=None, init=False, repr=False, compare=False)

    def issuer_payload(self) -> tuple[object, ...]:
        return (
            self.source.issuer_payload(),
            self.width,
            self.physical_steps,
            self.wrap_bits,
            self.source_residue,
            self.endpoint_residue,
            self.canonical_source_wrap,
            self.inlet_low,
            self.inlet_high_correction,
        )

    @property
    def producer_verified(self) -> bool:
        return self.source.producer_verified and harmonic_verified(
            self, self.issuer_payload(), issuer=_HALO_ISSUER
        )

    @property
    def modulus(self) -> int:
        return (1 << self.width) + 1

    def endpoint_bits(self, positions: tuple[int, ...]) -> tuple[int, ...]:
        """Read canonical residue bits, including the exceptional minus one."""
        if not self.producer_verified:
            raise ValueError("unissued negacyclic halo")
        if type(positions) is not tuple or any(
            type(position) is not int or not 0 <= position <= self.width
            for position in positions
        ):
            raise ValueError("halo positions must lie within the canonical residue")
        return tuple((self.endpoint_residue >> position) & 1 for position in positions)

    def packet(self) -> dict[str, object]:
        if not self.producer_verified:
            raise ValueError("unissued negacyclic halo")
        return {
            "source_authority": "issued exact Fermat exponent root",
            "source_level": self.source.level,
            "width_bits": self.width,
            "modulus": self.modulus,
            "physical_steps": self.physical_steps,
            "source_residue": self.source_residue,
            "endpoint_residue": self.endpoint_residue,
            "canonical_source_wrap_bits": self.wrap_bits,
            "canonical_source_wrap": self.canonical_source_wrap,
            "canonical_inlet_low": self.inlet_low,
            "canonical_inlet_high_correction": self.inlet_high_correction,
            "raw_source_carry": None,
            "primality_authority": False,
        }


_HALO_ISSUER = new_harmonic_issuer(FermatNegacyclicHalo)


def demand_fixed_multiplier_halo(
    index: int, level: int, physical_steps: int, *, wrap_bits: int = 32
) -> FermatNegacyclicHalo:
    """Power the source-issued ordinary ×3 action; retain demanded wrap bits."""
    if (
        type(index) is not int
        or not 0 <= index <= MAX_HALO_INDEX
        or type(level) is not int
        or level != (1 << index) - 1
        or type(physical_steps) is not int
        or not 1 <= physical_steps <= MAX_HALO_STEPS
        or type(wrap_bits) is not int
        or not 0 <= wrap_bits <= MAX_HALO_WRAP_BITS
    ):
        raise ValueError("negacyclic halo exceeds its admitted source or work bound")
    source_owner = issue_algebraic_root(index, level)
    if not source_owner.producer_verified:
        raise ValueError("unissued exact Fermat exponent root")
    width = 1 << index
    modulus = (1 << width) + 1
    # Do not reduce this exponent by an assumed Euler period: 3 may divide M.
    source = pow(3, 1 << level, modulus)
    high, low = divmod(3 * source, 1 << width)
    packed_modulus = modulus << wrap_bits
    action = AffinePortAction.reduced(
        packed_modulus, pow(3, physical_steps, packed_modulus), 0
    )
    wrap, endpoint = divmod(action.apply(source), modulus)
    result = FermatNegacyclicHalo(
        source_owner,
        width,
        physical_steps,
        wrap_bits,
        source,
        endpoint,
        wrap if wrap_bits else None,
        low,
        -high,
    )
    issue_harmonic(result, result.issuer_payload(), issuer=_HALO_ISSUER)
    if not result.producer_verified:
        raise ArithmeticError("negacyclic halo publication failed")
    return result
