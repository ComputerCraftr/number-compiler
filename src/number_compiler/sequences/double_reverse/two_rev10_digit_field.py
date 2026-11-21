"""Both mod-18 digit-field orientations for physical ``x -> 2*rev10(x)``.

For each *source* decimal digit d, emit the variable-width string str(2*d).
The user's low-first field concatenates those blocks LSD-to-MSD; its
character reversal is NOT the field produced by doubling a reversed source.

For every positive x, independently of decimal length and leading zeros:
    low_first_field(x) == high_first_field(x) == 2*x (mod 18)
    reverse_characters(low_first_field(x))
        == low_first_field(x) + 9*[x%10 >= 5] (mod 18).

The first identity is a universal autonomous temporal quotient: q' = 2*q.
The second is a lossless encoding of ONE physical low multiplication-carry
port, not an autonomous all-future carry program. Its powered lift is valid
ONLY on a source-authorized 2rev10 four-phase border cylinder. The existing
seed-morphism/Laurent packet is the authority for that guard; constructing
this small state directly does not certify membership in the cylinder.

On the certified border: phase 0,1,2,3 gives (leading, trailing) digits
(1,8), (1,2), (4,2), (4,8). Therefore the last-digit carry is
1,0,0,1. Its centered bit h=2c-1 obeys h(n+2)=-h(n), i.e.
Phi_4(S)*h = (S**2+1)*h = 0. The unconditional mod-18 ring and this
source-guarded harmonic have joint primitive period 12 for seed 196.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import lcm
from typing import TypedDict

from .temporal_hashlife_borders import outer_digits

MODULUS = 18


class _FieldOrientations90(TypedDict):
    high_first_mod90: int
    low_first_mod90: int
    reverse_characters_of_high_first_mod90: int
    reverse_characters_of_low_first_mod90: int


class _DigitFieldPacket(TypedDict):
    modulus: int
    scope: str
    low_first_digit_field_mod18: int
    high_first_digit_field_mod18: int
    four_field_orientations_mod90: _FieldOrientations90
    reversed_characters_of_low_first_mod18: int
    reversed_characters_of_high_first_mod18: int
    decoded_low_multiply_carry: int
    border_phase: int
    leading_source_digit: int
    trailing_source_digit: int
    decimal_width_growth_bit: int
    centered_phi4_harmonic: int
    harmonic_annihilator: str
    successor_low_first_mod18: int
    successor_reverse_characters_mod18: int
    temporal_primitive_period: int
    moore_joint_state_bound: int
    temporal_powering: str
    independent_reverse_residue_successor_closed: bool
    joint_source_guarded_successor_closed: bool
    full_interior_carry_vector_successor_closed: bool
    source_occurrences_materialized: int


def universal_forward_field_mod18(seed: int, generation: int) -> int:
    """Unconditionally powered 2rev10 digit field, for every positive seed.

    Unlike the reversed-character field, this does not require an issued
    source border: reversal preserves the seed mod 9 and mod-18 field parity
    is always even. Thus D_2(X_n) == 2**(n+1)*seed (mod 18).
    """
    if type(seed) is not int or seed < 0:
        raise ValueError("digit-field seed must be a nonnegative integer")
    if type(generation) is not int or generation < 0:
        raise ValueError("digit-field generation must be nonnegative")
    return (2 * (seed % 9) * pow(2, generation, 18)) % 18


def _first_doubled_digit(digit: int) -> int:
    return 1 if digit >= 5 else 2 * digit


@dataclass(frozen=True, slots=True)
class TwoReverseDualDigitField18:
    """Guarded Moore state for the two mod-18 fields and their carry port.

    ``from_border`` must only be called by a source-authorized border owner.
    ``power`` is a *temporal* power for that guarded class, not spatial word
    repetition. No physical occurrence rows, integer endpoints or carry
    histories are stored in a state or visited during powering.
    """

    residue: int
    border_phase: int

    def __post_init__(self) -> None:
        if type(self.residue) is not int or self.residue not in range(0, 18, 2):
            raise ValueError("digit-field mod-18 residue must be even")
        if type(self.border_phase) is not int or self.border_phase not in range(4):
            raise ValueError("2rev10 requires an authenticated border phase 0..3")

    @classmethod
    def from_border(
        cls, *, physical_mod198: int, phase: int
    ) -> TwoReverseDualDigitField18:
        if type(physical_mod198) is not int or physical_mod198 not in range(198):
            raise ValueError("invalid issued physical mod-198 projection")
        return cls(2 * physical_mod198 % MODULUS, phase)

    @staticmethod
    def _crt90(field_mod9: int, last_digit: int) -> int:
        """Canonical CRT: z % 9 = field_mod9, z % 10 = last_digit."""
        return (last_digit + 10 * ((field_mod9 - last_digit) % 9)) % 90

    @property
    def four_field_orientations_mod90(self) -> _FieldOrientations90:
        """All four word/reversal readouts, selected by the certified ports.

        The *shared* digit-sum class is self.residue % 9.  The last
        character in each orientation comes from one boundary digit;
        no part of the emitted concatenation is constructed here.
        """
        lead, trail = outer_digits(self.border_phase)
        r9 = self.residue % 9
        return {
            "high_first_mod90": self._crt90(r9, 2 * trail % 10),
            "low_first_mod90": self._crt90(r9, 2 * lead % 10),
            "reverse_characters_of_high_first_mod90": self._crt90(
                r9, _first_doubled_digit(lead)
            ),
            "reverse_characters_of_low_first_mod90": self._crt90(
                r9, _first_doubled_digit(trail)
            ),
        }

    @property
    def incoming_carry(self) -> int:
        """Actual low-source multiplication carry [source units digit >= 5]."""
        return int(outer_digits(self.border_phase)[1] >= 5)

    @property
    def reversed_characters_mod18(self) -> int:
        """User's ``int(dig_f[::-1]) % 18``, without emitting the field."""
        return (self.residue + 9 * self.incoming_carry) % MODULUS

    @property
    def centered_harmonic(self) -> int:
        """The exact fourth-cyclotomic coordinate h = 2*c - 1."""
        return 2 * self.incoming_carry - 1

    @property
    def primitive_period(self) -> int:
        """Moore period for both observable residues with their future ports."""
        mod9 = self.residue // 2
        period9 = next(p for p in (1, 2, 6) if (pow(2, p, 9) - 1) * mod9 % 9 == 0)
        return lcm(4, period9)

    def power(self, physical_steps: int) -> TwoReverseDualDigitField18:
        """Binary modular power of the genuine joint temporal action."""
        if type(physical_steps) is not int or physical_steps < 0:
            raise ValueError("physical steps must be a nonnegative integer")
        return type(self)(
            self.residue * pow(2, physical_steps, MODULUS) % MODULUS,
            (self.border_phase + physical_steps) % 4,
        )

    def successor(self) -> TwoReverseDualDigitField18:
        return self.power(1)

    def packet(self) -> _DigitFieldPacket:
        next_state = self.successor()
        lead, trail = outer_digits(self.border_phase)
        orientations = self.four_field_orientations_mod90
        forward_mod18 = orientations["high_first_mod90"] % MODULUS
        low_carry = int(trail >= 5)
        return {
            "modulus": MODULUS,
            "scope": "source-authenticated 2rev10 four-phase border; not full carry-vector",
            "low_first_digit_field_mod18": forward_mod18,
            "high_first_digit_field_mod18": forward_mod18,
            "four_field_orientations_mod90": orientations,
            "reversed_characters_of_low_first_mod18": orientations[
                "reverse_characters_of_low_first_mod90"
            ]
            % MODULUS,
            "reversed_characters_of_high_first_mod18": orientations[
                "reverse_characters_of_high_first_mod90"
            ]
            % MODULUS,
            "decoded_low_multiply_carry": low_carry,
            "border_phase": self.border_phase,
            "leading_source_digit": lead,
            "trailing_source_digit": trail,
            "decimal_width_growth_bit": low_carry,
            "centered_phi4_harmonic": 2 * low_carry - 1,
            "harmonic_annihilator": "S^2+1",
            "successor_low_first_mod18": next_state.residue,
            "successor_reverse_characters_mod18": next_state.reversed_characters_mod18,
            "temporal_primitive_period": self.primitive_period,
            "moore_joint_state_bound": 36,
            "temporal_powering": "q -> 2**steps*q mod18; phase -> phase+steps mod4",
            "independent_reverse_residue_successor_closed": False,
            "joint_source_guarded_successor_closed": True,
            "full_interior_carry_vector_successor_closed": False,
            "source_occurrences_materialized": 0,
        }


__all__ = ["TwoReverseDualDigitField18", "universal_forward_field_mod18"]
