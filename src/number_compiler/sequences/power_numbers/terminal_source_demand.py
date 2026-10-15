"""NC14 source-owned terminal demands, not invented Fermat/Mersenne proofs.

The prime-threshold consumer needs a global signed-fold/occupied-support action.
This module binds its demand to the same candidate as the source-observer
machinery, including the Collatz radial clock, normalized difference unit,
Walsh64/F5 and the *moving* pivot XOR bank.  No finite source packet is
mistaken for an authenticated terminal carry-cochain.

Unlike the old diagnostic-only join, the terminal-threshold choke point now
retains a typed demand.  Expensive source observations are strictly lazy and
explicit, so even a 1-million-bit symbolic candidate cannot trigger eager
powering or a polynomial expansion during a prime query.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.arithmetic.fields.homogeneous_growth import HomogeneousGrowthScale
from number_compiler.arithmetic.fields.integer_congruence import join_congruences
from number_compiler.arithmetic.fields.radial_sturmian import RadialSturmianClock
from number_compiler.arithmetic.fields.walsh import WalshH5
from number_compiler.sequences.power_numbers.source_matrix import (
    MAX_SOURCE_LEVEL_BITS,
    _source_residue,
)
from number_compiler.sequences.power_numbers.three_power_joint_quotient import (
    DEFAULT_RADIX_DEMANDS,
    ThreePowerJointQuotient,
    demand_three_power_joint_quotient,
)

HALO_BOUNDARIES = (1, 2, 3, 5, 6)
SOURCE_TO_FOLD_GAP = "powered-unwrapped-source-to-global-signed-fold-not-certified"
FOLD_TO_THRESHOLD_GAP = "signed-halo-to-local-support-threshold-not-certified"
MAX_EXPLICIT_OBSERVED_LEVEL = 512
DEFAULT_MERSENNE_MODULI = (64, 125, 343, 1000, 1331)


def moving_walsh_h5(packet: ThreePowerJointQuotient) -> WalshH5 | None:
    """Exact H5 of the moving aligned-unit XOR mask at *absolute* bit offsets.

    Absolute position = source pivot (t+2) + unit offset (t+1) + local bit.
    The empty preceding word merely transports the length phase of the
    six-periodic Phi2 x Phi3 character.  This is a source observation, not a
    signed-Fermat-birth harmonic or a successor-closed prime state.
    """
    moving = packet.moving_unit_xor
    if moving is None:
        return None
    position = packet.level + 2 + moving.unit_offset
    relative = WalshH5.from_mask(moving.xor_mask, moving.width)
    initial_shift = WalshH5(position % 6, 0, 0, 0)
    shifted = initial_shift.then(relative)
    # End-position phase does not belong in a sparse Walsh packet; keep zero
    # as the identity length for later *additive* field use.
    return WalshH5(0, shifted.phi2, shifted.phi3_a, shifted.phi3_b)


@dataclass(frozen=True, slots=True)
class SourceTerminalDemand:
    """Candidate-bound terminal source obligation; no eager residue work."""

    family: str
    parameter: int
    source_level: int
    candidate_width: int
    sign: int
    source_kind: str

    def __post_init__(self) -> None:
        if (
            type(self.family) is not str
            or type(self.source_kind) is not str
            or any(
                type(value) is not int
                for value in (
                    self.parameter,
                    self.source_level,
                    self.candidate_width,
                    self.sign,
                )
            )
        ):
            raise TypeError("terminal source demand fields must have exact types")
        if type(self.parameter) is not int or self.parameter < 2:
            raise ValueError("terminal source parameter must be an integer >= 2")
        if self.family == "fermat":
            if self.parameter > MAX_SOURCE_LEVEL_BITS:
                raise ValueError(
                    "Fermat source parameter exceeds the symbolic level budget"
                )
            if (
                self.candidate_width != 1 << self.parameter
                or self.source_level != self.candidate_width - 1
                or self.sign != -1
                or self.source_kind != "dyadic-three-power"
            ):
                raise ValueError("Fermat terminal demand is not source-aligned")
        elif self.family == "mersenne":
            if (
                self.parameter != self.candidate_width
                or self.source_level != self.parameter - 2
                or self.sign != 1
                or self.source_kind != "norm-one-quadratic-trace"
            ):
                raise ValueError("Mersenne terminal demand is not source-aligned")
        else:
            raise ValueError("unknown terminal family")
        if self.source_level < 4:
            raise ValueError("four transitions require five nonnegative source levels")

    @classmethod
    def for_candidate(cls, family: str, parameter: int) -> SourceTerminalDemand:
        if type(parameter) is not int or parameter < 2:
            raise ValueError("terminal source parameter must be an integer >= 2")
        if family == "fermat":
            if parameter > MAX_SOURCE_LEVEL_BITS:
                raise ValueError(
                    "Fermat source parameter exceeds the symbolic level budget"
                )
            width = 1 << parameter
            return cls(family, parameter, width - 1, width, -1, "dyadic-three-power")
        if family == "mersenne":
            return cls(
                family,
                parameter,
                parameter - 2,
                parameter,
                1,
                "norm-one-quadratic-trace",
            )
        raise ValueError(family)

    @property
    def last_four_source_levels(self) -> tuple[int, ...]:
        """Four transitions require five consecutive chronological sources."""
        return tuple(range(self.source_level - 4, self.source_level + 1))

    @property
    def collatz_radial_clock(self) -> RadialSturmianClock:
        """Shared exact 3/2 radial phase; no irrational float approximation.

        For Fermat 3**(2**t), {2**t log2(3/2)}={2**t log2(3)}.
        The clock is an *occurrence*, not a complete global-fold transition.
        """
        if self.family != "fermat":
            raise ValueError(
                "Mersenne quadratic trace is not a three-power radial source"
            )
        if self.source_level > 1_000_000:
            raise ValueError(
                "radial occurrence exponent exceeds its explicit integer budget"
            )
        k = 1 << self.source_level
        return RadialSturmianClock(HomogeneousGrowthScale(k, k))

    def observe_mersenne_sources(
        self,
        moduli: tuple[int, ...] = DEFAULT_MERSENNE_MODULI,
    ) -> MersenneTerminalSourceObservations:
        """Source-native low-radix norm-one trace and innovation borrows.

        Only source matrix arithmetic modulo the admitted *small moduli* is
        performed.  This is never a Lucas--Lehmer replay modulo the candidate.
        """
        if self.family != "mersenne":
            raise ValueError("Mersenne trace source is not a Fermat exponential")
        if (
            type(moduli) is not tuple
            or not moduli
            or len(moduli) > 8
            or len(set(moduli)) != len(moduli)
        ):
            raise ValueError("invalid Mersenne source moduli")
        if self.last_four_source_levels[0] < 0:
            raise ValueError("Mersenne source lacks four predecessor levels")
        rows = tuple(
            tuple(_source_residue("mersenne", level, modulus)[0] for modulus in moduli)
            for level in self.last_four_source_levels
        )
        return MersenneTerminalSourceObservations(self, moduli, rows)

    @property
    def missing_proofs(self) -> tuple[str, str]:
        return (SOURCE_TO_FOLD_GAP, FOLD_TO_THRESHOLD_GAP)

    def observe_fermat_sources(
        self,
        demands: tuple[tuple[int, int], ...] = DEFAULT_RADIX_DEMANDS,
        *,
        moving_width: int = 12,
        max_level: int = MAX_EXPLICIT_OBSERVED_LEVEL,
    ) -> FermatTerminalSourceObservations:
        """Demand five exact finite-source packets, never an eager fold.

        The bound is deliberately explicit: the production prime query only
        issues this symbolic demand.  An investigation may elect to pay for
        finite CRT/carry/Walsh outputs at each of its last five source levels.
        """
        if self.family != "fermat":
            raise ValueError("Fermat three-power source is not a Mersenne trace")
        if type(max_level) is not int or max_level < 1 or self.source_level > max_level:
            raise ValueError("explicit finite-source observer level budget exceeded")
        if self.last_four_source_levels[0] < 1:
            raise ValueError("terminal source lacks four predecessor levels")
        observations = tuple(
            demand_three_power_joint_quotient(
                self.parameter, t, demands, moving_width=moving_width
            )
            for t in self.last_four_source_levels
        )
        return FermatTerminalSourceObservations(self, observations)


@dataclass(frozen=True, slots=True)
class FermatTerminalSourceObservations:
    """All five real source-observer packets, but no *signed-fold* producer."""

    demand: SourceTerminalDemand
    sources: tuple[ThreePowerJointQuotient, ...]

    def __post_init__(self) -> None:
        if (
            type(self.demand) is not SourceTerminalDemand
            or self.demand.family != "fermat"
            or type(self.sources) is not tuple
            or len(self.sources) != 5
        ):
            raise ValueError("missing five Fermat source observations")
        for level, packet in zip(
            self.demand.last_four_source_levels, self.sources, strict=True
        ):
            if (
                type(packet) is not ThreePowerJointQuotient
                or packet.index != self.demand.parameter
                or packet.level != level
            ):
                raise ValueError(
                    "foreign or unauthenticated terminal source observation"
                )

    @property
    def absolute_moving_h5(self) -> tuple[WalshH5 | None, ...]:
        """Project absolute-position H5 only on request, without hidden state."""
        return tuple(moving_walsh_h5(packet) for packet in self.sources)

    def finite_crt_ambiguity(self) -> tuple[int, int]:
        """Construct two globally different lifts of the same local CRT data.

        Only a proof about finite-observer insufficiency. These integers are
        NOT certified to be 3**(2**t), and are never used as candidate values.
        They show why projecting a guessed prime bit out of the finite CRT is
        unsound even when the Walsh and pivot ports are perfectly consistent.
        """
        n = self.demand.parameter
        if n > 10:
            raise ValueError("CRT alias construction exceeds explicit width budget")
        modulus = (1 << (1 << n)) + 1
        packet = self.sources[-1]
        m = packet.crt_modulus
        base = packet.crt_source
        zero_join = join_congruences((base, m), (0, modulus))
        minus_one_join = join_congruences((base, m), (modulus - 1, modulus))
        if zero_join is None or minus_one_join is None:
            raise ValueError(
                "finite CRT and candidate residue demands are inconsistent"
            )
        zero, _ = zero_join
        minus_one, _ = minus_one_join
        if (
            zero % m != base
            or minus_one % m != base
            or zero % modulus != 0
            or minus_one % modulus != modulus - 1
        ):
            raise ArithmeticError("constructed CRT ambiguity is inconsistent")
        return zero, minus_one

    @property
    def signed_fold_births_authenticated(self) -> bool:
        return False

    def moving_unit_fold_edits(self) -> tuple[int | None, ...]:
        """Exact *partial* Fermat-fold corrections from authenticated run pivots.

        For each selected aligned-unit window, evaluate the entire XOR-run
        action with only run endpoints, using 2**w == -1 (mod F_n). This is a
        genuine projection into the global Fermat ring, not a base-2 lookup or
        an invented source successor. Unobserved bits of u_t/u_(t+1) remain
        unconstrained, so these corrections never authorize a prime decision.
        """
        width = self.demand.candidate_width
        modulus = (1 << width) + 1

        def phase(position: int) -> int:
            block, remaining = divmod(position, width)
            value = 1 << remaining
            return value if not block & 1 else -value

        answers: list[int | None] = []
        for packet in self.sources:
            moving = packet.moving_unit_xor
            if moving is None:
                answers.append(None)
                continue
            total = 0
            for run in moving.runs:
                sign = 1 if run.expected_bit == 0 else -1
                total += sign * (
                    phase(run.unit_start + run.length) - phase(run.unit_start)
                )
            result = total % modulus
            literal = (
                (moving.next_bits - moving.current_bits) << moving.unit_offset
            ) % modulus
            if result != literal:
                raise ArithmeticError(
                    "guarded moving XOR does not equal its folded edit"
                )
            answers.append(result)
        return tuple(answers)

    @property
    def source_to_global_fold_proven(self) -> bool:
        # The observed multiradix/CRT and moving Walsh packets are exact, but
        # no implementation generates their authentic Fermat-signed seam.
        return False

    @property
    def terminal_status(self) -> str:
        return "UNKNOWN"

    @property
    def missing_proofs(self) -> tuple[str, str]:
        return self.demand.missing_proofs


@dataclass(frozen=True, slots=True)
class MersenneTerminalSourceObservations:
    """Exact finite-ring trace observations, not cyclic candidate residues."""

    demand: SourceTerminalDemand
    moduli: tuple[int, ...]
    source_rows: tuple[tuple[int, ...], ...]

    def __post_init__(self) -> None:
        if (
            type(self.demand) is not SourceTerminalDemand
            or self.demand.family != "mersenne"
            or len(self.source_rows) != 5
            or type(self.moduli) is not tuple
            or not self.moduli
        ):
            raise ValueError("missing five Mersenne source rows")
        for level, residues in zip(
            self.demand.last_four_source_levels, self.source_rows, strict=True
        ):
            if len(residues) != len(self.moduli):
                raise ValueError("incomplete Mersenne prime-radix ports")
            for modulus, residue in zip(self.moduli, residues, strict=True):
                if residue != _source_residue("mersenne", level, modulus)[0]:
                    raise ValueError(
                        "source trace does not match powered norm-one matrix"
                    )

    @property
    def innovation_borrows(self) -> tuple[tuple[int, ...], ...]:
        """Four consecutive source differences, with exact radix boundaries."""
        return tuple(
            tuple(int(after < before) for before, after in zip(a, b, strict=True))
            for a, b in zip(self.source_rows[:-1], self.source_rows[1:], strict=True)
        )

    @property
    def source_to_global_fold_proven(self) -> bool:
        return False

    @property
    def terminal_status(self) -> str:
        return "UNKNOWN"

    @property
    def missing_proofs(self) -> tuple[str, str]:
        return self.demand.missing_proofs


__all__ = [
    "FOLD_TO_THRESHOLD_GAP",
    "HALO_BOUNDARIES",
    "SOURCE_TO_FOLD_GAP",
    "FermatTerminalSourceObservations",
    "MersenneTerminalSourceObservations",
    "SourceTerminalDemand",
    "moving_walsh_h5",
]
