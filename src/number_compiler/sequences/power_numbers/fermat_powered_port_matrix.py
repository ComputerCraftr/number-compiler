"""Production Fermat 3X temporal matrix with authenticated, punctured ports.

The finite causal-row diagnostics can cost O(base * steps * digit-depth) and
breach the harmonic snapshot budget.  This operator instead uses the exact
modular action x |-> 3**steps*x modulo b**(position+1).  Conditional digit
rows are represented by their ENDPOINTS, not by materialized full histories.

The registry supplies exact low-prime clocks, a guarded initial radial
language, and independently certified dyadic XOR metadata.  ``then`` checks
both true physical adjacency and every conditional port, and ``square``
issues the actual second-half action.  No root's high radial word, signed
phase histogram, or prime bit is guessed at later ordinary-tripling ticks.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING, cast

from number_compiler.arithmetic.contracts.family_identity import FamilyId
from number_compiler.arithmetic.fields.radix import compose_radix_endpoint_rows
from number_compiler.hashlife.interfaces.border_macros import (
    BorderTemporalSpan,
    BorderTemporalUnit,
    require_exact_temporal_port_join,
)
from number_compiler.sequences.power_numbers._harmonic_authority import (
    harmonic_verified,
    issue_harmonic,
    new_harmonic_issuer,
)
from number_compiler.sequences.power_numbers.fermat_boundary_macros import (
    FermatAlgebraicRoot,
    FermatBorderMacro,
    FermatClockId,
    FermatRadialPort,
    _totient_prime_power_base,
    exact_three_power_residue,
    issue_algebraic_root,
    issue_fermat_border_macro,
)
from number_compiler.sequences.power_numbers.temporal_matrix_support import (
    dyadic_puncture_offsets,
    join_puncture_provenance,
)
from number_compiler.sequences.power_numbers.three_power_signed_border_action import (
    SourceWeightedTriplingAction,
)

if TYPE_CHECKING:
    from number_compiler.sequences.power_numbers.numbers import FermatNumberSpec

MAX_POWERED_PHYSICAL_STEPS = 4096
MAX_POWERED_DIGIT_POSITION = 256
MAX_POWERED_TRACE = 64
_SUPPORTED_BASES = frozenset((2, 5, 7, 10))


def _carry_port(
    value: int, base: int, lower: int, modulus: int
) -> tuple[int, int, int]:
    return (value // lower, 3 * (value % lower) // lower, 3 * value // modulus)


@dataclass(frozen=True, slots=True)
class FermatPuncturedPort:
    """A demand-driven source tick with both sides of the carry boundary."""

    tick: int
    source_digit: int
    carry_in: int
    carry_out: int
    source_residue: int
    clock_residues: tuple[tuple[FermatClockId, int], ...]
    radial: FermatRadialPort


@dataclass(frozen=True, slots=True, weakref_slot=True)
class FermatPoweredPortMatrix:
    """Source-bound affine positional map, not a Fermat-candidate prime test."""

    macro: FermatBorderMacro = field(repr=False)
    base: int
    position: int
    physical_offset: int
    physical_steps: int
    source_residue: int
    endpoint_residue: int
    conditional_endpoints: tuple[int, ...]
    punctures: tuple[FermatPuncturedPort, ...]
    _issuer: object = field(default=None, init=False, repr=False, compare=False)

    def issuer_payload(self) -> tuple[object, ...]:
        return (
            self.macro.issuer_payload(),
            self.base,
            self.position,
            self.physical_offset,
            self.physical_steps,
            self.source_residue,
            self.endpoint_residue,
            self.conditional_endpoints,
            self.punctures,
        )

    @property
    def producer_verified(self) -> bool:
        return self.macro.producer_verified and harmonic_verified(
            self, self.issuer_payload(), issuer=_POWERED_ISSUER
        )

    @property
    def modulus(self) -> int:
        return cast(int, self.base ** (self.position + 1))

    @property
    def lower_modulus(self) -> int:
        return cast(int, self.base**self.position)

    @property
    def selected_digit(self) -> int:
        return self.source_residue // self.lower_modulus

    @property
    def carry_in(self) -> int:
        return _carry_port(
            self.source_residue, self.base, self.lower_modulus, self.modulus
        )[1]

    @property
    def carry_out(self) -> int:
        return _carry_port(
            self.source_residue, self.base, self.lower_modulus, self.modulus
        )[2]

    def rebase(self, offset: int) -> FermatPoweredPortMatrix:
        """Reissue from the SAME root at its true physical successor offset."""
        if not self.producer_verified or type(offset) is not int or offset < 0:
            raise ValueError("rebase requires an issued matrix and positive offset")
        return _compile_at(
            self.macro, self.base, self.position, offset, self.physical_steps
        )

    def then(self, later: FermatPoweredPortMatrix) -> FermatPoweredPortMatrix:
        """Join the true endpoint, carry inlet and every conditional row port."""
        if not self.producer_verified or not later.producer_verified:
            raise ValueError("matrix join requires two issued Fermat actions")
        require_exact_temporal_port_join(
            BorderTemporalSpan(
                FamilyId.FERMAT,
                self.macro,
                BorderTemporalUnit.PHYSICAL_TICKS,
                self.base,
                self.position,
                self.physical_offset,
                self.physical_steps,
                MAX_POWERED_PHYSICAL_STEPS,
                MAX_POWERED_PHYSICAL_STEPS,
                self.source_residue,
                self.endpoint_residue,
            ),
            BorderTemporalSpan(
                FamilyId.FERMAT,
                later.macro,
                BorderTemporalUnit.PHYSICAL_TICKS,
                later.base,
                later.position,
                later.physical_offset,
                later.physical_steps,
                MAX_POWERED_PHYSICAL_STEPS,
                MAX_POWERED_PHYSICAL_STEPS,
                later.source_residue,
                later.endpoint_residue,
            ),
        )
        if (
            self.endpoint_residue % self.lower_modulus
            != later.source_residue % later.lower_modulus
        ):
            raise ValueError("matrix join changes lower carry ingress")
        # Conditional start digits of the second half are determined by the
        # first half's endpoint map, not by the pointed row of the second.
        conditional_endpoints = compose_radix_endpoint_rows(
            self.conditional_endpoints,
            later.conditional_endpoints,
            lower_modulus=self.lower_modulus,
            inlet_residue=later.source_residue,
        )
        if conditional_endpoints[self.selected_digit] != later.endpoint_residue:
            raise ArithmeticError("matrix pointed successor is not the joined endpoint")
        # Puncture coincidence at the join is checked independently against
        # the ordered modular clocks, which also encode the carry inlet.
        if self.punctures[-1] != later.punctures[0]:
            raise ArithmeticError("complete physical puncture disagrees at the join")
        joined = FermatPoweredPortMatrix(
            self.macro,
            self.base,
            self.position,
            self.physical_offset,
            self.physical_steps + later.physical_steps,
            self.source_residue,
            later.endpoint_residue,
            conditional_endpoints,
            join_puncture_provenance(
                self.punctures,
                later.punctures,
                first_offset=self.physical_offset,
                total_steps=self.physical_steps + later.physical_steps,
            ),
        )
        issue_harmonic(joined, joined.issuer_payload(), issuer=_POWERED_ISSUER)
        if not joined.producer_verified:
            raise ArithmeticError("Fermat child-summary join publication failed")
        return joined

    def square(self) -> FermatPoweredPortMatrix:
        """Double physical duration, without rebuilding the signed root."""
        if not self.producer_verified:
            raise ValueError("square requires an issued Fermat temporal matrix")
        if 2 * self.physical_steps > MAX_POWERED_PHYSICAL_STEPS:
            raise ValueError("powered physical duration exceeds production bound")
        later = self.rebase(self.physical_offset + self.physical_steps)
        return self.then(later)

    def power_of_two(self, squarings: int) -> FermatPoweredPortMatrix:
        if type(squarings) is not int or not 0 <= squarings <= 12:
            raise ValueError("invalid Fermat physical squaring count")
        result = self
        for _ in range(squarings):
            result = result.square()
        return result

    def _selected_trace(
        self,
    ) -> tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]]:
        if not self.producer_verified or self.physical_steps > MAX_POWERED_TRACE:
            raise ValueError("full trace exceeds the explicitly bounded view")
        current = self.source_residue
        lower, modulus = self.lower_modulus, self.modulus
        digits: list[int] = []
        incoming: list[int] = []
        outgoing: list[int] = []
        for _ in range(self.physical_steps):
            digit, cin, cout = _carry_port(current, self.base, lower, modulus)
            digits.append(digit)
            incoming.append(cin)
            outgoing.append(cout)
            current = 3 * current % modulus
        digits.append(current // lower)
        if current != self.endpoint_residue:
            raise ArithmeticError("selected trace disagrees with powered endpoint")
        return tuple(digits), tuple(incoming), tuple(outgoing)

    def packet(self, *, trace: bool = False) -> dict[str, object]:
        if not self.producer_verified:
            raise ValueError("unissued Fermat powered port matrix")
        if type(trace) is not bool:
            raise TypeError("Fermat matrix trace demand must be Boolean")
        if trace and self.physical_steps > MAX_POWERED_TRACE:
            raise ValueError("Fermat chronological trace exceeds 64 physical ticks")
        packet: dict[str, object] = {
            "source_authority": (
                "issued Fermat signed bilateral source / border macro"
                if self.macro.radial_guard_verified
                else "issued exact exponent root / low-clock macro; radial unavailable"
            ),
            "source_level": self.macro.source.level,
            "radix": self.base,
            "digit_position": self.position,
            "physical_offset": self.physical_offset,
            "physical_steps": self.physical_steps,
            "source_residue": self.source_residue,
            "selected_source_digit": self.selected_digit,
            "selected_endpoint_residue": self.endpoint_residue,
            "conditional_rows": self.base,
            "conditional_endpoint_residues": self.conditional_endpoints,
            "source_cylinder_verified": (
                type(self.macro.source) is not FermatAlgebraicRoot
            ),
            "source_guard_admitted": True,
            "complete_signed_fold_certified": False,
            "primality_authority": False,
            "macro_registry": self.macro.names,
            "root_radial_word": self.macro.root_radial_word,
            "root_radial_guard": self.macro.radial_guard,
            "root_radial_guard_verified": self.macro.radial_guard_verified,
            "transported_radial_guard": "conservative interval, source-rooted",
            "radial_registered_families": tuple(
                sorted(("139", "13", "14", "15", "26", "27", "28"))
            ),
            "root_binary_LTE_gap": self.macro.binary_gap
            if self.macro.binary_lte_verified
            else None,
            "dyadic_pivot_xor": self.macro.pivot_xor,
            "signed_middle_status": (
                "open; no unknown carry or XOR asserted"
                if self.macro.radial_guard_verified
                else "not-issued; low source only"
            ),
            "physical_clock_status": "closed at every puncture",
            "matrix_join_status": "conditional lower/upper ports successor closed",
            "powered_action": "multiply-by-3**ticks mod radix**(position+1)",
            "powered_endpoint_exponent_bits": self.physical_steps.bit_length(),
            "puncture_count": len(self.punctures),
            "causal_rows_constructed": False,
            "selected_digit_path_status": "requested" if trace else "not-requested",
        }
        if trace:
            digits, cin, cout = self._selected_trace()
            packet["trace"] = {
                "unit": "physical-tripling-ticks",
                "digits": digits,
                "carry_in": cin,
                "carry_out": cout,
                "port_punctures": tuple(
                    {
                        "tick": x.tick,
                        "source_digit": x.source_digit,
                        "carry_in": x.carry_in,
                        "carry_out": x.carry_out,
                        "source_residue": x.source_residue,
                        "clocks": tuple(
                            (identity.display_label, value)
                            for identity, value in x.clock_residues
                        ),
                        "radial_exact_width": x.radial.exact_width,
                        "radial_guaranteed_word": x.radial.guaranteed_word,
                        "radial_guaranteed_places": x.radial.guaranteed_places,
                        "radial_named_family": x.radial.named_family,
                    }
                    for x in self.punctures
                ),
            }
        return packet


_POWERED_ISSUER = new_harmonic_issuer(FermatPoweredPortMatrix)


def _compile_at(
    macro: FermatBorderMacro,
    base: int,
    position: int,
    offset: int,
    steps: int,
) -> FermatPoweredPortMatrix:
    if not macro.producer_verified:
        raise ValueError("unissued source-bound macro")
    if (
        type(base) is not int
        or base not in _SUPPORTED_BASES
        or type(position) is not int
        or not 0 <= position <= MAX_POWERED_DIGIT_POSITION
        or type(offset) is not int
        or offset < 0
        or type(steps) is not int
        or not 1 <= steps <= MAX_POWERED_PHYSICAL_STEPS
        or offset + steps > MAX_POWERED_PHYSICAL_STEPS
        or (base == 7 and position >= 19)
    ):
        raise ValueError("Fermat powered carry request exceeds its admitted domain")
    lower = base**position
    modulus = base ** (position + 1)
    phi = _totient_prime_power_base(base, position + 1)
    source_level: int = macro.source.level
    root: int = exact_three_power_residue(source_level, modulus, phi)
    start = root * int.__pow__(3, offset, modulus) % modulus
    factor = int.__pow__(3, steps, modulus)
    end: int = start * factor % modulus
    low: int = start % lower
    endpoints: tuple[int, ...] = tuple(
        (low + digit * lower) * factor % modulus for digit in range(base)
    )
    selected: int = start // lower
    if endpoints[selected] != end:
        raise ArithmeticError("pointed endpoint disagrees with conditional transfer")
    if offset == 0 and base == 10 and type(macro.source) is not FermatAlgebraicRoot:
        # A high border is a root-only constraint. It never gets silently
        # replayed after the first ordinary tripling.
        signed_source = cast(SourceWeightedTriplingAction, macro.source)
        high_start = (
            signed_source.origin.bilateral.decimal.source_digits - macro.radial_guard[1]
        )
        if (
            position == high_start
            and (3 * (start % lower) // lower) not in macro.radial_guard[2]
        ):
            raise ArithmeticError("root radial carry ingress is forbidden")
    points: list[FermatPuncturedPort] = []
    for tick in dyadic_puncture_offsets(steps):
        absolute = offset + tick
        value = root * int.__pow__(3, absolute, modulus) % modulus
        digit, cin, cout = _carry_port(value, base, lower, modulus)
        clocks = macro.puncture(absolute)
        clock_values = dict(clocks)
        if (
            base == 10
            and position >= 1
            and value % FermatClockId.DECIMAL_2_DIGITS.modulus
            != clock_values[FermatClockId.DECIMAL_2_DIGITS]
        ):
            raise ArithmeticError("decimal clock violates matrix low carry port")
        if (
            base == 10
            and position >= 3
            and value % FermatClockId.DECIMAL_4_DIGITS.modulus
            != clock_values[FermatClockId.DECIMAL_4_DIGITS]
        ):
            raise ArithmeticError("four-digit physical clock violates matrix port")
        if (
            base == 5
            and position >= 2
            and value % FermatClockId.QUINARY_CUBED.modulus
            != clock_values[FermatClockId.QUINARY_CUBED]
        ):
            raise ArithmeticError("5-adic physical clock violates matrix port")
        if (
            base == 7
            and position >= 1
            and value % FermatClockId.SEPTENARY_SQUARED.modulus
            != clock_values[FermatClockId.SEPTENARY_SQUARED]
        ):
            raise ArithmeticError("7-adic physical clock violates matrix port")
        radial = macro.radial_at(absolute)
        points.append(
            FermatPuncturedPort(absolute, digit, cin, cout, value, clocks, radial)
        )
    if points[0].source_residue != start or points[-1].source_residue != end:
        raise ArithmeticError("punctured physical transfer lost endpoint")
    result = FermatPoweredPortMatrix(
        macro,
        base,
        position,
        offset,
        steps,
        start,
        end,
        endpoints,
        tuple(points),
    )
    issue_harmonic(result, result.issuer_payload(), issuer=_POWERED_ISSUER)
    if not result.producer_verified:
        raise ArithmeticError("Fermat powered matrix publication failed")
    return result


def demand_fermat_powered_port_matrix(
    spec: FermatNumberSpec,
    level: int,
    steps: int,
    *,
    base: int = 10,
    position: int = 0,
) -> FermatPoweredPortMatrix:
    """Compile through the registry before choosing the matrix action."""
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )
    from number_compiler.sequences.power_numbers.numbers import FermatNumberSpec

    if type(spec) is not FermatNumberSpec or not 0 <= spec.index <= 16:
        raise ValueError("Fermat powered matrix source index exceeds bound 16")
    if (
        type(level) is not int
        or level != (1 << spec.index) - 1
        or type(steps) is not int
        or not 1 <= steps <= MAX_POWERED_PHYSICAL_STEPS
        or type(base) is not int
        or base not in _SUPPORTED_BASES
        or type(position) is not int
        or not 0 <= position <= MAX_POWERED_DIGIT_POSITION
        or (base == 7 and position >= 19)
    ):
        raise ValueError(
            "Fermat powered matrix exceeds its source/radix/horizon extent"
        )
    # Exactly one source issuer is selected. Prefer the certified two-sided
    # radial owner. A high-prefix arithmetic budget rejection must NOT
    # prevent an independently exact, source-rooted low modular query.
    # That branch explicitly leaves the high ingress and signed middle OPEN.
    source: SourceWeightedTriplingAction | FermatAlgebraicRoot
    if level <= 1:
        source = issue_algebraic_root(spec.index, level)
    else:
        try:
            source = spec.demand_three_power_signed_border_action(
                level,
                phase_binary_places=max(64, position + 1 if base == 2 else 64),
                phase_decimal_places=max(6, position + 1 if base in (5, 10) else 6),
                low_binary_places=1,
                low_decimal_places=1,
                high_binary_places=1,
                high_decimal_places=(3 if level >= 3 else 1),
            )
        except BlockContextBudgetExceeded:
            source = issue_algebraic_root(spec.index, level)
    macro = issue_fermat_border_macro(source)
    if base == 7 and level >= 1:
        multiradix = spec.demand_three_power_multiradix_port(level, 7, position + 1)
        if not multiradix.producer_verified:
            raise ArithmeticError("missing authenticated 7-adic matrix source")
        phi = _totient_prime_power_base(7, position + 1)
        if multiradix.source_residue != exact_three_power_residue(
            level, 7 ** (position + 1), phi
        ):
            raise ArithmeticError("7-adic source port fails CRT/clock join")
    return _compile_at(macro, base, position, 0, steps)


__all__ = (
    "MAX_POWERED_TRACE",
    "FermatPoweredPortMatrix",
    "FermatPuncturedPort",
    "demand_fermat_powered_port_matrix",
)
