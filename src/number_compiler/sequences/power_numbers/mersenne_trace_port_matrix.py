"""Selected-source Mersenne norm-one trace-squaring matrix and ports.

For candidate exponent ``p``, the trace seed is ``2*(2**p-1)`` reduced modulo
the requested radix power; the candidate integer is never materialized.
``A=[[trace,-1],[1,0]]`` has determinant one, so
``Tr(A**(2**t))`` obeys ``T'=T*T-2``. This is a bounded source observer, not a
Lucas-Lehmer primality certificate. Clock orbits start at the selected source
residues and are checked against their exact recurrence.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from typing import cast

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
from number_compiler.sequences.power_numbers.source_matrix import (
    checked_dyadic_matrix_power,
)
from number_compiler.sequences.power_numbers.temporal_matrix_support import (
    dyadic_puncture_offsets,
    join_puncture_provenance,
)

MAX_TRACE_STEPS = 4096
MAX_TRACE_POSITION = 64
MAX_TRACE_DETAIL_STEPS = 64
TRACE_BASES = frozenset((2, 5, 7, 10))


class MersenneClockId(Enum):
    """Canonical Mersenne clock identities with stable packet labels."""

    _value_: tuple[int, str]

    BINARY_4_DIGITS = (16, "M2-16")
    DECIMAL_2_DIGITS = (100, "M10-C4")
    DECIMAL_3_DIGITS = (1000, "M10-C20")
    DECIMAL_4_DIGITS = (10000, "M10-C100")
    QUINARY_CUBED = (125, "M5-125")
    SEPTENARY_SQUARED = (49, "M7-49")
    UNDENARY_SQUARED = (121, "M11-121")
    MOD_99 = (99, "M99")
    MOD_198 = (198, "M198")
    MOD_9900 = (9900, "M9900")

    @property
    def modulus(self) -> int:
        return self._value_[0]

    @property
    def display_label(self) -> str:
        return self._value_[1]


def _factor_base(base: int) -> tuple[int, ...]:
    if base == 2:
        return (2,)
    if base == 5:
        return (5,)
    if base == 7:
        return (7,)
    if base == 10:
        return (2, 5)
    raise ValueError("unknown norm-one trace base")


def sl2_order_upper(base: int, places: int) -> int:
    """Return the CRT-derived proposed period for an SL2 modular matrix."""
    if (
        type(base) is not int
        or base not in TRACE_BASES
        or type(places) is not int
        or not 1 <= places <= MAX_TRACE_POSITION + 1
    ):
        raise ValueError("norm-one trace place budget exceeded")
    modulus = base**places
    order: int = cast(int, modulus**3)
    for prime in _factor_base(base):
        order = order // (prime * prime) * (prime * prime - 1)
    return order


def trace_squaring_power(
    start: int,
    steps: int,
    base: int,
    places: int,
) -> int:
    """P_(2**steps)(start) mod b**places in O(log(|SL2|)) joins.

    Cayley-Hamilton gives Tr(A(x)**(2**s))=f**s(x). The proposed period
    is checked by exact powering against this selected matrix before any
    exponent reduction; callers repeat that check for every conditional input.
    """
    if type(start) is not int or type(steps) is not int or steps < 0:
        raise ValueError("nonintegral or negative norm-one trace source")
    if type(base) is not int or base not in TRACE_BASES:
        raise ValueError("unsupported norm-one trace radix")
    if steps > MAX_TRACE_STEPS:
        raise ValueError("trace squaring duration exceeds bounded horizon")
    if type(places) is not int or not 1 <= places <= MAX_TRACE_POSITION + 1:
        raise ValueError("norm-one trace place budget exceeded before allocation")
    modulus = base**places
    matrix = (start % modulus, modulus - 1, 1, 0)
    proposed_period = sl2_order_upper(base, places)
    product, _scalar_compositions, _matrix_compositions = checked_dyadic_matrix_power(
        matrix, steps, modulus, proposed_period
    )
    return cast(int, (product[0] + product[3]) % modulus)


@dataclass(frozen=True, slots=True)
class CertifiedTraceClock:
    identity: MersenneClockId
    preperiod: int
    period: int
    orbit: tuple[int, ...]

    @property
    def modulus(self) -> int:
        return self.identity.modulus

    @property
    def name(self) -> str:
        return self.identity.display_label

    def at(self, tick: int) -> int:
        if type(tick) is not int or tick < 0:
            raise ValueError("invalid norm-one physical clock tick")
        index = (
            tick
            if tick < self.preperiod
            else (self.preperiod + (tick - self.preperiod) % self.period)
        )
        return self.orbit[index]


def _certify_trace_clock(
    identity: MersenneClockId, source_trace: int
) -> CertifiedTraceClock:
    if type(identity) is not MersenneClockId:
        raise ValueError("unregistered norm-one modular clock")
    modulus = identity.modulus
    if type(source_trace) is not int or not 0 <= source_trace < modulus:
        raise ValueError("trace clock requires a reduced source root")
    seen: dict[int, int] = {}
    sequence: list[int] = []
    value = source_trace
    while value not in seen:
        if len(sequence) >= modulus:
            raise ArithmeticError("finite trace clock did not close")
        seen[value] = len(sequence)
        sequence.append(value)
        value = (value * value - 2) % modulus
    mu = seen[value]
    lam = len(sequence) - mu
    if (
        not 0 <= mu < len(sequence)
        or lam < 1
        or value != sequence[mu]
        or any(
            (sequence[i] * sequence[i] - 2) % modulus
            != (sequence[i + 1] if i + 1 < len(sequence) else sequence[mu])
            for i in range(len(sequence))
        )
    ):
        raise ArithmeticError("norm-one source cycle not successor closed")
    return CertifiedTraceClock(identity, mu, lam, tuple(sequence))


@dataclass(frozen=True, slots=True, weakref_slot=True)
class MersenneTraceMacro:
    candidate_exponent: int
    source_trace_residues: tuple[tuple[MersenneClockId, int], ...]
    clocks: tuple[CertifiedTraceClock, ...]
    _issuer: object = field(default=None, init=False, repr=False, compare=False)

    def issuer_payload(self) -> tuple[object, ...]:
        return self.candidate_exponent, self.source_trace_residues, self.clocks

    @property
    def producer_verified(self) -> bool:
        return harmonic_verified(
            self, self.issuer_payload(), issuer=_TRACE_MACRO_ISSUER
        )

    def puncture(self, tick: int) -> tuple[tuple[MersenneClockId, int], ...]:
        if not self.producer_verified:
            raise ValueError("unissued Mersenne source clock")
        values = tuple((clock.identity, clock.at(tick)) for clock in self.clocks)
        by_identity = dict(values)
        if (
            by_identity[MersenneClockId.MOD_9900] % MersenneClockId.MOD_99.modulus
            != by_identity[MersenneClockId.MOD_99]
            or by_identity[MersenneClockId.MOD_9900]
            % MersenneClockId.DECIMAL_2_DIGITS.modulus
            != by_identity[MersenneClockId.DECIMAL_2_DIGITS]
            or by_identity[MersenneClockId.MOD_9900] % MersenneClockId.MOD_198.modulus
            != by_identity[MersenneClockId.MOD_198]
            or by_identity[MersenneClockId.MOD_198] % MersenneClockId.MOD_99.modulus
            != by_identity[MersenneClockId.MOD_99]
            or by_identity[MersenneClockId.DECIMAL_3_DIGITS]
            % MersenneClockId.QUINARY_CUBED.modulus
            != by_identity[MersenneClockId.QUINARY_CUBED]
            or by_identity[MersenneClockId.DECIMAL_4_DIGITS]
            % MersenneClockId.DECIMAL_3_DIGITS.modulus
            != by_identity[MersenneClockId.DECIMAL_3_DIGITS]
            or by_identity[MersenneClockId.DECIMAL_4_DIGITS]
            % MersenneClockId.BINARY_4_DIGITS.modulus
            != by_identity[MersenneClockId.BINARY_4_DIGITS]
        ):
            raise ArithmeticError("trace CRT/odd-lift modular clocks disagree")
        return values

    def source_trace(self, base: int, places: int) -> int:
        """Return ``2*M_p`` modulo the selected positional modulus."""
        if not self.producer_verified:
            raise ValueError("unissued Mersenne source root")
        if (
            type(base) is not int
            or base not in TRACE_BASES
            or type(places) is not int
            or not 1 <= places <= MAX_TRACE_POSITION + 1
        ):
            raise ValueError("Mersenne source radix extent exceeds its bound")
        modulus = base**places
        return cast(int, (2 * (pow(2, self.candidate_exponent, modulus) - 1)) % modulus)


_TRACE_MACRO_ISSUER = new_harmonic_issuer(MersenneTraceMacro)


def issue_mersenne_trace_macro(exponent: int) -> MersenneTraceMacro:
    if type(exponent) is not int or not 0 <= exponent <= 1_000_000:
        raise ValueError("Mersenne trace candidate extent exceeded")
    residues = tuple(
        (
            identity,
            2 * (pow(2, exponent, identity.modulus) - 1) % identity.modulus,
        )
        for identity in MersenneClockId
    )
    result = MersenneTraceMacro(
        exponent,
        residues,
        tuple(_certify_trace_clock(identity, source) for identity, source in residues),
    )
    issue_harmonic(result, result.issuer_payload(), issuer=_TRACE_MACRO_ISSUER)
    if not result.producer_verified:
        raise ArithmeticError("Mersenne source trace registry issuance failed")
    return result


@dataclass(frozen=True, slots=True)
class TracePortPuncture:
    tick: int
    residue: int
    source_digit: int
    lower_square_carry: int
    lower_borrow: int
    clock_residues: tuple[tuple[MersenneClockId, int], ...]


@dataclass(frozen=True, slots=True, weakref_slot=True)
class MersennePoweredTraceMatrix:
    macro: MersenneTraceMacro = field(repr=False)
    base: int
    position: int
    offset: int
    steps: int
    source_residue: int
    endpoint_residue: int
    conditional_endpoints: tuple[int, ...]
    punctures: tuple[TracePortPuncture, ...]
    _issuer: object = field(default=None, init=False, repr=False, compare=False)

    def issuer_payload(self) -> tuple[object, ...]:
        return (
            self.macro.issuer_payload(),
            self.base,
            self.position,
            self.offset,
            self.steps,
            self.source_residue,
            self.endpoint_residue,
            self.conditional_endpoints,
            self.punctures,
        )

    @property
    def producer_verified(self) -> bool:
        return self.macro.producer_verified and harmonic_verified(
            self, self.issuer_payload(), issuer=_TRACE_MATRIX_ISSUER
        )

    def rebase(self, offset: int) -> MersennePoweredTraceMatrix:
        if not self.producer_verified or type(offset) is not int or offset < 0:
            raise ValueError("invalid Mersenne source clock rebase")
        return _compile(self.macro, self.base, self.position, offset, self.steps)

    def then(self, later: MersennePoweredTraceMatrix) -> MersennePoweredTraceMatrix:
        if not self.producer_verified or not later.producer_verified:
            raise ValueError("unissued Mersenne trace join")
        require_exact_temporal_port_join(
            BorderTemporalSpan(
                FamilyId.MERSENNE,
                self.macro,
                BorderTemporalUnit.TRACE_SQUARING_STEPS,
                self.base,
                self.position,
                self.offset,
                self.steps,
                MAX_TRACE_STEPS,
                MAX_TRACE_STEPS,
                self.source_residue,
                self.endpoint_residue,
            ),
            BorderTemporalSpan(
                FamilyId.MERSENNE,
                later.macro,
                BorderTemporalUnit.TRACE_SQUARING_STEPS,
                later.base,
                later.position,
                later.offset,
                later.steps,
                MAX_TRACE_STEPS,
                MAX_TRACE_STEPS,
                later.source_residue,
                later.endpoint_residue,
            ),
        )
        lower: int = self.base**self.position
        conditional_endpoints = compose_radix_endpoint_rows(
            self.conditional_endpoints,
            later.conditional_endpoints,
            lower_modulus=lower,
            inlet_residue=later.source_residue,
        )
        if (
            conditional_endpoints[self.source_residue // lower]
            != later.endpoint_residue
        ):
            raise ArithmeticError("trace pointed successor is not the joined endpoint")
        if self.punctures[-1] != later.punctures[0]:
            raise ArithmeticError("complete trace puncture disagrees at the join")
        joined = MersennePoweredTraceMatrix(
            self.macro,
            self.base,
            self.position,
            self.offset,
            self.steps + later.steps,
            self.source_residue,
            later.endpoint_residue,
            conditional_endpoints,
            join_puncture_provenance(
                self.punctures,
                later.punctures,
                first_offset=self.offset,
                total_steps=self.steps + later.steps,
            ),
        )
        issue_harmonic(joined, joined.issuer_payload(), issuer=_TRACE_MATRIX_ISSUER)
        if not joined.producer_verified:
            raise ArithmeticError("Mersenne child-summary join publication failed")
        return joined

    def square(self) -> MersennePoweredTraceMatrix:
        if not self.producer_verified or 2 * self.steps > MAX_TRACE_STEPS:
            raise ValueError("Mersenne trace square out of bounds")
        return self.then(self.rebase(self.offset + self.steps))

    def _selected_trace(self) -> dict[str, object]:
        if not self.producer_verified or self.steps > MAX_TRACE_DETAIL_STEPS:
            raise ValueError("Mersenne detailed trace exceeds 64 squaring steps")
        lower, modulus = self.base**self.position, self.base ** (self.position + 1)
        value = self.source_residue
        residues: list[int] = [value]
        digits: list[int] = []
        endpoints: list[int] = []
        carries: list[int] = []
        borrows: list[int] = []
        clocks: list[tuple[tuple[MersenneClockId, int], ...]] = []
        for tick in range(self.steps):
            low = value % lower
            digit = value // lower
            carry = (low * low - 2) // lower
            borrow = int(low * low < 2)
            next_value = (value * value - 2) % modulus
            next_digit = next_value // lower
            predicted = (carry + 2 * digit * low + digit * digit * lower) % self.base
            if predicted != next_digit:
                raise ArithmeticError(
                    "Mersenne detailed carry failed its local recurrence"
                )
            digits.append(digit)
            endpoints.append(next_digit)
            carries.append(carry)
            borrows.append(borrow)
            clocks.append(self.macro.puncture(self.offset + tick))
            value = next_value
            residues.append(value)
        if value != self.endpoint_residue:
            raise ArithmeticError(
                "Mersenne detailed trace differs from powered endpoint"
            )
        return {
            "unit": "trace-squaring-steps",
            "residues": tuple(residues),
            "digits": tuple(digits),
            "endpoint_digits": tuple(endpoints),
            "lower_square_carries": tuple(carries),
            "lower_borrows": tuple(borrows),
            "clock_residues": tuple(
                tuple((identity.display_label, residue) for identity, residue in values)
                for values in clocks
            ),
        }

    def packet(self, *, trace: bool = False) -> dict[str, object]:
        if not self.producer_verified:
            raise ValueError("unissued Mersenne trace matrix")
        if type(trace) is not bool:
            raise TypeError("Mersenne trace demand must be Boolean")
        if trace and self.steps > MAX_TRACE_DETAIL_STEPS:
            raise ValueError("Mersenne chronological trace exceeds 64 squaring steps")
        packet: dict[str, object] = {
            "source_authority": "selected Mersenne source 2*(2^p-1), reduced modulo the requested radix",
            "candidate_exponent": self.macro.candidate_exponent,
            "source_trace": self.macro.source_trace(self.base, self.position + 1),
            "radix": self.base,
            "digit_position": self.position,
            "trace_squaring_steps": self.steps,
            "trace_squaring_offset": self.offset,
            "clock_unit": "trace-squaring-steps",
            "source_residue": self.source_residue,
            "selected_source_digit": self.source_residue // (self.base**self.position),
            "selected_endpoint_residue": self.endpoint_residue,
            "conditional_rows": self.base,
            "conditional_endpoint_residues": self.conditional_endpoints,
            "macro_registry": tuple(c.name for c in self.macro.clocks),
            "modular_clock_periods": tuple(
                (c.name, c.preperiod, c.period) for c in self.macro.clocks
            ),
            "modular_clocks_successor_closed": True,
            "conditional_ports_successor_closed": True,
            "powered_action": "trace((x,-1;1,0)**(2**trace_squaring_steps))",
            "primality_authority": False,
            "complete_cyclic_fold_certified": False,
            "source_index_authority": True,
            "source_integer_materialized": False,
            "trace_status": "requested" if trace else "not-requested",
        }
        if trace:
            trace_packet = self._selected_trace()
            trace_packet["port_punctures"] = tuple(
                {
                    "tick": x.tick,
                    "source_digit": x.source_digit,
                    "source_residue": x.residue,
                    "lower_square_carry": x.lower_square_carry,
                    "lower_borrow": x.lower_borrow,
                    "clocks": tuple(
                        (identity.display_label, residue)
                        for identity, residue in x.clock_residues
                    ),
                }
                for x in self.punctures
            )
            packet["trace"] = trace_packet
        return packet


_TRACE_MATRIX_ISSUER = new_harmonic_issuer(MersennePoweredTraceMatrix)


def _compile(
    macro: MersenneTraceMacro,
    base: int,
    position: int,
    offset: int,
    steps: int,
) -> MersennePoweredTraceMatrix:
    if not macro.producer_verified:
        raise ValueError("unissued Mersenne trace source")
    if (
        type(base) is not int
        or base not in TRACE_BASES
        or type(position) is not int
        or not 0 <= position <= MAX_TRACE_POSITION
        or type(offset) is not int
        or offset < 0
        or type(steps) is not int
        or not 1 <= steps <= MAX_TRACE_STEPS
        or offset + steps > MAX_TRACE_STEPS
    ):
        raise ValueError("Mersenne source trace matrix outside admitted range")
    lower, modulus = base**position, base ** (position + 1)
    initial = macro.source_trace(base, position + 1)
    root = trace_squaring_power(initial, offset, base, position + 1)
    endpoint = trace_squaring_power(root, steps, base, position + 1)
    low = root % lower
    conditional = tuple(
        endpoint
        if d == root // lower
        else trace_squaring_power(low + d * lower, steps, base, position + 1)
        for d in range(base)
    )
    if endpoint != conditional[root // lower]:
        raise ArithmeticError("trace pointed endpoint not in conditional source")
    punctures: list[TracePortPuncture] = []
    for tick in dyadic_puncture_offsets(steps):
        absolute = offset + tick
        if tick == 0:
            value = root
        elif tick == steps:
            value = endpoint
        else:
            value = trace_squaring_power(initial, absolute, base, position + 1)
        clock_values = macro.puncture(absolute)
        for clock in macro.clocks:
            if modulus % clock.modulus == 0 and value % clock.modulus != clock.at(
                absolute
            ):
                raise ArithmeticError("norm-one clock contradicts the trace port")
        source_low = value % lower
        punctures.append(
            TracePortPuncture(
                absolute,
                value,
                value // lower,
                (source_low * source_low - 2) // lower,
                int(source_low * source_low < 2),
                clock_values,
            )
        )
    if punctures[0].residue != root or punctures[-1].residue != endpoint:
        raise ArithmeticError("trace source endpoints are not closed")
    result = MersennePoweredTraceMatrix(
        macro,
        base,
        position,
        offset,
        steps,
        root,
        endpoint,
        conditional,
        tuple(punctures),
    )
    issue_harmonic(result, result.issuer_payload(), issuer=_TRACE_MATRIX_ISSUER)
    if not result.producer_verified:
        raise ArithmeticError("Mersenne trace matrix issuance failed")
    return result


def demand_mersenne_trace_matrix(
    exponent: int,
    steps: int,
    *,
    base: int = 10,
    position: int = 0,
) -> MersennePoweredTraceMatrix:
    """Demand bounded trace-source work, never the candidate Mersenne modulus."""
    if (
        type(exponent) is not int
        or not 0 <= exponent <= 1_000_000
        or type(steps) is not int
        or not 1 <= steps <= MAX_TRACE_STEPS
        or type(base) is not int
        or base not in TRACE_BASES
        or type(position) is not int
        or not 0 <= position <= MAX_TRACE_POSITION
    ):
        raise ValueError("Mersenne trace demand outside matrix budget")
    return _compile(issue_mersenne_trace_macro(exponent), base, position, 0, steps)


__all__ = (
    "CertifiedTraceClock",
    "MersenneClockId",
    "MersennePoweredTraceMatrix",
    "MersenneTraceMacro",
    "demand_mersenne_trace_matrix",
    "issue_mersenne_trace_macro",
    "sl2_order_upper",
    "trace_squaring_power",
)
