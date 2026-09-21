"""Bounded exact clock experiment for scalar radial event packets.

This is not source admission or a temporal constructor. It consumes packets
from the existing innovation representation and refuses unresolved source
atoms. The valuation/gap bound is Theorems 1 and 9 of arXiv:1206.4224.
Zero results additionally require exact sparse cancellation after t=1+z;
exhausting a jet alone never authorizes ZERO.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import comb

from number_compiler.arithmetic.fields.event_innovation import (
    _children,
    _Context,
    normalize_event_sum,
)
from number_compiler.arithmetic.fields.symbolic_innovation import (
    InnovationID,
    SymbolicInnovationArena,
    _Interval,
    _Zero,
)


@dataclass(frozen=True, slots=True)
class ClockLimits:
    max_packets: int = 512
    max_jet_coefficients: int = 4096
    max_integer_bits: int = 65536
    max_integer_work_bits: int = 4_000_000

    def __post_init__(self) -> None:
        for value in (
            self.max_packets,
            self.max_jet_coefficients,
            self.max_integer_bits,
            self.max_integer_work_bits,
        ):
            if type(value) is not int or value <= 0:
                raise ValueError("clock limits must be positive exact integers")


@dataclass(frozen=True, slots=True)
class RadialEventPacket:
    coefficient: int
    shift: int
    growth: int
    no_growth: int = 0

    def __post_init__(self) -> None:
        for value in (self.coefficient, self.shift, self.growth, self.no_growth):
            if type(value) is not int:
                raise TypeError("radial event packet requires exact integers")
        if self.growth < 0 or self.no_growth < 0:
            raise ValueError("radial exponents must be nonnegative")


@dataclass(frozen=True, slots=True)
class ClockWitness:
    prefix: int
    leading: int


@dataclass(slots=True)
class ClockWork:
    """Experimental arithmetic counts, not production-ledger admission."""

    packets: int = 0
    jet_coefficients: int = 0
    zero_blocks: int = 0
    integer_work_bits: int = 0
    peak_sparse_basis_terms: int = 0


def _charge_bits(work: ClockWork, limits: ClockLimits, bits: int) -> None:
    work.integer_work_bits += bits
    if bits > limits.max_integer_bits:
        raise ValueError("radial clock integer budget exhausted")
    if work.integer_work_bits > limits.max_integer_work_bits:
        raise ValueError("radial clock integer work budget exhausted")


def _binomial(n: int, k: int, work: ClockWork, limits: ClockLimits) -> int:
    if not 0 <= k <= n:
        return 0
    _charge_bits(work, limits, max(1, min(k, n - k) * n.bit_length() + 1))
    return comb(n, k)


def expression_packets(
    arena: SymbolicInnovationArena,
    expression: InnovationID,
    *,
    limits: ClockLimits,
) -> tuple[RadialEventPacket, ...]:
    """Read normalized scalar event terms, without any atom-value callback.

    The arena ledger governs normalization allocations. ClockLimits governs
    extracted packets and subsequent arithmetic, not that earlier transaction.
    """
    normal = normalize_event_sum(arena, expression)
    pending = [(1, _Context(normal))]
    packets: list[RadialEventPacket] = []
    while pending:
        weight, state = pending.pop()
        edges = _children(arena, state)
        if edges:
            pending.extend((weight * c, child) for c, child in edges)
            continue
        node = arena.resolve(state.reference)
        if isinstance(node, _Zero):
            continue
        if not isinstance(node, _Interval) or node.length != 1:
            raise ValueError("radial clock needs resolved scalar event atoms")
        if len(packets) >= limits.max_packets:
            raise ValueError("radial clock packet budget exhausted")
        shift = -state.chart.offset * state.chart.slope
        packets.append(
            RadialEventPacket(
                weight, shift, state.radial.growth, state.radial.no_growth
            )
        )
    return tuple(packets)


def _canonical_packets(
    packets: tuple[RadialEventPacket, ...], work: ClockWork, limits: ClockLimits
) -> list[RadialEventPacket]:
    if type(packets) is not tuple or len(packets) > limits.max_packets:
        raise ValueError("radial clock packet budget exhausted")
    combined: dict[tuple[int, int], int] = {}
    for packet in packets:
        if type(packet) is not RadialEventPacket:
            raise TypeError("radial clock requires typed packets")
        packet.__post_init__()
        work.packets += 1
        if not packet.coefficient:
            continue
        bits = abs(packet.coefficient).bit_length() + packet.no_growth
        _charge_bits(work, limits, bits + 1)
        key = packet.shift, packet.growth
        value = packet.coefficient << packet.no_growth
        old = combined.get(key, 0)
        _charge_bits(work, limits, max(abs(old).bit_length(), bits) + 1)
        combined[key] = old + value
    return [
        RadialEventPacket(value, shift, growth)
        for (shift, growth), value in sorted(combined.items())
        if value
    ]


def _bound(packets: list[RadialEventPacket]) -> int:
    size = len(packets)
    return max(
        p.shift + (size - j) * (size - j - 1) // 2 for j, p in enumerate(packets)
    )


def _zero_certificate(
    packets: list[RadialEventPacket], work: ClockWork, limits: ClockLimits
) -> bool:
    """Exact sparse t-basis certificate; no expansion of (1+z)^growth.

    Strip the common z^a, then substitute z=t-1. Only the bounded relative
    shifts expand. A surviving sparse coefficient prevents a ZERO result.
    """
    origin = packets[0].shift
    basis: dict[int, int] = {}
    for packet in packets:
        degree = packet.shift - origin
        if degree + 1 > limits.max_jet_coefficients:
            raise ValueError("radial clock zero-certificate budget exhausted")
        for k in range(degree + 1):
            b = _binomial(degree, k, work, limits)
            bits = abs(packet.coefficient).bit_length() + b.bit_length() + 1
            _charge_bits(work, limits, bits)
            value = packet.coefficient * b * (-1 if (degree - k) % 2 else 1)
            exponent = packet.growth + k
            old = basis.get(exponent, 0)
            _charge_bits(work, limits, max(bits, abs(old).bit_length()) + 1)
            value += old
            if value:
                basis[exponent] = value
            else:
                basis.pop(exponent, None)
            work.peak_sparse_basis_terms = max(work.peak_sparse_basis_terms, len(basis))
    return not basis


def _extract_block(
    packets: list[RadialEventPacket], work: ClockWork, limits: ClockLimits
) -> ClockWitness | None:
    origin, bound = packets[0].shift, _bound(packets)
    count = bound - origin + 1
    if work.jet_coefficients + count > limits.max_jet_coefficients:
        raise ValueError("radial clock jet budget exhausted")
    for position in range(origin, bound + 1):
        work.jet_coefficients += 1
        value = 0
        for packet in packets:
            b = _binomial(packet.growth, position - packet.shift, work, limits)
            bits = abs(packet.coefficient).bit_length() + b.bit_length() + 1
            _charge_bits(work, limits, max(bits, abs(value).bit_length()) + 1)
            value += packet.coefficient * b
        if value:
            return ClockWitness(position, value)
    if not _zero_certificate(packets, work, limits):
        raise ArithmeticError("jet exhausted without an exact zero certificate")
    work.zero_blocks += 1
    return None


def extract_radial_clock(
    packets: tuple[RadialEventPacket, ...],
    *,
    work: ClockWork,
    limits: ClockLimits | None = None,
) -> ClockWitness | None:
    """Return the exact first event or certified zero for supplied scalar packets.

    Gap separation includes later-starting packets before evaluating a jet.
    All exponent arithmetic is exact. Neither a source predicate nor a bound
    on the number of packets created by future temporal actions is inferred.
    """
    if limits is None:
        limits = ClockLimits()
    canonical = _canonical_packets(packets, work, limits)
    block: list[RadialEventPacket] = []
    for packet in canonical:
        if block and packet.shift > _bound(block):
            witness = _extract_block(block, work, limits)
            if witness is not None:
                return witness
            block = []
        block.append(packet)
    return _extract_block(block, work, limits) if block else None
