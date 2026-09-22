"""Powered F5 x F2 cocycle tables for decimal reverse/add.

This module is discovery infrastructure, not a production temporal owner.  It
measures the exact block action

    alpha'   = L5(q,r) alpha   + F5
    epsilon' = L2(q,r) epsilon + F2

for power-of-two temporal blocks.  The nonlinear forcing ``F5``/``F2`` is the
*whole block* residual; no list of the block's primitive carry fields is part of
its identity.

Every output coordinate is accompanied by the exact decimal carrier

    S = alpha + 5 beta + 10 nu

and by the physical forward carry law

    C[i+1] = C[i] if S[i] == 9 else nu[i].

The tables are intended to expose candidate temporal quotients and collision
witnesses before any production claim is made.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import comb
from collections.abc import Iterable

from number_compiler.arithmetic.formula.decimal_pair_coordinates import (
    decimal_pair_coordinates,
)
from number_compiler.arithmetic.polynomials.f2_transport import F2SpatialTransport
from number_compiler.arithmetic.polynomials.f5_transport import F5SpatialTransport


@dataclass(frozen=True, slots=True)
class PairOrbitRow:
    time: int
    value: int
    pair: tuple[int, ...]

    @property
    def width(self) -> int:
        return len(self.pair)


@dataclass(frozen=True, slots=True)
class PoweredCocycleBlock:
    start: int
    steps: int
    end: int
    source_width: int
    target_width: int
    no_growths: int
    growths: int
    f5_forcing: tuple[int, ...]
    f2_forcing: tuple[int, ...]
    source_alpha: tuple[int, ...]
    source_epsilon: tuple[int, ...]
    target_alpha: tuple[int, ...]
    target_epsilon: tuple[int, ...]
    target_pair: tuple[int, ...]
    growth_word: tuple[int, ...]

    @property
    def f5_factors(self) -> tuple[tuple[int, int], ...]:
        return F5SpatialTransport(self.no_growths, self.growths).frobenius_factors()

    @property
    def f2_factors(self) -> tuple[tuple[int, int], ...]:
        return F2SpatialTransport(self.no_growths, self.growths).frobenius_factors()


@dataclass(frozen=True, slots=True)
class CarrierCoordinate:
    start: int
    steps: int
    end: int
    index: int
    x: int
    no_growths: int
    growths: int
    symbol: int
    alpha: int
    beta: int
    nu: int
    epsilon: int
    carry_in: int
    carry_out: int
    domain: str
    f5_linear: int
    f5_forcing: int
    f2_linear: int
    f2_forcing: int

    @property
    def reduced_cocycle_id(self) -> int:
        """Class in ``0..94`` once the F2 homogeneous source is dead."""
        if self.no_growths < 1:
            raise ValueError(
                "reduced F5 carrier class requires an annihilated F2 source"
            )
        if self.f2_linear != 0 or self.f2_forcing != self.epsilon:
            raise AssertionError(
                "F2 forcing must equal target parity after annihilation"
            )
        return self.symbol * 5 + self.f5_forcing


def cocycle_word(block: PoweredCocycleBlock) -> tuple[int, ...]:
    """Carry-free local alphabet on an already supplied output field.

    Incoming carry is a prefix action of the threshold grammar, not part of
    this alphabet. Supplying the output field is still a construction cost.
    """
    if block.no_growths < 1:
        raise ValueError("reduced F5 carrier class requires an annihilated F2 source")
    if block.f2_forcing != block.target_epsilon:
        raise ValueError("F2 forcing must equal target parity after annihilation")
    return tuple(
        5 * symbol + forcing
        for symbol, forcing in zip(block.target_pair, block.f5_forcing, strict=True)
    )


def reverse_add_pair_orbit(seed: int, steps: int) -> tuple[PairOrbitRow, ...]:
    if type(seed) is not int or seed < 0:
        raise ValueError(seed)
    if type(steps) is not int or steps < 0:
        raise ValueError(steps)
    value = seed
    out: list[PairOrbitRow] = []
    for time in range(steps + 1):
        digits = tuple(int(ch) for ch in reversed(str(value)))
        width = len(digits)
        pair = tuple(digits[i] + digits[width - 1 - i] for i in range(width))
        out.append(PairOrbitRow(time, value, pair))
        if time != steps:
            value += int(str(value)[::-1])
    return tuple(out)


def _alpha(pair: Iterable[int]) -> tuple[int, ...]:
    return tuple(int(symbol) % 5 for symbol in pair)


def _epsilon(pair: Iterable[int]) -> tuple[int, ...]:
    return tuple(int(symbol) % 2 for symbol in pair)


def _apply_f5(values: tuple[int, ...], q: int, r: int) -> tuple[int, ...]:
    target_width = len(values) + r
    return tuple(
        sum(
            pow(2, q, 5) * comb(r, shift) * values[i - shift]
            for shift in range(r + 1)
            if 0 <= i - shift < len(values)
        )
        % 5
        for i in range(target_width)
    )


def _apply_f2(values: tuple[int, ...], q: int, r: int) -> tuple[int, ...]:
    target_width = len(values) + r
    return tuple(
        sum(
            (int(q == 0) * comb(r, shift)) * values[i - shift]
            for shift in range(r + 1)
            if 0 <= i - shift < len(values)
        )
        % 2
        for i in range(target_width)
    )


def powered_block(
    orbit: tuple[PairOrbitRow, ...], start: int, steps: int
) -> PoweredCocycleBlock:
    if type(start) is not int or type(steps) is not int or start < 0 or steps < 1:
        raise ValueError((start, steps))
    end = start + steps
    if end >= len(orbit):
        raise IndexError((start, steps, len(orbit)))
    source = orbit[start]
    target = orbit[end]
    r = target.width - source.width
    q = steps - r
    if r < 0 or q < 0:
        raise AssertionError((start, steps, source.width, target.width))
    growth_word = tuple(orbit[t + 1].width - orbit[t].width for t in range(start, end))
    if sum(growth_word) != r or any(bit not in (0, 1) for bit in growth_word):
        raise AssertionError((start, steps, growth_word, r))

    source_alpha = _alpha(source.pair)
    source_epsilon = _epsilon(source.pair)
    target_alpha = _alpha(target.pair)
    target_epsilon = _epsilon(target.pair)
    linear5 = _apply_f5(source_alpha, q, r)
    linear2 = _apply_f2(source_epsilon, q, r)
    f5 = tuple((b - a) % 5 for a, b in zip(linear5, target_alpha, strict=True))
    f2 = tuple(a ^ b for a, b in zip(linear2, target_epsilon, strict=True))
    return PoweredCocycleBlock(
        start,
        steps,
        end,
        source.width,
        target.width,
        q,
        r,
        f5,
        f2,
        source_alpha,
        source_epsilon,
        target_alpha,
        target_epsilon,
        target.pair,
        growth_word,
    )


def carrier_coordinates(block: PoweredCocycleBlock) -> tuple[CarrierCoordinate, ...]:
    linear5 = _apply_f5(block.source_alpha, block.no_growths, block.growths)
    linear2 = _apply_f2(block.source_epsilon, block.no_growths, block.growths)
    carry = 0
    rows: list[CarrierCoordinate] = []
    for i, symbol in enumerate(block.target_pair):
        alpha, beta, nu = decimal_pair_coordinates(symbol)
        epsilon = symbol % 2
        carry_in = carry
        carry_out = carry if symbol == 9 else nu
        domain = "EQ" if symbol == 9 else "GT" if nu else "LT"
        if symbol != alpha + 5 * beta + 10 * nu:
            raise AssertionError((symbol, alpha, beta, nu))
        if carry_out != (carry_in if symbol == 9 else nu):
            raise AssertionError((symbol, carry_in, carry_out, nu))
        if (linear5[i] + block.f5_forcing[i]) % 5 != alpha:
            raise AssertionError((block.start, block.steps, i, "F5"))
        if linear2[i] ^ block.f2_forcing[i] != epsilon:
            raise AssertionError((block.start, block.steps, i, "F2"))
        rows.append(
            CarrierCoordinate(
                block.start,
                block.steps,
                block.end,
                i,
                2 * i - (block.target_width - 1),
                block.no_growths,
                block.growths,
                symbol,
                alpha,
                beta,
                nu,
                epsilon,
                carry_in,
                carry_out,
                domain,
                linear5[i],
                block.f5_forcing[i],
                linear2[i],
                block.f2_forcing[i],
            )
        )
        carry = carry_out
    return tuple(rows)


def compose_forcing(
    left: PoweredCocycleBlock, right: PoweredCocycleBlock
) -> tuple[tuple[int, ...], tuple[int, ...]]:
    if left.end != right.start or left.target_width != right.source_width:
        raise ValueError("powered cocycle blocks are not chronologically adjacent")
    transported5 = _apply_f5(left.f5_forcing, right.no_growths, right.growths)
    transported2 = _apply_f2(left.f2_forcing, right.no_growths, right.growths)
    if len(transported5) != len(right.f5_forcing):
        raise AssertionError("F5 forcing alignment failure")
    if len(transported2) != len(right.f2_forcing):
        raise AssertionError("F2 forcing alignment failure")
    return (
        tuple((a + b) % 5 for a, b in zip(transported5, right.f5_forcing, strict=True)),
        tuple(a ^ b for a, b in zip(transported2, right.f2_forcing, strict=True)),
    )


def verify_square(orbit: tuple[PairOrbitRow, ...], start: int, half_steps: int) -> bool:
    left = powered_block(orbit, start, half_steps)
    right = powered_block(orbit, start + half_steps, half_steps)
    full = powered_block(orbit, start, 2 * half_steps)
    f5, f2 = compose_forcing(left, right)
    return (
        f5 == full.f5_forcing
        and f2 == full.f2_forcing
        and left.no_growths + right.no_growths == full.no_growths
        and left.growths + right.growths == full.growths
    )


__all__ = [
    "CarrierCoordinate",
    "PairOrbitRow",
    "PoweredCocycleBlock",
    "carrier_coordinates",
    "compose_forcing",
    "powered_block",
    "reverse_add_pair_orbit",
    "verify_square",
]
