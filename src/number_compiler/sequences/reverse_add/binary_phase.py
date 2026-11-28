"""Source-certified four-phase binary reverse/add grammar (k >= 2).
The exponent is a physical run length, not a replay or countdown.
"""

from __future__ import annotations

from collections.abc import Iterator, Sequence
from dataclasses import dataclass
from itertools import groupby, repeat

# Exact observations of the common modular action. Columns are u,v,w,1.
PORT_NAMES = (
    "source",
    "reversed",
    "or_overlap",
    "or_flipped_on",
    "or_opposite_flipped_on",
    "xor_on",
    "xor_off",
    "ripple_carry",
    "successor",
)
_PORT_ROWS = (
    (
        (-3, 3, -3, 0),
        (12, 0, 6, -3),
        (9, 0, 5, 0),
        (3, 0, 1, -3),
        (-12, 3, -8, 0),
        (1, 1, 3, -3),
        (-11, 1, -3, 0),
        (-2, 2, -6, 0),
        (9, 3, 3, -3),
    ),
    (
        (9, 3, 3, -3),
        (-15, 3, -6, 3),
        (0, 2, 2, 1),
        (-15, 1, -8, 2),
        (9, 1, 1, -4),
        (-14, 5, -3, 0),
        (1, 2, 3, -3),
        (4, 4, 6, -2),
        (-6, 6, -3, 0),
    ),
)


@dataclass(frozen=True, slots=True)
class BinaryMooreAction:
    """Nine set/carry port observations plus carry phase, no occurrence ID."""

    modulus: int
    carry: int
    u: int
    v: int
    w: int

    def __post_init__(self) -> None:
        if (
            type(self.modulus) is not int
            or self.modulus < 1
            or type(self.carry) is not int
            or self.carry not in (0, 1)
            or any(
                type(x) is not int or not 0 <= x < self.modulus
                for x in (self.u, self.v, self.w)
            )
        ):
            raise ValueError("invalid modular binary action")

    def jump(self, steps: int) -> BinaryMooreAction:
        if type(steps) is not int or steps < 0:
            raise ValueError("invalid binary action extent")
        blocks, tail = divmod(steps, 4)
        m = self.modulus
        t = pow(2, blocks, m)
        u, v, w = self.u * t % m, self.v * t * t % m, self.w * t % m
        p = self.carry + tail
        for _ in range(p // 2):  # at most two residual half returns
            u, v, w = w, 2 * v % m, 2 * u % m
        return BinaryMooreAction(m, p % 2, u, v, w)

    def ports(self) -> tuple[int, ...]:
        return tuple(
            (a * self.u + b * self.v + c * self.w + d) % self.modulus
            for a, b, c, d in _PORT_ROWS[self.carry]
        )


@dataclass(frozen=True, slots=True)
class BinaryPhase:
    k: int
    phase: int

    def __post_init__(self) -> None:
        if (
            type(self.k) is not int
            or self.k < 2
            or type(self.phase) is not int
            or not 0 <= self.phase < 4
        ):
            raise ValueError("outside certified binary grammar")

    def jump(self, steps: int) -> BinaryPhase:
        if type(steps) is not int or steps < 0:
            raise ValueError("invalid binary action extent")
        q, p = divmod(self.phase + steps, 4)
        return BinaryPhase(self.k + q, p)

    def runs(self) -> tuple[tuple[int, int], ...]:
        k = self.k
        if self.phase in (0, 2):
            return (
                (1, 1),
                (0, 1),
                (1, k + 1),
                (0, 1),
                (1, 1),
                (0, k + 1 + (self.phase == 2)),
            )
        if self.phase == 1:
            return ((1, 2), (0, k - 1), (1, 1), (0, 3), (1, k - 1), (0, 1), (1, 1))
        return ((1, 2), (0, k + 1), (1, 1), (0, 1), (1, k), (0, 1), (1, 1))

    @property
    def width(self) -> int:
        return 2 * self.k + 6 + (self.phase >= 2)

    def digit(self, position: int) -> int:
        if not 0 <= position < self.width:
            raise IndexError(position)
        for bit, count in reversed(self.runs()):
            if position < count:
                return bit
            position -= count
        raise AssertionError("binary grammar width mismatch")

    def iter_digits(self) -> Iterator[int]:
        for bit, count in reversed(self.runs()):
            while count:  # Only when actual expanded output is demanded.
                chunk = min(count, 1 << 30)
                yield from repeat(bit, chunk)
                count -= chunk

    def modular_action(self, modulus: int) -> BinaryMooreAction:
        if type(modulus) is not int or modulus < 1:
            raise ValueError("positive modulus required")
        t = pow(2, self.k, modulus)
        u, v, w = (2 * t, 16 * t * t, 0) if self.phase < 2 else (0, 32 * t * t, 4 * t)
        return BinaryMooreAction(
            modulus, self.phase % 2, u % modulus, v % modulus, w % modulus
        )

    def residue(self, modulus: int) -> int:
        return self.modular_action(modulus).ports()[0]


def recognize(digits: Sequence[int]) -> BinaryPhase | None:
    """Recognize any exact member, without exploring a future orbit."""
    if len(digits) < 10 or digits[-1] != 1:
        return None
    k = (len(digits) - 6) // 2
    start = 0 if len(digits) % 2 == 0 else 2
    actual: list[tuple[int, int]] = []
    for bit, group in groupby(reversed(digits)):
        actual.append((bit, sum(1 for _ in group)))
        if len(actual) > 7:
            return None
    for p in (start, start + 1):
        candidate = BinaryPhase(k, p)
        if candidate.runs() == tuple(actual):
            return candidate
    return None


def admit(digits: Sequence[int], steps: int) -> BinaryPhase | None:
    phase = recognize(digits)
    if phase is not None:
        return phase.jump(steps)
    # Fixed finite entry equations, checked independently in the regression.
    # T^8(22)=744; T^21(1)=48960. No replay on an admitted request.
    if len(digits) == 5 and tuple(digits) == (0, 1, 1, 0, 1) and steps >= 8:
        return BinaryPhase(2, 0).jump(steps - 8)
    if len(digits) == 1 and digits[0] == 1 and steps >= 21:
        return BinaryPhase(5, 0).jump(steps - 21)
    return None


def recognize_packed(value: int) -> BinaryPhase | None:
    """Exact polynomial guard on a bounded packed physical source."""
    width = value.bit_length()
    if width < 10:
        return None
    k = (width - 6) // 2
    t = 1 << k
    start = 0 if width % 2 == 0 else 2
    if start == 0:
        candidates = (48 * t * t - 6 * t, 48 * t * t + 18 * t - 3)
    else:
        candidates = (96 * t * t - 12 * t, 96 * t * t + 12 * t - 3)
    for p, candidate in enumerate(candidates, start):
        if value == candidate:
            return BinaryPhase(k, p)
    return None
