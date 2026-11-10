"""Controlled mod-11 center/half-word temporal action for reverse/add.

This is a *controlled* Moore output action: the source's symmetric central
coefficient and the two adjoining physical carry ports determine one step.
Once a complete physical port program has been supplied, its 4x4 affine action
on (left_half, reversed_right_half, cumulative_difference, 1) composes and
powers without replaying that program. A modular return is NEVER permission
to repeat the physical port program at a new source.

The normalized half words use exactly the extraction in the NC19 half-sum
experiment: first = int(decimal[:ceil(width/2)]), second =
int(decimal[floor(width/2):][::-1]). For odd widths, they overlap on the
center digit. All arithmetic below is in F_11.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass

from number_compiler.arithmetic.fields.morphism_core import binary_power

MODULUS = 11
Row4 = tuple[int, int, int, int]
Matrix4 = tuple[Row4, Row4, Row4, Row4]


def _multiply_row(a: Matrix4, b: Matrix4, row: int) -> Row4:
    values = [
        sum(a[row][k] * b[k][column] for k in range(4)) % MODULUS for column in range(4)
    ]
    return values[0], values[1], values[2], values[3]


def _mul(a: Matrix4, b: Matrix4) -> Matrix4:
    return (
        _multiply_row(a, b, 0),
        _multiply_row(a, b, 1),
        _multiply_row(a, b, 2),
        _multiply_row(a, b, 3),
    )


def half_residues11(digits_lsd: Sequence[int]) -> tuple[int, int]:
    """Return exact half-word residues; never materialize the half integers."""
    width = len(digits_lsd)
    if width < 1:
        raise ValueError("center11 requires a nonempty source digit tape")
    half = (width + 1) // 2
    first = 0
    second = 0
    for index in range(half):
        high_digit = digits_lsd[width - 1 - index]
        low_digit = digits_lsd[index]
        if (
            type(high_digit) is not int
            or not 0 <= high_digit <= 9
            or type(low_digit) is not int
            or not 0 <= low_digit <= 9
        ):
            raise ValueError("center11 digit is outside the decimal alphabet")
        first = (10 * first + high_digit) % MODULUS
        second = (10 * second + low_digit) % MODULUS
    return first, second


@dataclass(frozen=True, slots=True)
class Center11Action:
    """Fixed-size affine half-word + cumulative defect transfer.

    The homogeneous block matrix is a controlled linear part; `growth_count`
    and width parities transport the moving reflection axis. `then()` joins
    compatible adjacent *port actions*, but does not itself authenticate
    which port word belongs to a particular future physical source.
    """

    duration: int
    source_width_parity: int
    target_width_parity: int
    growth_count: int
    rows: Matrix4

    def __post_init__(self) -> None:
        if type(self.duration) is not int or self.duration < 0:
            raise ValueError("center11 duration must be nonnegative")
        if (
            type(self.source_width_parity) is not int
            or self.source_width_parity not in (0, 1)
            or type(self.target_width_parity) is not int
            or self.target_width_parity not in (0, 1)
            or type(self.growth_count) is not int
            or not 0 <= self.growth_count <= self.duration
            or self.target_width_parity
            != (self.source_width_parity + self.growth_count) % 2
        ):
            raise ValueError("center11 width-skew/phase certificate mismatch")
        if (
            type(self.rows) is not tuple
            or len(self.rows) != 4
            or any(type(row) is not tuple for row in self.rows)
            or any(
                len(row) != 4
                or any(type(v) is not int or not 0 <= v < MODULUS for v in row)
                for row in self.rows
            )
            or self.rows[3] != (0, 0, 0, 1)
        ):
            raise ValueError("center11 affine action is not canonical")
        # The cumulative defect is a *sum of all intermediate output
        # differences*, not merely the difference of the final two halves.
        # It is therefore an independent affine OUTPUT row after temporal
        # composition, although it has no independent physical carry driver.
        if self.rows[0][2] or self.rows[1][2] or self.rows[2][2] != 1:
            raise ValueError("center11 cumulative defect cocycle is not aligned")
        if self.duration == 1:
            expected = tuple(
                (self.rows[0][j] - self.rows[1][j]) % MODULUS for j in (0, 1)
            ) + (1, (self.rows[0][3] - self.rows[1][3]) % MODULUS)
            if self.rows[2] != expected:
                raise ValueError("center11 one-tick defect is not the difference")

    @classmethod
    def identity(cls, source_width_parity: int) -> Center11Action:
        if type(source_width_parity) is not int or source_width_parity not in (0, 1):
            raise ValueError("invalid center11 width phase")
        return cls(
            0,
            source_width_parity,
            source_width_parity,
            0,
            ((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)),
        )

    @classmethod
    def from_physical_ports(
        cls,
        *,
        source_width: int,
        growth: int,
        center_coefficient: int,
        carry_in: int,
        carry_out: int,
    ) -> Center11Action:
        """Use the same physical Q19 carries as Laurent normalization."""
        if type(source_width) is not int or source_width < 1:
            raise ValueError("invalid center11 physical source width")
        if type(growth) is not int or growth not in (0, 1):
            raise ValueError("center11 growth must be an issued bit")
        if (
            type(center_coefficient) is not int
            or not 0 <= center_coefficient <= 18
            or type(carry_in) is not int
            or carry_in not in (0, 1)
            or type(carry_out) is not int
            or carry_out not in (0, 1)
        ):
            raise ValueError("center11 physical coefficient/carry port is invalid")
        if carry_out != (center_coefficient + carry_in) // 10:
            raise ValueError("center11 outgoing carry contradicts central coefficient")
        odd = source_width & 1
        if odd and center_coefficient % 2:
            raise ValueError("odd-width center11 raw coefficient must double one digit")
        # The three real group-ring matrices: J, K, -K.
        if not growth:
            m = ((1, 1), (1, 1))
            offsets = (carry_in, carry_out if odd else carry_in)
        elif not odd:
            m = ((1, 1), (-1, -1))
            offsets = (carry_in, center_coefficient + carry_out)
        else:
            m = ((-1, -1), (1, 1))
            offsets = (center_coefficient + carry_out, carry_out)
        a, b = m
        ua, ub = offsets
        rows = (
            (a[0] % 11, a[1] % 11, 0, ua % 11),
            (b[0] % 11, b[1] % 11, 0, ub % 11),
            ((a[0] - b[0]) % 11, (a[1] - b[1]) % 11, 1, (ua - ub) % 11),
            (0, 0, 0, 1),
        )
        return cls(1, odd, odd ^ growth, growth, rows)

    @property
    def homogeneous(self) -> tuple[tuple[int, int], tuple[int, int]]:
        return ((self.rows[0][0], self.rows[0][1]), (self.rows[1][0], self.rows[1][1]))

    @property
    def growth_synchronized(self) -> bool:
        """A growth event followed by >=1 physical step kills old half states."""
        return self.homogeneous == ((0, 0), (0, 0))

    def then(self, later: Center11Action) -> Center11Action:
        if (
            type(later) is not Center11Action
            or self.target_width_parity != later.source_width_parity
        ):
            raise ValueError("center11 source/target width-skew seam mismatch")
        return Center11Action(
            self.duration + later.duration,
            self.source_width_parity,
            later.target_width_parity,
            self.growth_count + later.growth_count,
            _mul(later.rows, self.rows),
        )

    def square(self, successor: Center11Action) -> Center11Action:
        """Square two supplied and phase-compatible actions, not a guessed word."""
        if type(successor) is not Center11Action or successor.duration != self.duration:
            raise ValueError("center11 square needs two equal-duration issued actions")
        return self.then(successor)

    def formal_power(self, copies: int) -> Center11Action:
        """Logarithmic power of a GIVEN port program; no physical repeat proof."""
        if type(copies) is not int or copies < 0:
            raise ValueError("center11 power count must be nonnegative")
        if copies > 1 and self.target_width_parity != self.source_width_parity:
            raise ValueError("width-skew program cannot repeat without phase transport")
        return binary_power(
            self,
            copies,
            identity=self.identity(self.source_width_parity),
            compose=Center11Action.then,
        ).value

    def apply(
        self, first: int, second: int, accumulated: int = 0
    ) -> tuple[int, int, int]:
        if any(type(v) is not int for v in (first, second, accumulated)):
            raise ValueError("center11 input must contain exact integer residues")
        v = (first % 11, second % 11, accumulated % 11, 1)
        first_out = sum(x * y for x, y in zip(self.rows[0], v, strict=True)) % 11
        second_out = sum(x * y for x, y in zip(self.rows[1], v, strict=True)) % 11
        difference_out = sum(x * y for x, y in zip(self.rows[2], v, strict=True)) % 11
        return first_out, second_out, difference_out

    def packet(
        self, first: int, second: int, *, accumulated: int = 0
    ) -> dict[str, object]:
        new_first, new_second, new_accumulated = self.apply(first, second, accumulated)
        return {
            "modulus": 11,
            "duration": self.duration,
            "source_width_parity": self.source_width_parity,
            "target_width_parity": self.target_width_parity,
            "growth_count": self.growth_count,
            "source_halves": [first % 11, second % 11],
            "target_halves": [new_first, new_second],
            "cumulative_difference_before": accumulated % 11,
            "cumulative_difference_after": new_accumulated,
            "homogeneous": [list(row) for row in self.homogeneous],
            "growth_synchronized": self.growth_synchronized,
            "matrix4": [list(row) for row in self.rows],
            "source_port_program_required": True,
        }


__all__ = ["Center11Action", "half_residues11", "MODULUS"]
