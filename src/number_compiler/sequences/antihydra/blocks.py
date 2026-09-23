"""Admitted dyadic cylinders with physical quadratic roofs and prefix safety.

Only demanded kernels of at most eight returns are built by branch discovery.
Larger cylinders compose their actions, including their physical clock roof.
"""

from __future__ import annotations

from dataclasses import dataclass
from operator import add, mul

from number_compiler.arithmetic.fields.consumer_pullback import PrefixSafety
from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer


def _join_source_cylinders(
    before_width: int,
    before_residue: int,
    before_output: int,
    before_skew: SkewTransfer[int],
    after_width: int,
    after_residue: int,
    after_skew: SkewTransfer[int],
) -> tuple[int, int, int, int]:
    """Transport the second cylinder through the first source chart.

    Both the total arithmetic and guarded physical roof must use this same
    CRT lift, chronological skew, and output occurrence. The physical roof's
    translated high coordinate is deliberately computed only on demand.
    The tuple is ``(lift, joined_residue, joined_output, 3**width)``.
    """
    modulus = 1 << after_width
    first_gain = 3**before_width
    lift = ((after_residue - before_output) * pow(first_gain, -1, modulus)) % modulus
    residue = before_residue + (lift << before_width)
    transfer = before_skew.then(after_skew, multiply=mul, add=add)
    output = (transfer.upper * residue + transfer.offset) // transfer.lower
    return lift, residue, output, first_gain


@dataclass(frozen=True, slots=True)
class ArithmeticCylinder:
    """Total arithmetic source action without an eagerly constructed clock roof."""

    width: int
    residue: int
    output: int
    delta: int
    minimum: int
    parity_word: int

    def __post_init__(self) -> None:
        if (
            type(self.width) is not int
            or not 1 <= self.width <= 64
            or any(
                type(value) is not int
                for value in (
                    self.residue,
                    self.output,
                    self.delta,
                    self.minimum,
                    self.parity_word,
                )
            )
            or not 0 <= self.residue < 1 << self.width
            or not 0 <= self.parity_word < 1 << self.width
        ):
            raise ValueError("invalid bounded arithmetic cylinder")

    @property
    def skew(self) -> SkewTransfer[int]:
        p2, p3 = 1 << self.width, 3**self.width
        return SkewTransfer(p3, p2 * self.output - p3 * self.residue, p2)

    def advance(self, h: int, ledger: int) -> tuple[int, int]:
        p2 = 1 << self.width
        if type(h) is not int or type(ledger) is not int:
            raise TypeError("cylinder arithmetic requires exact integers")
        if h < 6 or h % p2 != self.residue:
            raise ValueError("source is outside the arithmetic cylinder")
        return 3**self.width * (h >> self.width) + self.output, ledger + self.delta

    def then(self, after: ArithmeticCylinder) -> ArithmeticCylinder:
        safety = PrefixSafety(self.delta, self.minimum).then(
            PrefixSafety(after.delta, after.minimum)
        )
        k, ell = self.width, after.width
        _lift, residue, output, _first_gain = _join_source_cylinders(
            k, self.residue, self.output, self.skew, ell, after.residue, after.skew
        )
        return ArithmeticCylinder(
            k + ell,
            residue,
            output,
            safety.delta,
            safety.minimum,
            self.parity_word | (after.parity_word << k),
        )


@dataclass(frozen=True, slots=True)
class Cylinder:
    width: int
    residue: int
    output: int
    delta: int
    minimum: int
    # Four times physical T, in x=(h-residue)/2^width and incoming ledger a.
    quadratic: int
    linear: int
    ledger_coefficient: int
    constant: int

    @property
    def skew(self) -> SkewTransfer[int]:
        p2, p3 = 1 << self.width, 3**self.width
        return SkewTransfer(p3, p2 * self.output - p3 * self.residue, p2)

    def apply(self, h: int, ledger: int) -> tuple[int, int, int, int]:
        """Return h', ledger', physical L and R; reject unsafe cylinders."""
        if ledger + self.minimum < 0:
            raise ValueError("source is outside the safe admitted cylinder")
        h_next, ledger_next = self.advance(h, ledger)
        x = h >> self.width
        numerator = (
            (self.quadratic * x + self.linear) * x
            + self.ledger_coefficient * ledger
            + self.constant
        )
        if numerator % 4:
            raise ArithmeticError("nonintegral physical clock roof")
        ticks = numerator // 4
        displacement = h_next - h - self.width
        if (ticks - displacement) % 2 or ticks < abs(displacement):
            raise ArithmeticError("invalid directional clock roof")
        return (
            h_next,
            ledger_next,
            (ticks - displacement) // 2,
            (ticks + displacement) // 2,
        )

    def advance(self, h: int, ledger: int) -> tuple[int, int]:
        """Apply the total arithmetic skew without asserting TM admission."""
        p2 = 1 << self.width
        if type(h) is not int or type(ledger) is not int:
            raise TypeError("cylinder arithmetic requires exact integers")
        if h < 6 or h % p2 != self.residue:
            raise ValueError("source is outside the arithmetic cylinder")
        return 3**self.width * (h >> self.width) + self.output, ledger + self.delta

    def then(self, after: Cylinder) -> Cylinder:
        """Compose full cylinders; derive the required incoming source lift."""
        safety = PrefixSafety(self.delta, self.minimum).then(
            PrefixSafety(after.delta, after.minimum)
        )
        k, ell = self.width, after.width
        lift, residue, output, p3 = _join_source_cylinders(
            k, self.residue, self.output, self.skew, ell, after.residue, after.skew
        )
        # x_first = 2^ell*x + lift, x_after = 3^k*x + translated.
        translated = (p3 * lift + self.output - after.residue) // (1 << ell)
        a, b = 1 << ell, p3
        q = self.quadratic * a * a + after.quadratic * b * b
        linear = (2 * self.quadratic * lift + self.linear) * a + (
            2 * after.quadratic * translated + after.linear
        ) * b
        constant = (
            (self.quadratic * lift + self.linear) * lift
            + self.constant
            + (after.quadratic * translated + after.linear) * translated
            + after.constant
            + after.ledger_coefficient * self.delta
        )
        return Cylinder(
            k + ell,
            residue,
            output,
            safety.delta,
            safety.minimum,
            q,
            linear,
            self.ledger_coefficient + after.ledger_coefficient,
            constant,
        )


def kernel(residue: int, width: int) -> Cylinder:
    return physical_roof(arithmetic_kernel(residue, width))


def physical_roof(core: ArithmeticCylinder) -> Cylinder:
    """Decorate one admitted parity word with its quadratic physical roof."""
    if type(core) is not ArithmeticCylinder:
        raise TypeError("physical roof requires an arithmetic cylinder")
    core.__post_init__()
    residue, width = core.residue, core.width
    q, slope = residue, 1 << width
    delta = quadratic = linear = coefficient = constant = 0
    minimum = 0
    for index in range(width):
        odd = (core.parity_word >> index) & 1
        quadratic += 3 * slope * slope
        linear += 6 * slope * (q - odd)
        constant += 3 * q * q - 6 * odd * q - (25 if odd else 4)
        if not odd:
            constant += 8 * delta
            coefficient += 8
        delta += -1 if odd else 2
        minimum = min(minimum, delta)
        q = (3 * q - odd) // 2
        slope = 3 * slope // 2
    if (q, delta, minimum) != (core.output, core.delta, core.minimum):
        raise ValueError("arithmetic parity word differs from its cylinder")
    return Cylinder(
        width,
        residue,
        q,
        delta,
        minimum,
        quadratic,
        linear,
        coefficient,
        constant,
    )


def arithmetic_from_word(
    residue: int, width: int, parity_word: int
) -> ArithmeticCylinder:
    """Restrict an already admitted chronological parity word."""
    if type(width) is not int or not 1 <= width <= 64:
        raise ValueError("arithmetic word width must be 1..64")
    if type(residue) is not int or not 0 <= residue < 1 << width:
        raise ValueError("noncanonical cylinder residue")
    if type(parity_word) is not int or not 0 <= parity_word < 1 << width:
        raise ValueError("noncanonical arithmetic parity word")
    q, delta, minimum = residue, 0, 0
    for index in range(width):
        odd = (parity_word >> index) & 1
        delta += -1 if odd else 2
        minimum = min(minimum, delta)
        q = (3 * q - odd) // 2
    return ArithmeticCylinder(width, residue, q, delta, minimum, parity_word)


def admitted_arithmetic_cylinder(residue: int, width: int) -> ArithmeticCylinder:
    """Construct the unique source-admitted arithmetic cylinder of width <=64."""
    if type(width) is not int or not 1 <= width <= 64:
        raise ValueError("admitted arithmetic width must be 1..64")
    if type(residue) is not int or not 0 <= residue < 1 << width:
        raise ValueError("noncanonical cylinder residue")
    q, delta, minimum, parity_word = residue, 0, 0, 0
    for index in range(width):
        odd = q & 1
        parity_word |= odd << index
        delta += -1 if odd else 2
        minimum = min(minimum, delta)
        q = (3 * q - odd) // 2
    return ArithmeticCylinder(width, residue, q, delta, minimum, parity_word)


def arithmetic_kernel(residue: int, width: int) -> ArithmeticCylinder:
    """Build one bounded arithmetic leaf without physical roof coefficients."""
    if type(width) is not int or not 1 <= width <= 8:
        raise ValueError("kernel width must be 1..8")
    return admitted_arithmetic_cylinder(residue, width)


def terminal_effect(h: int) -> tuple[int, int]:
    """A(0,b), odd b>=3, up to the undefined F0 boundary (no extra tick)."""
    if type(h) is not int or h < 7 or not h & 1:
        raise ValueError("terminal section requires odd h>=7")
    ticks = (3 * h * h - 12 * h - 19) // 4
    displacement = 2 - h
    return (ticks - displacement) // 2, (ticks + displacement) // 2
