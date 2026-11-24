"""Ordered two-dimensional output actions; no physical repetition authority.

Callers own source admission and allocation budgets. A supplied finite word or
its formal repetition never certifies a physical recurrence or a future digit.
"""

from __future__ import annotations

from collections.abc import Callable, Iterable, Iterator
from dataclasses import dataclass
from math import comb

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.morphism_core import binary_power

MatrixEntries = tuple[int, int, int, int]


def _ring(modulus: int | None) -> None:
    if modulus is not None:
        require_integer(modulus, "matrix modulus", 2)


@dataclass(frozen=True, slots=True)
class Matrix2:
    """Exact or modular column action, in row-major order."""

    entries: MatrixEntries
    modulus: int | None = None

    def __post_init__(self) -> None:
        _ring(self.modulus)
        if (
            type(self.entries) is not tuple
            or len(self.entries) != 4
            or any(type(value) is not int for value in self.entries)
        ):
            raise TypeError("matrix requires four exact integer entries")
        if self.modulus is not None:
            a, b, c, d = self.entries
            object.__setattr__(
                self,
                "entries",
                (
                    a % self.modulus,
                    b % self.modulus,
                    c % self.modulus,
                    d % self.modulus,
                ),
            )

    @classmethod
    def identity(cls, modulus: int | None = None) -> Matrix2:
        return cls((1, 0, 0, 1), modulus)

    @classmethod
    def digit(cls, coefficient: int, modulus: int | None = None) -> Matrix2:
        require_integer(coefficient, "continuant coefficient", 1, 10)
        return cls((coefficient, 1, 1, 0), modulus)

    @classmethod
    def upper_shear(cls, delta: int, modulus: int | None = None) -> Matrix2:
        require_integer(delta, "shear displacement")
        return cls((1, delta, 0, 1), modulus)

    def multiply(self, right: Matrix2) -> Matrix2:
        if type(right) is not Matrix2 or self.modulus != right.modulus:
            raise ValueError("ordered matrices require the same coefficient ring")
        a, b, c, d = self.entries
        e, f, g, h = right.entries
        return Matrix2(
            (a * e + b * g, a * f + b * h, c * e + d * g, c * f + d * h), self.modulus
        )

    def then(self, later: Matrix2) -> Matrix2:
        """Apply this action first, then later: the product is later*self."""
        if type(later) is not Matrix2:
            raise TypeError("ordered composition requires a Matrix2")
        return later.multiply(self)

    def power(self, exponent: int) -> Matrix2:
        return self.power_with_work(exponent)[0]

    def power_with_work(self, exponent: int) -> tuple[Matrix2, int]:
        require_integer(exponent, "formal matrix exponent", 0)
        result = binary_power(
            self,
            exponent,
            identity=self.identity(self.modulus),
            compose=lambda earlier, later: earlier.then(later),
        )
        return result.value, result.compositions

    def apply(self, p: int, q: int) -> tuple[int, int]:
        require_integer(p, "first coordinate")
        require_integer(q, "second coordinate")
        a, b, c, d = self.entries
        left, right = a * p + b * q, c * p + d * q
        if self.modulus is not None:
            return left % self.modulus, right % self.modulus
        return left, right


def ordered_decimal_continuant(
    digits: Iterable[int], modulus: int | None = None
) -> Matrix2:
    """Fold validated decimal digits into an MSD-first right product.

    Digit validation belongs to the issuing source or admitted frame. The
    modulus is checked by the returned matrix's coefficient-ring owner.
    """
    if modulus is None:
        return _exact_continuant(digits, (1, 0, 0, 1))
    result = Matrix2.identity(modulus)
    for digit in digits:
        result = result.multiply(Matrix2.digit(digit + 1, modulus))
    return result


def _exact_continuant(
    digits: Iterable[int], entries: tuple[int, int, int, int]
) -> Matrix2:
    q, r, p, s = entries
    for digit in digits:
        coefficient = digit + 1
        q, r, p, s = q * coefficient + r, q, p * coefficient + s, p
    return Matrix2((q, r, p, s))


def _fixed_decimal_digits(value: int, place: int) -> Iterator[int]:
    while place:
        digit, value = divmod(value, place)
        yield digit
        place //= 10


def fold_fixed_decimal_row(value: int, first_place: int, product: Matrix2) -> Matrix2:
    """Append one admitted fixed-width row, preserving its leading zeroes."""
    digits = _fixed_decimal_digits(value, first_place)
    if product.modulus is None:
        return _exact_continuant(digits, product.entries)
    return product.multiply(ordered_decimal_continuant(digits, product.modulus))


def compile_dyadic_ordered_band(
    quotient: int,
    rows: int,
    width: int,
    reserve: Callable[[int, int, int], None],
    *,
    use_memo: bool,
) -> Matrix2:
    """Compile admitted dyadic shifts in chronological row order.

    The caller authenticates the quotient and coverage. Each working state
    and retained result is charged through ``reserve`` before allocation.
    """
    base = 10**width
    first_place = 10 ** (width - 1)
    memo: dict[tuple[int, int], Matrix2] = {}
    retained_bits = 0
    pending: list[tuple[int, int, int, tuple[int, int, int] | None]] = [
        (quotient, rows, 0, None)
    ]
    values: list[Matrix2] = []
    while pending:
        q, count, stage, repeat = pending.pop()
        key = (q, count)
        if stage == 0 and use_memo and key in memo:
            values.append(memo[key])
            continue
        reserve(q, count, retained_bits)
        if stage == 0 and count == 1:
            if width == 1:
                result = Matrix2.digit(q % base + 1)
            else:
                result = fold_fixed_decimal_row(
                    q % base, first_place, Matrix2.identity()
                )
        elif stage == 0:
            period = 0
            for candidate in range(1, min(32, count // 2) + 1):
                ring = base << (count - candidate - 1)
                if q % ring == (q >> candidate) % ring:
                    period = candidate
                    break
            if period:
                copies, tail = divmod(count, period)
                pending.append((q, count, 2, (period, copies, tail)))
                if tail:
                    pending.append((q >> (period * copies), tail, 0, None))
                pending.append((q % (base << (period - 1)), period, 0, None))
            else:
                left = count // 2
                pending.append((q, count, 1, None))
                pending.append((q >> left, count - left, 0, None))
                pending.append((q % (base << (left - 1)), left, 0, None))
            continue
        elif stage == 1:
            right, left_matrix = values.pop(), values.pop()
            result = left_matrix.multiply(right)
        else:
            assert repeat is not None
            _, copies, tail = repeat
            suffix = values.pop() if tail else None
            initial = values.pop()
            result = initial.power(copies)
            if suffix is not None:
                result = result.multiply(suffix)
        if use_memo:
            retained_bits += 8 * (
                q.bit_length()
                + sum(value.bit_length() for value in result.entries)
                + 256
            )
            reserve(q, count, retained_bits)
            memo[key] = result
        values.append(result)
    if len(values) != 1:
        raise ArithmeticError("ordered source fold did not produce one action")
    return values.pop()


@dataclass(frozen=True, slots=True)
class OrderedMatrixProduct:
    matrix: Matrix2
    multiplications: int
    letters_read: int


@dataclass(frozen=True, slots=True)
class OrderedMatrixProgram:
    """A supplied word. Formal repetition is not a source certificate."""

    letters: tuple[Matrix2, ...]

    def __post_init__(self) -> None:
        if (
            type(self.letters) is not tuple
            or not self.letters
            or any(type(letter) is not Matrix2 for letter in self.letters)
        ):
            raise TypeError("ordered program requires a nonempty matrix tuple")
        if any(letter.modulus != self.letters[0].modulus for letter in self.letters):
            raise ValueError("ordered program mixes coefficient rings")

    def product(self, start: int, count: int, *, repeat: bool = False) -> Matrix2:
        return self.product_with_work(start, count, repeat=repeat).matrix

    def product_with_work(
        self, start: int, count: int, *, repeat: bool = False
    ) -> OrderedMatrixProduct:
        require_integer(start, "word start", 0)
        require_integer(count, "word length", 0)
        if type(repeat) is not bool:
            raise TypeError("formal repetition flag must be Boolean")
        size = len(self.letters)
        if not repeat and start + count > size:
            raise ValueError("ordered word has no supplied continuation")
        cycles, tail = divmod(count, size) if repeat else (0, count)
        result = Matrix2.identity(self.letters[0].modulus)
        reads = work = 0
        if cycles:
            for offset in range(size):
                result = result.then(self.letters[(start + offset) % size])
            reads = work = size
            result, powers = result.power_with_work(cycles)
            work += powers
        for offset in range(tail):
            index = (start + offset) % size if repeat else start + offset
            result = result.then(self.letters[index])
            reads += 1
            work += 1
        return OrderedMatrixProduct(result, work, reads)


@dataclass(frozen=True, slots=True)
class OrderedCovector:
    """Coefficients of sum c[i]*p**i*q**(degree-i); output only."""

    coefficients: tuple[int, ...]
    modulus: int | None = None

    def __post_init__(self) -> None:
        _ring(self.modulus)
        if type(self.coefficients) is not tuple or not 1 <= len(self.coefficients) <= 9:
            raise ValueError("ordered covector degree must lie in 0..8")
        if any(type(value) is not int for value in self.coefficients):
            raise TypeError("ordered covector requires exact integer coefficients")
        if self.modulus is not None:
            object.__setattr__(
                self,
                "coefficients",
                tuple(value % self.modulus for value in self.coefficients),
            )

    def pullback(self, matrix: Matrix2) -> OrderedCovector:
        if type(matrix) is not Matrix2 or matrix.modulus != self.modulus:
            raise ValueError("covector and matrix must have the same ring")
        a, b, c, d = matrix.entries
        degree = len(self.coefficients) - 1
        out = [0] * (degree + 1)
        for i, coefficient in enumerate(self.coefficients):
            for j in range(i + 1):
                left = comb(i, j) * a**j * b ** (i - j)
                for k in range(degree - i + 1):
                    right = comb(degree - i, k) * c**k * d ** (degree - i - k)
                    out[j + k] += coefficient * left * right
                    if self.modulus is not None:
                        out[j + k] %= self.modulus
        return OrderedCovector(tuple(out), self.modulus)

    def value(self, p: int, q: int) -> int:
        require_integer(p, "first coordinate")
        require_integer(q, "second coordinate")
        degree = len(self.coefficients) - 1
        # All exponents are nonnegative: int documents pow's integral branch
        # to type checkers, without coercing any admitted source coordinate.
        result = sum(
            c * int(pow(p, i)) * int(pow(q, degree - i))
            for i, c in enumerate(self.coefficients)
        )
        return result if self.modulus is None else result % self.modulus
