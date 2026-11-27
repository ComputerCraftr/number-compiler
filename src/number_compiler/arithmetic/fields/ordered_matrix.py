"""Ordered two-dimensional output actions; no physical repetition authority.

Callers own source admission and allocation budgets. A supplied finite word or
its formal repetition never certifies a physical recurrence or a future digit.
"""

from __future__ import annotations

from collections.abc import Callable, Iterable, Iterator
from dataclasses import dataclass
from math import comb

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
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


def append_decimal_value(
    value: int, place: int, entries: MatrixEntries
) -> MatrixEntries:
    a, b, c, d = entries
    while place:
        digit, value = divmod(value, place)
        x = digit + 1
        a, b, c, d = a * x + b, a, c * x + d, c
        place //= 10
    return a, b, c, d


def fold_fixed_decimal_row(value: int, first_place: int, product: Matrix2) -> Matrix2:
    """Append one admitted fixed-width row, preserving its leading zeroes."""
    if product.modulus is None:
        return Matrix2(append_decimal_value(value, first_place, product.entries))
    return product.multiply(
        ordered_decimal_continuant(
            _fixed_decimal_digits(value, first_place), product.modulus
        )
    )


def _long_dyadic_band_period(q: int, rows: int, width: int, odd_base: int) -> int:
    """Lift a binary overlap to the first full decimal return of the band."""
    limit = rows // 2
    size = rows - 1 + width
    # Bit p survives exactly while the low source coordinates still match
    # at lag p. Compare candidate positions in parallel in packed integers.
    # The first full binary overlap is the primitive admissible binary lag.
    probe = 24
    head = q & ((1 << (limit + probe)) - 1)
    candidates = (1 << (limit + 1)) - 2
    for bit in range(probe):
        column = head >> bit
        candidates &= column if column & 1 else ~column
        if not candidates:
            return 0
    while candidates:
        selected = candidates & -candidates
        lag = selected.bit_length() - 1
        if not ((q ^ (q >> lag)) & ((1 << (size - lag)) - 1)):
            break
        candidates ^= selected
    else:
        return 0

    # Fine-Wilf: every other admissible binary lag is a multiple of lag.
    # At a multiple, the odd defect gains the geometric-sum factor.
    defect = (
        (pow(2, lag, odd_base) - 1) * (q % odd_base) + (q & ((1 << lag) - 1))
    ) % odd_base
    period = lag
    if defect:
        missing = width
        while defect % 5 == 0:
            defect //= 5
            missing -= 1
        if lag % 4 == 0:
            period *= 5**missing
        else:
            unit = lag
            while unit % 5 == 0:
                unit //= 5
                missing -= 1
            period *= (4 if lag % 2 else 2) * 5 ** max(0, missing - 1)
    if period <= limit:
        # Only this complete congruence authorizes ordered powering.
        shift = size - period
        shifted = q >> period
        if (
            not ((q ^ shifted) & ((1 << shift) - 1))
            and ((q - shifted) >> shift) % odd_base == 0
        ):
            return period
    return 0


def dyadic_band_period(q: int, count: int, width: int, odd_base: int) -> int:
    """Prove repetition in the lifted word before opening either child."""
    if count >= 128:
        return _long_dyadic_band_period(q, count, width, odd_base)
    return _short_dyadic_band_period(q, count, width, odd_base)


def _short_dyadic_band_period(q: int, count: int, width: int, odd_base: int) -> int:
    limit = min(32, count // 2)
    shift = count - 2 + width
    mask = (1 << shift) - 1
    for period in range(1, limit + 1):
        shifted = q >> period
        if not ((q ^ shifted) & mask) and ((q - shifted) >> shift) % odd_base == 0:
            return period
        shift -= 1
        mask >>= 1
    return 0


def _canonical_dyadic_motif(q: int, period: int, base: int) -> tuple[int, int]:
    """Return a least cyclic lift and the original word's receiving phase.

    A rotation shifts the low parity coordinates and appends the first row
    as the new high coordinate. No row spelling is constructed.
    """
    best, rotation = q, 0
    mask = (1 << (period - 1)) - 1
    for step in range(1, period):
        q = ((q >> 1) & mask) | ((q % base) << (period - 1))
        if q < best:
            best, rotation = q, step
    return best, (-rotation) % period


def _append_dyadic_digits(q: int, count: int, entries: MatrixEntries) -> MatrixEntries:
    """Fused terminal action for a bounded single-column dyadic word."""
    a, b, c, d = entries
    for _ in range(count):
        x = q % 10 + 1
        a, b, c, d = a * x + b, a, c * x + d, c
        q >>= 1
    return a, b, c, d


# This immutable finite alphabet is source independent, not a history cache.
DYADIC_FOUR_ROW = tuple(_append_dyadic_digits(q, 4, (1, 0, 0, 1)) for q in range(80))


def fold_dyadic_leaf(q: int, count: int, width: int, base: int) -> Matrix2:
    """Fused arithmetic leaf, not a DAG node or digit object per coefficient."""
    a, b, c, d = 1, 0, 0, 1
    if width == 1:
        groups, tail = divmod(count, 4)
        for _ in range(groups):
            e, f, g, h = DYADIC_FOUR_ROW[q % 80]
            a, b, c, d = a * e + b * g, a * f + b * h, c * e + d * g, c * f + d * h
            q >>= 4
        if tail:
            a, b, c, d = _append_dyadic_digits(q, tail, (a, b, c, d))
    else:
        first_place = base // 10
        for _ in range(count):
            a, b, c, d = append_decimal_value(q % base, first_place, (a, b, c, d))
            q >>= 1
    return Matrix2((a, b, c, d))


def _conjugate_by_prefix(value: Matrix2, prefix: Matrix2, parity: int) -> Matrix2:
    a, b, c, d = prefix.entries
    sign = -1 if parity else 1
    inverse = Matrix2((sign * d, -sign * b, -sign * c, sign * a))
    return inverse.multiply(value).multiply(prefix)


def compile_dyadic_ordered_band(
    quotient: int,
    rows: int,
    width: int,
    reserve: Callable[[int, int, int], None],
    *,
    use_memo: bool,
) -> Matrix2:
    """Compile a lifted diagonal with bounded, source-independent tile reuse.

    The caller supplies the physical source guard. Reserve the simultaneous
    root/child operands and bounded motif cache before any split. Repeats are
    recognized on Q, and rotations reuse a primitive orbit matrix. Only a
    nonrepeating terminal tile opens its bounded digit factors.
    """
    require_integer(rows, "ordered band rows", 1)
    require_integer(width, "ordered band width", 1)
    require_integer(quotient, "ordered band quotient", 0)
    if rows == 8 and width == 1:
        # Two 640 × 16-byte buffers coexist while freezing the alphabet.
        # Include 4 KiB for the builder frame, operands and result.
        try:
            reserve(quotient, rows, (2 * 640 * 16 + 4096) * 8)
        except BlockContextBudgetExceeded:
            pass
        else:
            from number_compiler.arithmetic.fields.dyadic_eight_rows import (
                eight_row_interval,
            )

            return eight_row_interval(quotient)

    # A depth-first binary fold holds disjoint completed children plus one
    # working product. The caller's root bit reservation bounds those limbs.
    # The extra fixed-size cache can retain only small primitive/leaf actions.
    capacity = min(16, max(1, rows // 16)) if use_memo else 0
    leaf_rows = max(2, min(64, 128 // width))
    cache_bits = capacity * 8 * (256 + min(rows, 64) * (16 * width + 1))
    # Include the simultaneously live packed probe, lag mask, and lift checks.
    probe_bits = 8 * (rows + 4 * width + 64) if rows >= 128 else 0
    period_of = dyadic_band_period
    try:
        reserve(quotient, rows, cache_bits + probe_bits)
    except BlockContextBudgetExceeded:
        if not probe_bits:
            raise
        reserve(quotient, rows, cache_bits)
        period_of = _short_dyadic_band_period
    base, odd_base = 10**width, 5**width
    quotient %= base << (rows - 1)
    memo: dict[tuple[int, int], Matrix2] = {}

    def small(q: int, count: int) -> Matrix2:
        key = (q, count)
        value = memo.get(key)
        if value is None:
            value = fold_dyadic_leaf(q, count, width, base)
            if len(memo) < capacity:
                memo[key] = value
        return value

    # Pending entries are symbolic split/return actions, not physical rows.
    pending: list[tuple[int, int, int]] = [(quotient, rows, 0)]
    values: list[Matrix2] = []
    while pending:
        q, count, stage = pending.pop()
        if stage == 2:
            values.append(values.pop().power(count))
            continue
        if stage == 1:
            right_product, left_product = values.pop(), values.pop()
            values.append(left_product.multiply(right_product))
            continue
        if capacity:
            cached = memo.get((q, count))
            if cached is not None:
                values.append(cached)
                continue
        period = period_of(q, count, width, odd_base)
        if period:
            copies, tail = divmod(count, period)
            motif = q % (base << (period - 1))
            if period > 32:
                # A long return covers at least two copies. Compile its body
                # once with the same balanced traversal and bounded leaf cache.
                if tail:
                    pending.append((0, 0, 1))
                    pending.append((q >> (copies * period), tail, 0))
                pending.append((0, copies, 2))
                pending.append((motif, period, 0))
                continue
            canonical, phase = _canonical_dyadic_motif(motif, period, base)
            product = small(canonical, period).power(copies)
            if phase:
                prefix = small(canonical % (base << (phase - 1)), phase)
                product = _conjugate_by_prefix(product, prefix, phase * width & 1)
            if tail:
                product = product.multiply(small(q >> (copies * period), tail))
            values.append(product)
        elif count <= leaf_rows:
            values.append(small(q, count))
        else:
            left_rows = count // 2
            pending.append((q, count, 1))
            pending.append((q >> left_rows, count - left_rows, 0))
            pending.append((q % (base << (left_rows - 1)), left_rows, 0))
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
