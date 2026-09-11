"""Exact Karatsuba digit-field products and cyclotomic square quotients.

The older special-number differential path built raw cyclic/negacyclic square
fields with one scalar product for every nonzero digit pair.  This module keeps
the same coefficient semantics but constructs the ordinary polynomial product
with a balanced Karatsuba recursion before folding it into ``x**m-1`` or
``x**m+1``.  It then uses :mod:`carry_normalization` so the spatial carry vector
is never retained: only the single fixed/anti-fixed boundary carry survives.

This changes the digit-product work from quadratic to ``O(m**log2(3))`` scalar
leaf products for dense length-m fields.  It does *not* make Pepin or
Lucas-Lehmer logarithmic in their iteration count; that projection cost remains
separately metered.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from typing import Literal

from number_compiler.arithmetic.carry.carry_normalization import (
    EndAroundCarryNormalization,
    RadixCarryBlock,
    normalize_cyclic_block,
    normalize_negacyclic_block,
)
from number_compiler.arithmetic.fields.radix import bit_width


@dataclass(frozen=True, slots=True)
class ConvolutionMetrics:
    input_length: int
    padded_length: int
    scalar_multiplications: int
    coefficient_additions: int
    recursive_nodes: int
    algorithm: str = "karatsuba"

    @property
    def description_bits(self) -> int:
        return sum(
            bit_width(v)
            for v in (
                self.input_length,
                self.padded_length,
                self.scalar_multiplications,
                self.coefficient_additions,
                self.recursive_nodes,
            )
        )


@dataclass(frozen=True, slots=True)
class DigitSquareProjection:
    width: int
    sign: int
    field: tuple[int, ...]
    normalization: EndAroundCarryNormalization
    convolution: ConvolutionMetrics
    naive_scalar_products: int

    @property
    def residue(self) -> int:
        return self.normalization.residue

    @property
    def scalar_reduction(self) -> float:
        if not self.convolution.scalar_multiplications:
            return float("inf") if self.naive_scalar_products else 1.0
        return self.naive_scalar_products / self.convolution.scalar_multiplications


def _trim(values: list[int]) -> list[int]:
    while values and values[-1] == 0:
        values.pop()
    return values


def _add_vectors(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[tuple[int, ...], int]:
    n = max(len(a), len(b))
    out = [0] * n
    adds = 0
    for i in range(n):
        av = a[i] if i < len(a) else 0
        bv = b[i] if i < len(b) else 0
        out[i] = av + bv
        adds += int(i < len(a) and i < len(b))
    return tuple(_trim(out)), adds


def _sub_into(target: list[int], source: tuple[int, ...], offset: int = 0) -> int:
    adds = 0
    for i, value in enumerate(source):
        target[offset + i] -= value
        adds += 1
    return adds


def _add_into(target: list[int], source: tuple[int, ...], offset: int = 0) -> int:
    adds = 0
    for i, value in enumerate(source):
        target[offset + i] += value
        adds += 1
    return adds


def karatsuba_convolution(
    first: Sequence[int], second: Sequence[int], *, threshold: int = 1
) -> tuple[tuple[int, ...], ConvolutionMetrics]:
    """Exact ordinary convolution with explicit scalar-product accounting."""
    a = tuple(map(int, first))
    b = tuple(map(int, second))
    threshold = int(threshold)
    if threshold < 1:
        raise ValueError(threshold)
    input_length = max(len(a), len(b))
    if not a or not b:
        return (), ConvolutionMetrics(input_length, input_length, 0, 0, 0, "zero")
    padded = 1 << (input_length - 1).bit_length()
    aa = a + (0,) * (padded - len(a))
    bb = b + (0,) * (padded - len(b))

    # Explicit postorder Karatsuba frames.  Results retain the same charged
    # scalar/addition/node counts as the former recursive implementation.
    results: list[tuple[tuple[int, ...], int, int, int]] = []
    tasks: list[
        tuple[Literal["EVAL"], tuple[int, ...], tuple[int, ...]]
        | tuple[Literal["COMBINE"], int, int, int, int]
    ] = [("EVAL", aa, bb)]
    while tasks:
        frame = tasks.pop()
        tag = frame[0]
        if frame[0] == "EVAL":
            x, y = frame[1], frame[2]
            n = len(x)
            if n <= threshold:
                out = [0] * (2 * n - 1)
                muls = adds = 0
                for i, xv in enumerate(x):
                    if not xv:
                        continue
                    for j, yv in enumerate(y):
                        if not yv:
                            continue
                        product_value = xv * yv
                        had_value = out[i + j] != 0
                        out[i + j] += product_value
                        muls += 1
                        adds += int(had_value)
                results.append((tuple(_trim(out)), muls, adds, 1))
                continue
            half = n // 2
            x0, x1 = x[:half], x[half:]
            y0, y1 = y[:half], y[half:]
            sx, ax = _add_vectors(x0, x1)
            sy, ay = _add_vectors(y0, y1)
            sx = sx + (0,) * (half - len(sx))
            sy = sy + (0,) * (half - len(sy))
            tasks.append(("COMBINE", n, half, ax, ay))
            tasks.append(("EVAL", sx, sy))
            tasks.append(("EVAL", x1, y1))
            tasks.append(("EVAL", x0, y0))
            continue

        if frame[0] == "COMBINE":
            n, half, ax, ay = map(int, frame[1:])
            z1, m1, a1, r1 = results.pop()
            z2, m2, a2, r2 = results.pop()
            z0, m0, a0, r0 = results.pop()
            cross = list(z1) + [0] * max(0, max(len(z0), len(z2)) - len(z1))
            cross += [0] * max(0, (2 * half - 1) - len(cross))
            adds = a0 + a1 + a2 + ax + ay
            adds += _sub_into(cross, z0)
            adds += _sub_into(cross, z2)
            out = [0] * (2 * n - 1)
            adds += _add_into(out, z0, 0)
            adds += _add_into(out, tuple(cross), half)
            adds += _add_into(out, z2, 2 * half)
            results.append(
                (
                    tuple(_trim(out)),
                    m0 + m1 + m2,
                    adds,
                    1 + r0 + r1 + r2,
                )
            )
            continue
        raise AssertionError(tag)

    if len(results) != 1:
        raise AssertionError(len(results))
    product, muls, adds, nodes = results.pop()
    wanted = len(a) + len(b) - 1
    product = product[:wanted] + (0,) * max(0, wanted - len(product))
    return product, ConvolutionMetrics(
        input_length,
        padded,
        muls,
        adds,
        nodes,
        "schoolbook" if padded <= threshold else "karatsuba",
    )


def karatsuba_square(
    values: Sequence[int], *, threshold: int = 1
) -> tuple[tuple[int, ...], ConvolutionMetrics]:
    """Exact square using triangular leaves and three recursive subsquares.

    A leaf evaluates each unordered pair once: diagonal terms are emitted
    directly and off-diagonal terms are doubled.  The recursive identity
    ``(x0+x1)^2-x0^2-x1^2`` likewise needs three squares rather than routing
    through the general two-input multiplication owner.  Multiplication by two
    is charged as one coefficient addition.
    """
    source = tuple(map(int, values))
    threshold = int(threshold)
    if threshold < 1:
        raise ValueError(threshold)
    input_length = len(source)
    if not source:
        return (), ConvolutionMetrics(0, 0, 0, 0, 0, "zero")
    padded = 1 << (input_length - 1).bit_length()
    initial = source + (0,) * (padded - input_length)
    results: list[tuple[tuple[int, ...], int, int, int]] = []
    tasks: list[
        tuple[Literal["EVAL"], tuple[int, ...]]
        | tuple[Literal["COMBINE"], int, int, int]
    ] = [("EVAL", initial)]
    while tasks:
        frame = tasks.pop()
        if frame[0] == "EVAL":
            x = frame[1]
            n = len(x)
            if n <= threshold:
                out = [0] * (2 * n - 1)
                muls = adds = 0
                for i, left in enumerate(x):
                    if not left:
                        continue
                    for j in range(i, n):
                        right = x[j]
                        if not right:
                            continue
                        product_value = left * right
                        if i != j:
                            product_value += product_value
                            adds += 1
                        had_value = out[i + j] != 0
                        out[i + j] += product_value
                        muls += 1
                        adds += int(had_value)
                results.append((tuple(_trim(out)), muls, adds, 1))
                continue
            half = n // 2
            x0, x1 = x[:half], x[half:]
            summed, input_adds = _add_vectors(x0, x1)
            summed = summed + (0,) * (half - len(summed))
            tasks.append(("COMBINE", n, half, input_adds))
            tasks.append(("EVAL", summed))
            tasks.append(("EVAL", x1))
            tasks.append(("EVAL", x0))
            continue

        if frame[0] == "COMBINE":
            n, half, input_adds = map(int, frame[1:])
            middle, middle_muls, middle_adds, middle_nodes = results.pop()
            high, high_muls, high_adds, high_nodes = results.pop()
            low, low_muls, low_adds, low_nodes = results.pop()
            cross = list(middle) + [0] * max(0, max(len(low), len(high)) - len(middle))
            cross += [0] * max(0, (2 * half - 1) - len(cross))
            adds = low_adds + middle_adds + high_adds + input_adds
            adds += _sub_into(cross, low)
            adds += _sub_into(cross, high)
            out = [0] * (2 * n - 1)
            adds += _add_into(out, low, 0)
            adds += _add_into(out, tuple(cross), half)
            adds += _add_into(out, high, 2 * half)
            results.append(
                (
                    tuple(_trim(out)),
                    low_muls + middle_muls + high_muls,
                    adds,
                    1 + low_nodes + middle_nodes + high_nodes,
                )
            )
            continue
        raise AssertionError(frame[0])

    if len(results) != 1:
        raise AssertionError(len(results))
    product, muls, adds, nodes = results.pop()
    wanted = 2 * input_length - 1
    product = product[:wanted] + (0,) * max(0, wanted - len(product))
    return product, ConvolutionMetrics(
        input_length,
        padded,
        muls,
        adds,
        nodes,
        "schoolbook" if padded <= threshold else "karatsuba",
    )


def adaptive_square_convolution(
    values: Sequence[int],
) -> tuple[tuple[int, ...], ConvolutionMetrics]:
    """Choose a fail-honest sparse/small schoolbook or dense Karatsuba square.

    The decision uses only input width and nonzero density, both already present
    before multiplication.  It never executes and discards a losing product.
    Small/sparse fields use the direct convolution; dense fields at width >=512
    use a threshold-8 Karatsuba tree, where the charged add+multiply count is
    lower on the release stress suite.
    """
    vals = tuple(map(int, values))
    n = len(vals)
    if not n:
        return (), ConvolutionMetrics(0, 0, 0, 0, 0, "zero")
    density = sum(int(v != 0) for v in vals) / n
    threshold = 8 if n >= 512 and density >= 0.40 else (1 << (n - 1).bit_length())
    product, metrics = karatsuba_square(vals, threshold=threshold)
    algorithm = (
        "karatsuba" if threshold == 8 and metrics.padded_length > 8 else "schoolbook"
    )
    return product, ConvolutionMetrics(
        metrics.input_length,
        metrics.padded_length,
        metrics.scalar_multiplications,
        metrics.coefficient_additions,
        metrics.recursive_nodes,
        algorithm,
    )


def fold_cyclic(product: Sequence[int], width: int) -> tuple[int, ...]:
    width = int(width)
    if width <= 0:
        raise ValueError(width)
    out = [0] * width
    for i, value in enumerate(map(int, product)):
        out[i % width] += value
    return tuple(out)


def fold_negacyclic(product: Sequence[int], width: int) -> tuple[int, ...]:
    width = int(width)
    if width <= 0:
        raise ValueError(width)
    out = [0] * width
    for i, value in enumerate(map(int, product)):
        q, r = divmod(i, width)
        out[r] += -value if q & 1 else value
    return tuple(out)


def _binary_digits(
    value: int, width: int, *, signed_minus_one: bool = False
) -> tuple[int, ...]:
    value, width = int(value), int(width)
    if width <= 0 or value < 0:
        raise ValueError((value, width))
    scale = 1 << width
    if signed_minus_one and value == scale:
        return (-1,) + (0,) * (width - 1)
    if value >= scale:
        raise ValueError((value, width))
    return tuple((value >> i) & 1 for i in range(width))


def binary_square_sign_representative(value: int, width: int, sign: int) -> int:
    """Canonical sparse representative of the exact ``x ~ -x`` square quotient.

    ``sign=+1`` denotes modulus ``2**width-1`` (Mersenne/cyclic) and
    ``sign=-1`` denotes modulus ``2**width+1`` (Fermat/negacyclic), matching
    :class:`EndAroundCarryNormalization`.  Since ``x**2 == (-x)**2`` in either
    quotient, a squaring recurrence may canonicalize its *input* by sign before
    constructing the digit product.

    The representative minimizes the number of nonzero canonical binary
    digits, then the integer value for deterministic ties.  For the unique
    negacyclic ``-1`` residue ``2**width`` the canonical signed digit field is
    ``(-1,0,...,0)`` and therefore has weight one.
    """
    value, width, sign = int(value), int(width), int(sign)
    if width <= 0 or sign not in (-1, 1):
        raise ValueError((value, width, sign))
    scale = 1 << width
    modulus = scale - sign
    if not 0 <= value < modulus:
        raise ValueError((value, width, sign))

    def weight(candidate: int) -> int:
        if sign == -1 and candidate == scale:
            return 1
        return int(candidate).bit_count()

    negative = (-value) % modulus
    return min((weight(value), value), (weight(negative), negative))[1]


def cyclic_binary_square_projection(value: int, width: int) -> DigitSquareProjection:
    """Exact ``value**2 mod (2**width-1)`` through Karatsuba + scalar carry."""
    value, width = int(value), int(width)
    modulus = (1 << width) - 1
    if width < 2 or not 0 <= value < modulus:
        raise ValueError((value, width))
    digits = _binary_digits(value, width)
    product, metrics = adaptive_square_convolution(digits)
    field = fold_cyclic(product, width)
    block = RadixCarryBlock.from_coefficients(field, base=2)
    normalization = normalize_cyclic_block(block)
    naive = sum(digits) ** 2
    if normalization.residue != value * value % modulus:
        raise AssertionError((value, width, normalization.residue))
    return DigitSquareProjection(width, 1, field, normalization, metrics, naive)


def cyclic_binary_square_add_projection(
    value: int, width: int, constant: int
) -> DigitSquareProjection:
    """Exact ``value**2 + constant`` modulo ``2**width-1`` in the digit field."""
    value, width, constant = int(value), int(width), int(constant)
    modulus = (1 << width) - 1
    if width < 2 or not 0 <= value < modulus:
        raise ValueError((value, width))
    digits = _binary_digits(value, width)
    product, metrics = adaptive_square_convolution(digits)
    mutable_field = list(fold_cyclic(product, width))
    mutable_field[0] += constant
    field = tuple(mutable_field)
    block = RadixCarryBlock.from_coefficients(field, base=2)
    normalization = normalize_cyclic_block(block)
    naive = sum(digits) ** 2
    if normalization.residue != (value * value + constant) % modulus:
        raise AssertionError((value, width, constant, normalization.residue))
    return DigitSquareProjection(width, 1, field, normalization, metrics, naive)


def negacyclic_binary_square_projection(
    value: int, width: int
) -> DigitSquareProjection:
    """Exact ``value**2 mod (2**width+1)`` through Karatsuba + scalar carry."""
    value, width = int(value), int(width)
    modulus = (1 << width) + 1
    if width <= 0 or not 0 <= value < modulus:
        raise ValueError((value, width))
    digits = _binary_digits(value, width, signed_minus_one=True)
    product, metrics = adaptive_square_convolution(digits)
    field = fold_negacyclic(product, width)
    block = RadixCarryBlock.from_coefficients(field, base=2)
    normalization = normalize_negacyclic_block(block)
    naive = sum(int(bool(d)) for d in digits if d) ** 2
    if normalization.residue != value * value % modulus:
        raise AssertionError(
            (value, width, normalization.residue, value * value % modulus)
        )
    return DigitSquareProjection(width, -1, field, normalization, metrics, naive)


__all__ = [
    "ConvolutionMetrics",
    "DigitSquareProjection",
    "adaptive_square_convolution",
    "binary_square_sign_representative",
    "cyclic_binary_square_add_projection",
    "cyclic_binary_square_projection",
    "fold_cyclic",
    "fold_negacyclic",
    "karatsuba_convolution",
    "karatsuba_square",
    "negacyclic_binary_square_projection",
]
