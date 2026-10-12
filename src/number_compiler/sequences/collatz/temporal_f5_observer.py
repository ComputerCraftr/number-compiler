"""Finite F5 affine and root-semifield observations for Collatz tapes.

These optional observers are separate from physical successor selection.
They retain exact finite-field actions and bounded root-fiber certificates.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from typing import overload

from number_compiler.arithmetic.fields.morphism_core import AffineCocycle, binary_power
from number_compiler.arithmetic.fields.root_semifield import RootSemifieldElement
from number_compiler.resources.ledger import ResourceLedger

_F5 = 5
_ROOT_CERTIFICATE_DEPTH = 8


@dataclass(frozen=True, slots=True, order=True)
class CollatzF5AffineAction:
    """Affine map ``x -> scale*x + offset`` on F5."""

    scale: int
    offset: int

    def __post_init__(self) -> None:
        if type(self.scale) is not int or type(self.offset) is not int:
            raise TypeError("F5 affine action needs exact integers")
        if not 1 <= self.scale < _F5 or not 0 <= self.offset < _F5:
            raise ValueError("F5 affine action lies outside AGL(1,5)")

    @classmethod
    def identity(cls) -> CollatzF5AffineAction:
        return cls(1, 0)

    def apply(self, value: int) -> int:
        if type(value) is not int:
            raise TypeError("F5 action input must be an exact integer")
        return AffineCocycle(self.scale, self.offset).apply(
            value,
            multiply=lambda a, b: a * b % _F5,
            add=lambda a, b: (a + b) % _F5,
        )

    def then(self, after: CollatzF5AffineAction) -> CollatzF5AffineAction:
        if type(after) is not CollatzF5AffineAction:
            raise TypeError("F5 affine actions compose with their own type")
        composed = AffineCocycle(self.scale, self.offset).then(
            AffineCocycle(after.scale, after.offset),
            multiply=lambda a, b: a * b % _F5,
            add=lambda a, b: (a + b) % _F5,
        )
        return CollatzF5AffineAction(composed.multiplier, composed.addend)

    def power(self, exponent: int) -> CollatzF5AffineAction:
        return binary_power(
            self,
            exponent,
            identity=CollatzF5AffineAction.identity(),
            compose=CollatzF5AffineAction.then,
        ).value


HENSEL_ZERO_F5 = CollatzF5AffineAction(3, 0)
HENSEL_ONE_F5 = CollatzF5AffineAction(4, 3)
ODD_HALF_F5 = CollatzF5AffineAction(3, 1)


class _F5AffineAlphabet(Sequence[CollatzF5AffineAction]):
    """Fixed AGL(1,5) coordinates, constructed only when explicitly read."""

    def __len__(self) -> int:
        return 20

    @overload
    def __getitem__(self, index: int) -> CollatzF5AffineAction: ...

    @overload
    def __getitem__(self, index: slice) -> tuple[CollatzF5AffineAction, ...]: ...

    def __getitem__(
        self,
        index: int | slice,
    ) -> CollatzF5AffineAction | tuple[CollatzF5AffineAction, ...]:
        if isinstance(index, slice):
            return tuple(
                CollatzF5AffineAction(i // _F5 + 1, i % _F5)
                for i in range(*index.indices(len(self)))
            )
        if index < 0:
            index += len(self)
        if not 0 <= index < len(self):
            raise IndexError(index)
        scale, offset = divmod(index, _F5)
        return CollatzF5AffineAction(scale + 1, offset)


F5_AFFINE_ALPHABET = _F5AffineAlphabet()


def _f5_index(action: CollatzF5AffineAction) -> int:
    if type(action) is not CollatzF5AffineAction:
        raise TypeError("temporal fiber requires an F5 affine action")
    action.__post_init__()
    return (action.scale - 1) * _F5 + action.offset


@dataclass(frozen=True, slots=True)
class CollatzAnonymousF5Fiber:
    """Anonymous multiplicities over the finite temporal F5 action group."""

    counts: tuple[int, ...]

    def __post_init__(self) -> None:
        if len(self.counts) != len(F5_AFFINE_ALPHABET):
            raise ValueError("temporal F5 fiber has the wrong basis size")
        if any(type(count) is not int or count < 0 for count in self.counts):
            raise ValueError("temporal F5 multiplicities must be natural numbers")

    @classmethod
    def identity(cls) -> CollatzAnonymousF5Fiber:
        counts = [0] * len(F5_AFFINE_ALPHABET)
        counts[_f5_index(CollatzF5AffineAction.identity())] = 1
        return cls(tuple(counts))

    @classmethod
    def source_symbol_fiber(cls) -> CollatzAnonymousF5Fiber:
        counts = [0] * len(F5_AFFINE_ALPHABET)
        counts[_f5_index(HENSEL_ZERO_F5)] += 1
        counts[_f5_index(HENSEL_ONE_F5)] += 1
        return cls(tuple(counts))

    @classmethod
    def singleton(cls, action: CollatzF5AffineAction) -> CollatzAnonymousF5Fiber:
        if type(action) is not CollatzF5AffineAction:
            raise ValueError("temporal singleton fiber needs an admitted F5 action")
        counts = [0] * len(F5_AFFINE_ALPHABET)
        counts[_f5_index(action)] = 1
        return cls(tuple(counts))

    @property
    def unique_action(self) -> CollatzF5AffineAction:
        support = tuple(self.support)
        if self.cardinality != 1 or len(support) != 1:
            raise ValueError("temporal fiber is not a singleton source action")
        return support[0]

    @property
    def cardinality(self) -> int:
        return sum(self.counts)

    @property
    def root_amplitude(self) -> RootSemifieldElement:
        return RootSemifieldElement(self.cardinality)

    @property
    def support(self) -> frozenset[CollatzF5AffineAction]:
        return frozenset(
            F5_AFFINE_ALPHABET[index]
            for index, count in enumerate(self.counts)
            if count
        )

    def root_sum(self, other: CollatzAnonymousF5Fiber) -> CollatzAnonymousF5Fiber:
        if type(other) is not CollatzAnonymousF5Fiber:
            raise TypeError("temporal root sum requires another F5 fiber")
        out = CollatzAnonymousF5Fiber(
            tuple(a + b for a, b in zip(self.counts, other.counts, strict=True))
        )
        expected = self.root_amplitude.root_sum(other.root_amplitude)
        if out.root_amplitude != expected:
            raise AssertionError("root-sum fiber cardinality lost exactness")
        return out

    def root_difference(
        self, other: CollatzAnonymousF5Fiber
    ) -> CollatzAnonymousF5Fiber:
        if type(other) is not CollatzAnonymousF5Fiber:
            raise TypeError("temporal root difference requires another F5 fiber")
        if any(b > a for a, b in zip(self.counts, other.counts, strict=True)):
            raise ValueError("root difference requires a proved subfiber")
        out = CollatzAnonymousF5Fiber(
            tuple(a - b for a, b in zip(self.counts, other.counts, strict=True))
        )
        expected = self.root_amplitude.root_difference(other.root_amplitude)
        if out.root_amplitude != expected:
            raise AssertionError("root-difference fiber cardinality lost exactness")
        return out

    def multiply(self, other: CollatzAnonymousF5Fiber) -> CollatzAnonymousF5Fiber:
        if type(other) is not CollatzAnonymousF5Fiber:
            raise TypeError("temporal Cayley product requires another F5 fiber")
        counts = [0] * len(F5_AFFINE_ALPHABET)
        left_entries = tuple(
            (index, count) for index, count in enumerate(self.counts) if count
        )
        right_entries = tuple(
            (index, count) for index, count in enumerate(other.counts) if count
        )
        for left_index, left_count in left_entries:
            left = F5_AFFINE_ALPHABET[left_index]
            for right_index, right_count in right_entries:
                target = left.then(F5_AFFINE_ALPHABET[right_index])
                counts[_f5_index(target)] += left_count * right_count
        out = CollatzAnonymousF5Fiber(tuple(counts))
        expected = self.root_amplitude.multiply(other.root_amplitude)
        if out.root_amplitude != expected:
            raise AssertionError("root-product fiber cardinality lost exactness")
        return out

    def power(self, exponent: int) -> CollatzAnonymousF5Fiber:
        return binary_power(
            self,
            exponent,
            identity=CollatzAnonymousF5Fiber.identity(),
            compose=CollatzAnonymousF5Fiber.multiply,
        ).value


def _root_fiber(
    depth: int, *, ledger: ResourceLedger | None = None
) -> CollatzAnonymousF5Fiber:
    """Build the bounded anonymous temporal fiber through the root algebra."""
    if type(depth) is not int or not 0 <= depth <= _ROOT_CERTIFICATE_DEPTH:
        raise ValueError(depth)
    fiber = CollatzAnonymousF5Fiber.identity()
    symbol = CollatzAnonymousF5Fiber.source_symbol_fiber()
    for _ in range(depth):
        fiber = fiber.multiply(symbol)
        if ledger is not None:
            ledger.bump("collatz_physical_temporal_root_cayley_products")
    return fiber


@dataclass(frozen=True, slots=True)
class CollatzPoweredRootVietaProgram:
    """Lazy anonymous F5 coefficient program, with no source-port authority.

    Construction and composition retain only a symbol count. Explicit evaluation
    uses binary powering of twenty Cayley multiplicities; those integers can have
    a number of bits linear in ``symbols``. Integer coordinate power sums are
    descriptive Vieta data, not a proof about exact Collatz successors.
    """

    symbols: int

    def __post_init__(self) -> None:
        if type(self.symbols) is not int or self.symbols < 0:
            raise ValueError("powered root/Vieta program needs a natural width")

    @property
    def semantic_key(self) -> tuple[str, int]:
        return ("collatz-f5-vieta-power-v1", self.symbols)

    def then(
        self, after: CollatzPoweredRootVietaProgram
    ) -> CollatzPoweredRootVietaProgram:
        if type(after) is not CollatzPoweredRootVietaProgram:
            raise TypeError("root/Vieta composition requires another powered program")
        return CollatzPoweredRootVietaProgram(self.symbols + after.symbols)

    def square(self) -> CollatzPoweredRootVietaProgram:
        return CollatzPoweredRootVietaProgram(2 * self.symbols)

    def evaluate(self) -> CollatzAnonymousF5Fiber:
        """Materialize exact finite multiplicities only on explicit demand."""
        return CollatzAnonymousF5Fiber.source_symbol_fiber().power(self.symbols)

    def vieta_moments(self, order: int = 19) -> tuple[int, ...]:
        """Return coordinate power sums from degree zero through ``order``."""
        if type(order) is not int or order < 0:
            raise ValueError("Vieta moment order must be nonnegative")
        counts = self.evaluate().counts
        roots = tuple(5 * action.scale + action.offset for action in F5_AFFINE_ALPHABET)
        return tuple(
            sum(count * root**degree for root, count in zip(roots, counts, strict=True))
            for degree in range(order + 1)
        )


@dataclass(frozen=True, slots=True)
class CollatzRootFiberCertificate:
    """Explicit bounded support audit plus a lazy all-scale coefficient program."""

    depth: int
    support_size: int
    amplitude_square: int
    powered_program: CollatzPoweredRootVietaProgram

    @property
    def powered_symbols(self) -> int:
        return self.powered_program.symbols

    def powered_multiplicity(self, action: CollatzF5AffineAction) -> int:
        return self.powered_program.evaluate().counts[_f5_index(action)]


def root_fiber_certificate(
    normalized_symbols: int, *, ledger: ResourceLedger | None = None
) -> CollatzRootFiberCertificate:
    if type(normalized_symbols) is not int or normalized_symbols < 0:
        raise ValueError(normalized_symbols)
    if ledger is not None and type(ledger) is not ResourceLedger:
        raise TypeError("root fiber certificate requires its resource ledger")
    depth = min(normalized_symbols, _ROOT_CERTIFICATE_DEPTH)
    fiber = _root_fiber(depth, ledger=ledger)
    if normalized_symbols >= _ROOT_CERTIFICATE_DEPTH and len(fiber.support) != 20:
        raise AssertionError("temporal F5 root fiber did not saturate at depth eight")
    if ledger is not None:
        ledger.bump(
            "collatz_physical_temporal_root_semifield_amplitude_square",
            fiber.cardinality,
        )
        ledger.bump("collatz_physical_temporal_root_vieta_programs")
        ledger.bump(
            "collatz_physical_temporal_root_vieta_powered_symbols", normalized_symbols
        )
        ledger.bump(
            "collatz_physical_temporal_root_vieta_program_description_bits",
            max(1, normalized_symbols.bit_length()),
        )
    return CollatzRootFiberCertificate(
        depth,
        len(fiber.support),
        fiber.cardinality,
        CollatzPoweredRootVietaProgram(normalized_symbols),
    )


def _append_dyadic_f5(
    normalized: CollatzF5AffineAction,
    physical: CollatzF5AffineAction,
    multiplier: int,
    target_origin: int,
    residue: int,
) -> tuple[CollatzF5AffineAction, CollatzF5AffineAction]:
    # Admitted dyadic widths are multiples of four, so 2**width = 1 mod 5.
    action = CollatzF5AffineAction(
        multiplier % 5, (target_origin - multiplier * residue) % 5
    )
    return normalized.then(action), physical.then(action)


def _run_zero_f5(length: int) -> CollatzF5AffineAction:
    if type(length) is not int or length <= 0:
        raise ValueError("zero run length must be positive")
    # x -> 3*x on F5 has order four.
    return HENSEL_ZERO_F5.power(length & 3)


def _run_one_f5(length: int) -> CollatzF5AffineAction:
    if type(length) is not int or length <= 0:
        raise ValueError("one run length must be positive")
    # x -> 4*x+3 on F5 is an involution.
    return HENSEL_ONE_F5 if length & 1 else CollatzF5AffineAction.identity()


_CYCLE_F5 = HENSEL_ONE_F5.then(HENSEL_ZERO_F5)
