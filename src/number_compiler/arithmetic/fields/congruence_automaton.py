"""Factored affine congruence automata and radix/mixed-radix morphisms.

A factored residue state is a tuple over explicit moduli. A radix digit is the
affine transition

    r_i -> base*r_i + digit (mod M_i).

These transitions compose as a monoid. Repeated runs therefore power by
squaring, and additive jumps are the same affine object with multiplier one.
Family-specific classifiers consume this shared arithmetic.
"""

from __future__ import annotations

from collections.abc import Iterable, Sequence
from dataclasses import dataclass

from number_compiler.arithmetic.automata.program_word import CanonicalWord, iter_runs
from number_compiler.arithmetic.fields.morphism_core import AffineCocycle, binary_power
from number_compiler.arithmetic.fields.radix import (
    bit_width,
    digits_lsd,
    symbol_runs,
)


@dataclass(frozen=True, slots=True)
class FactoredCongruenceState:
    residues: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class FactoredAffineMorphism:
    """Affine map on every component of one fixed factored modulus carrier."""

    moduli: tuple[int, ...]
    multipliers: tuple[int, ...]
    offsets: tuple[int, ...]
    symbols: int = 0
    compositions: int = 0

    def __post_init__(self) -> None:
        mods = tuple(map(int, self.moduli))
        if not mods or any(m <= 1 for m in mods):
            raise ValueError(mods)
        if len(self.multipliers) != len(mods) or len(self.offsets) != len(mods):
            raise ValueError("factored affine arity mismatch")
        object.__setattr__(self, "moduli", mods)
        object.__setattr__(
            self,
            "multipliers",
            tuple(int(a) % m for a, m in zip(self.multipliers, mods)),
        )
        object.__setattr__(
            self, "offsets", tuple(int(c) % m for c, m in zip(self.offsets, mods))
        )
        if self.symbols < 0 or self.compositions < 0:
            raise ValueError((self.symbols, self.compositions))

    @classmethod
    def identity(cls, moduli: Sequence[int]) -> FactoredAffineMorphism:
        mods = tuple(map(int, moduli))
        return cls(mods, tuple(1 % m for m in mods), (0,) * len(mods), 0, 0)

    @classmethod
    def digit(
        cls, moduli: Sequence[int], radix: int, digit: int
    ) -> FactoredAffineMorphism:
        mods = tuple(map(int, moduli))
        radix = int(radix)
        digit = int(digit)
        if radix < 2 or not 0 <= digit < radix:
            raise ValueError((radix, digit))
        return cls(
            mods, tuple(radix % m for m in mods), tuple(digit % m for m in mods), 1, 0
        )

    @classmethod
    def additive(cls, moduli: Sequence[int], delta: int) -> FactoredAffineMorphism:
        mods = tuple(map(int, moduli))
        delta = int(delta)
        return cls(mods, tuple(1 for _ in mods), tuple(delta % m for m in mods), 1, 0)

    @property
    def cocycle(self) -> AffineCocycle[tuple[int, ...]]:
        return AffineCocycle(self.multipliers, self.offsets)

    def _then_raw(self, other: FactoredAffineMorphism) -> FactoredAffineMorphism:
        if self.moduli != other.moduli:
            raise ValueError("incompatible factored modulus carriers")

        def multiply(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
            return tuple((x * y) % m for x, y, m in zip(a, b, self.moduli))

        def add(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
            return tuple((x + y) % m for x, y, m in zip(a, b, self.moduli))

        cocycle = self.cocycle.then(other.cocycle, multiply=multiply, add=add)
        return FactoredAffineMorphism(
            self.moduli,
            cocycle.multiplier,
            cocycle.addend,
            self.symbols + other.symbols,
            0,
        )

    def then(self, other: FactoredAffineMorphism) -> FactoredAffineMorphism:
        out = self._then_raw(other)
        return FactoredAffineMorphism(
            out.moduli,
            out.multipliers,
            out.offsets,
            out.symbols,
            self.compositions + other.compositions + 1,
        )

    def power(self, exponent: int) -> FactoredAffineMorphism:
        """Repeat this map through the shared binary-power kernel."""
        base = FactoredAffineMorphism(
            self.moduli, self.multipliers, self.offsets, self.symbols, 0
        )
        powered = binary_power(
            base,
            exponent,
            identity=FactoredAffineMorphism.identity(self.moduli),
            compose=FactoredAffineMorphism._then_raw,
        )
        result = powered.value
        return FactoredAffineMorphism(
            result.moduli,
            result.multipliers,
            result.offsets,
            result.symbols,
            powered.compositions,
        )

    def apply(self, state: FactoredCongruenceState) -> FactoredCongruenceState:
        if len(state.residues) != len(self.moduli):
            raise ValueError((len(state.residues), len(self.moduli)))
        return FactoredCongruenceState(
            tuple(
                (a * int(r) + c) % m
                for r, a, c, m in zip(
                    state.residues, self.multipliers, self.offsets, self.moduli
                )
            )
        )

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("factored_affine", self.moduli, self.multipliers, self.offsets)

    @property
    def description_bits(self) -> int:
        return sum(
            bit_width(m) + bit_width(a) + bit_width(c)
            for m, a, c in zip(self.moduli, self.multipliers, self.offsets)
        )


def compile_radix_runs_morphism(
    moduli: Sequence[int], runs_msf: Iterable[tuple[int, int]], *, radix: int
) -> FactoredAffineMorphism:
    """Compile a most-significant-first RLE digit word without expanding runs."""
    result = FactoredAffineMorphism.identity(moduli)
    for digit, count in runs_msf:
        count = int(count)
        if count < 0:
            raise ValueError(count)
        if count:
            result = result.then(
                FactoredAffineMorphism.digit(moduli, radix, int(digit)).power(count)
            )
    return result


def compile_word_morphism(
    moduli: Sequence[int], word_msf: CanonicalWord, *, radix: int
) -> FactoredAffineMorphism:
    return compile_radix_runs_morphism(moduli, iter_runs(word_msf), radix=radix)


@dataclass(frozen=True, slots=True)
class MixedRadixEncoding:
    """Exact periodic mixed-radix representation, least-significant digit first."""

    digits: tuple[int, ...]
    bases: tuple[int, ...]

    def __post_init__(self) -> None:
        if not self.digits or len(self.digits) != len(self.bases):
            raise ValueError((len(self.digits), len(self.bases)))
        if any(b < 2 or not 0 <= d < b for d, b in zip(self.digits, self.bases)):
            raise ValueError(self)

    @property
    def value(self) -> int:
        out = 0
        for digit, base in reversed(tuple(zip(self.digits, self.bases))):
            out = int(base) * out + int(digit)
        return out

    @property
    def payload_bits(self) -> int:
        return sum(max(1, (b - 1).bit_length()) for b in self.bases)


def encode_periodic_mixed_radix(value: int, bases: Sequence[int]) -> MixedRadixEncoding:
    value = int(value)
    period = tuple(map(int, bases))
    if value < 0 or not period or any(b < 2 for b in period):
        raise ValueError((value, period))
    if value == 0:
        return MixedRadixEncoding((0,), (period[0],))
    digits: list[int] = []
    used: list[int] = []
    n = value
    i = 0
    while n:
        base = period[i % len(period)]
        n, digit = divmod(n, base)
        digits.append(digit)
        used.append(base)
        i += 1
    result = MixedRadixEncoding(tuple(digits), tuple(used))
    if result.value != value:
        raise AssertionError((value, result))
    return result


def mixed_radix_morphism(
    moduli: Sequence[int], encoding: MixedRadixEncoding
) -> FactoredAffineMorphism:
    """Compile an exact mixed-radix number from MS digit to LS digit."""
    out = FactoredAffineMorphism.identity(moduli)
    for i in range(len(encoding.digits) - 1, -1, -1):
        out = out.then(
            FactoredAffineMorphism.digit(moduli, encoding.bases[i], encoding.digits[i])
        )
    return out


def binary_digit_reinterpretation_morphism(
    moduli: Sequence[int], value: int, target_base: int
) -> FactoredAffineMorphism:
    """Compile the binary 0/1 word of ``value`` while evaluating it in another radix.

    This is the morphism counterpart of :func:`reinterpret_binary_digits`.
    It does *not* preserve the arithmetic value unless ``target_base==2``; it
    preserves the digit language exactly and therefore exposes cyclotomic word
    identities such as Mersenne repunits and Fermat two-spike words.
    """
    value, target_base = int(value), int(target_base)
    if value < 0 or target_base < 2:
        raise ValueError((value, target_base))
    bits_msf = tuple(reversed(digits_lsd(value, 2)))
    return compile_radix_runs_morphism(moduli, symbol_runs(bits_msf), radix=target_base)


def reinterpret_binary_digits(value: int, target_base: int) -> int:
    """Interpret the *same* binary digit string as digits in ``target_base``."""
    value, target_base = int(value), int(target_base)
    if value < 0 or target_base < 2:
        raise ValueError((value, target_base))
    bits = digits_lsd(value, 2)
    return sum(int(bit) * pow(target_base, i) for i, bit in enumerate(bits))


def undo_binary_digit_reinterpretation(encoded: int, source_base: int) -> int:
    """Inverse of :func:`reinterpret_binary_digits` on its 0/1 digit image."""
    encoded, source_base = int(encoded), int(source_base)
    if encoded < 0 or source_base < 2:
        raise ValueError((encoded, source_base))
    digits = digits_lsd(encoded, source_base)
    if any(d not in (0, 1) for d in digits):
        raise ValueError("value is outside the binary-digit reinterpretation image")
    return sum(int(bit) << i for i, bit in enumerate(digits))


__all__ = [
    "FactoredAffineMorphism",
    "FactoredCongruenceState",
    "MixedRadixEncoding",
    "binary_digit_reinterpretation_morphism",
    "compile_radix_runs_morphism",
    "compile_word_morphism",
    "encode_periodic_mixed_radix",
    "mixed_radix_morphism",
    "reinterpret_binary_digits",
    "undo_binary_digit_reinterpretation",
]
