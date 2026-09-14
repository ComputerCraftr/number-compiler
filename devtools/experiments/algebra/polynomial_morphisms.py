"""Canonical lazy polynomial morphisms for arithmetic-progression products.

This research utility separates a predictable product *operator* from its
coefficient materialization.  A block

    P(a,s,n; X) = prod_{j=0}^{n-1} (X - (a + j*s))

is represented by the constant-field descriptor ``(a,s,n)``.  Adjacent blocks
compose exactly, and dyadic doubling is just composition with the translated
copy.  Coefficients are lowered only when an observer (for example a remainder
or support GCD) actually needs them.

The descriptor is compact; materializing a degree-n polynomial is not.  The
arena therefore reports coefficient work/cache size separately so callers
cannot mistake operator compression for an asymptotic arithmetic result.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from math import gcd

from number_compiler.arithmetic.fields.morphism_core import LazyLoweringCache
from number_compiler.arithmetic.fields.radix import bit_width

Polynomial = tuple[int, ...]
PolyMultiply = Callable[[Polynomial, Polynomial], Polynomial]


@dataclass(frozen=True, slots=True)
class ProgressionProductShape:
    """Canonical progression-product structure modulo affine coordinate action.

    Translation is always gauge.  When ``root_step`` is a unit modulo the
    modulus, scale is gauge as well, so every unit-step progression of the same
    width shares one shape.  Nonunit steps remain in the shape because scaling
    by them is not invertible in the candidate ring.
    """

    modulus: int
    count: int
    step_class: int | None

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "progression-product-shape",
            self.modulus,
            self.count,
            "unit" if self.step_class is None else self.step_class,
        )

    @property
    def split_counts(self) -> tuple[int, int]:
        if self.count <= 1:
            raise ValueError("cannot split a zero/one-root shape")
        left = self.count // 2
        return left, self.count - left


@dataclass(frozen=True, slots=True)
class ProgressionAffineAction:
    """Cheap coordinate action removed before algebraic-shape lookup."""

    root_start: int
    root_step: int


@dataclass(frozen=True, slots=True)
class ProgressionProductMorphism:
    """Monic product over one arithmetic progression of roots."""

    modulus: int
    root_start: int
    root_step: int
    count: int

    def __post_init__(self) -> None:
        modulus = int(self.modulus)
        count = int(self.count)
        if modulus <= 1 or count < 0:
            raise ValueError((modulus, count))
        object.__setattr__(self, "modulus", modulus)
        object.__setattr__(self, "root_start", int(self.root_start) % modulus)
        object.__setattr__(self, "root_step", int(self.root_step) % modulus)
        object.__setattr__(self, "count", count)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "progression-product-morphism",
            self.modulus,
            self.root_start,
            self.root_step,
            self.count,
        )

    @property
    def algebraic_shape(self) -> ProgressionProductShape:
        step_class = None if gcd(self.root_step, self.modulus) == 1 else self.root_step
        return ProgressionProductShape(self.modulus, self.count, step_class)

    @property
    def affine_action(self) -> ProgressionAffineAction:
        return ProgressionAffineAction(self.root_start, self.root_step)

    @property
    def algebraic_key(self) -> tuple[object, ...]:
        return self.algebraic_shape.canonical_key

    @property
    def description_bits(self) -> int:
        return (
            bit_width(self.modulus)
            + bit_width(self.root_start)
            + bit_width(self.root_step)
            + bit_width(self.count)
        )

    @property
    def end_root(self) -> int:
        """Root immediately following this block in the same progression."""
        return (self.root_start + self.count * self.root_step) % self.modulus

    def translated(self, root_delta: int) -> ProgressionProductMorphism:
        return ProgressionProductMorphism(
            self.modulus,
            self.root_start + int(root_delta),
            self.root_step,
            self.count,
        )

    def following(self) -> ProgressionProductMorphism:
        """Same-width block immediately following this block."""
        return ProgressionProductMorphism(
            self.modulus,
            self.end_root,
            self.root_step,
            self.count,
        )

    def then(self, other: ProgressionProductMorphism) -> ProgressionProductMorphism:
        """Concatenate adjacent progression products exactly."""
        if self.modulus != other.modulus or self.root_step != other.root_step:
            raise ValueError((self, other))
        if self.count == 0:
            return other
        if other.count == 0:
            return self
        if other.root_start != self.end_root:
            raise ValueError("progression-product blocks are not adjacent")
        return ProgressionProductMorphism(
            self.modulus,
            self.root_start,
            self.root_step,
            self.count + other.count,
        )

    def doubled(self) -> ProgressionProductMorphism:
        return self.then(self.following())

    def split(self) -> tuple[ProgressionProductMorphism, ProgressionProductMorphism]:
        """Balanced semantic split; no coefficient vector is created."""
        if self.count <= 1:
            raise ValueError("cannot split a zero/one-root product")
        left_count = self.count // 2
        right_count = self.count - left_count
        left = ProgressionProductMorphism(
            self.modulus,
            self.root_start,
            self.root_step,
            left_count,
        )
        right = ProgressionProductMorphism(
            self.modulus,
            left.end_root,
            self.root_step,
            right_count,
        )
        return left, right


class ProgressionProductArena:
    """Interned coefficient lowering for progression-product morphisms.

    A coefficient polynomial is materialized at most once per canonical block
    within the arena.  This removes repeated balanced-product construction
    during remainder descent while keeping the retained coefficient payload
    visible in metrics.
    """

    __slots__ = (
        "_cache",
        "_raw_keys",
        "_shape_by_key",
        "materialized_coefficient_slots",
        "shape_hits",
        "shape_misses",
    )

    def __init__(self) -> None:
        # Coefficients remain an absolute-coordinate lowering cache.  The
        # algebraic structure cache is deliberately upstream of it.
        self._cache: LazyLoweringCache[tuple[object, ...], Polynomial] = (
            LazyLoweringCache()
        )
        self._shape_by_key: dict[tuple[object, ...], ProgressionProductShape] = {}
        self._raw_keys: set[tuple[object, ...]] = set()
        self.shape_hits = 0
        self.shape_misses = 0
        self.materialized_coefficient_slots = 0

    def canonicalize(
        self,
        morphism: ProgressionProductMorphism,
    ) -> tuple[ProgressionProductShape, ProgressionAffineAction]:
        """Intern the algebraic shape before absolute-coordinate lowering."""
        self._raw_keys.add(morphism.canonical_key)
        shape = morphism.algebraic_shape
        key = shape.canonical_key
        old = self._shape_by_key.get(key)
        if old is None:
            self._shape_by_key[key] = shape
            self.shape_misses += 1
            old = shape
        else:
            self.shape_hits += 1
        return old, morphism.affine_action

    @property
    def raw_state_count(self) -> int:
        return len(self._raw_keys)

    @property
    def algebraic_shape_count(self) -> int:
        return len(self._shape_by_key)

    @property
    def algebraic_compression_ratio(self) -> float:
        return self.raw_state_count / max(1, self.algebraic_shape_count)

    def split(
        self,
        morphism: ProgressionProductMorphism,
    ) -> tuple[ProgressionProductMorphism, ProgressionProductMorphism]:
        shape, _action = self.canonicalize(morphism)
        left_count, right_count = shape.split_counts
        left = ProgressionProductMorphism(
            morphism.modulus,
            morphism.root_start,
            morphism.root_step,
            left_count,
        )
        right = ProgressionProductMorphism(
            morphism.modulus,
            left.end_root,
            morphism.root_step,
            right_count,
        )
        return left, right

    @property
    def size(self) -> int:
        return self._cache.size

    @property
    def hits(self) -> int:
        return self._cache.hits

    @property
    def misses(self) -> int:
        return self._cache.misses

    def materialize(
        self,
        morphism: ProgressionProductMorphism,
        *,
        multiply: PolyMultiply,
    ) -> Polynomial:
        """Lower one absolute block only when coefficients are demanded.

        Algebraic shape interning happens first, but coefficients intentionally
        retain their absolute-coordinate cache identity.  The rejected
        shape-coefficient/Taylor transport path was slower on release controls
        and is not kept as a parallel representation.
        """
        pending = [(morphism, False)]
        while pending:
            current, expanded = pending.pop()
            key = current.canonical_key
            if not expanded:
                self.canonicalize(current)
                cached = self._cache.peek(key)
                if cached is not None:

                    def cached_factory(cached: Polynomial = cached) -> Polynomial:
                        return cached

                    self._cache.get_or_lower(key, cached_factory)
                    continue
                if current.count > 1:
                    left, right = self.split(current)
                    pending.extend(((current, True), (right, False), (left, False)))
                    continue
            if current.count == 0:
                output: Polynomial = (1,)
            elif current.count == 1:
                output = ((-current.root_start) % current.modulus, 1)
            else:
                left, right = self.split(current)
                left_output = self._cache.peek(left.canonical_key)
                right_output = self._cache.peek(right.canonical_key)
                assert left_output is not None and right_output is not None
                output = multiply(left_output, right_output)
            self.materialized_coefficient_slots += len(output)

            def output_factory(output: Polynomial = output) -> Polynomial:
                return output

            self._cache.get_or_lower(key, output_factory)
        result = self._cache.peek(morphism.canonical_key)
        assert result is not None
        return result


@dataclass(frozen=True, slots=True)
class NewtonPrecisionMorphism:
    """One exact Newton precision-doubling schedule descriptor.

    This does not claim the inverse coefficients are free.  It makes the
    predictable precision transition explicit so arithmetic work and schedule
    description are measured separately.
    """

    precision: int

    def __post_init__(self) -> None:
        if int(self.precision) < 1:
            raise ValueError(self.precision)
        object.__setattr__(self, "precision", int(self.precision))

    def doubled(self, *, limit: int | None = None) -> NewtonPrecisionMorphism:
        target = self.precision * 2
        if limit is not None:
            target = min(target, int(limit))
        if target < self.precision:
            raise ValueError(limit)
        return NewtonPrecisionMorphism(target)

    @property
    def description_bits(self) -> int:
        return bit_width(self.precision)


__all__ = [
    "NewtonPrecisionMorphism",
    "ProgressionAffineAction",
    "ProgressionProductArena",
    "ProgressionProductMorphism",
    "ProgressionProductShape",
]
