"""Shared logarithmic-depth spatial prefix monoid compiler.

A fixed finite monoid is represented by its ``after o before`` composition
matrix.  Local one-hot element masks are lifted by a Hillis--Steele style
parallel prefix.  Every stage doubles the covered spatial interval, so the
formula depth is ``ceil(log2(width))`` while a random-access query evaluates
only the dependency cone for the requested position.

This is the single owner of spatial prefix composition used by reverse/add
carry actions and generic radix digit transducers (including Collatz).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from number_compiler.arithmetic.formula.formula import FormulaArena
from number_compiler.arithmetic.formula.types import Expr


@dataclass(frozen=True, slots=True)
class FiniteMonoid:
    """Canonical finite monoid table.

    ``composition[after][before]`` is ``after o before``.  Elements are dense
    integer ids ``0..size-1``.
    """

    composition: tuple[tuple[int, ...], ...]
    identity: int

    def __post_init__(self) -> None:
        rows = tuple(tuple(map(int, row)) for row in self.composition)
        n = len(rows)
        if n <= 0 or any(len(row) != n for row in rows):
            raise ValueError("composition table must be nonempty and square")
        if not 0 <= int(self.identity) < n:
            raise ValueError(self.identity)
        if any(not 0 <= value < n for row in rows for value in row):
            raise ValueError("composition escapes monoid")
        ident = int(self.identity)
        for x in range(n):
            if rows[ident][x] != x or rows[x][ident] != x:
                raise ValueError("identity row/column is invalid")
        # Exhaustive associativity validation is cubic in the monoid size.
        # Production carry/character monoids are tiny, so prove those directly.
        # Larger digit-transducer monoids are generated from exact function
        # composition; re-proving associativity here would turn validation into
        # an eager O(|M|^3) hot-path cost.
        if n <= 16:
            for a in range(n):
                for b in range(n):
                    ab = rows[a][b]
                    for c in range(n):
                        if rows[ab][c] != rows[a][rows[b][c]]:
                            raise ValueError("composition table is not associative")
        object.__setattr__(self, "composition", rows)
        object.__setattr__(self, "identity", ident)

    @property
    def size(self) -> int:
        return len(self.composition)


@dataclass(frozen=True, slots=True)
class FormulaPrefixMonoidProjection:
    """One-hot inclusive prefix products over a spatial formula word."""

    masks: tuple[Expr, ...]
    monoid: FiniteMonoid
    stages: int

    def __post_init__(self) -> None:
        if len(self.masks) != self.monoid.size or not self.masks:
            raise ValueError((len(self.masks), self.monoid.size))
        width = self.masks[0].width
        if width <= 0 or any(mask.width != width for mask in self.masks):
            raise ValueError("prefix masks must have one positive common width")
        if self.stages < 0:
            raise ValueError(self.stages)

    @property
    def width(self) -> int:
        return self.masks[0].width

    def state_at(self, arena: FormulaArena, position: int) -> int:
        """Return one inclusive prefix element at one coordinate.

        Evaluation is random access: no earlier coordinate is recursively
        evaluated.  The reached formula depth is bounded by ``stages`` plus the
        local-symbol predicate depth.
        """
        position = int(position)
        if not 0 <= position < self.width:
            raise IndexError(position)
        hits = [
            element
            for element, mask in enumerate(self.masks)
            if arena.eval_closed_bit(mask, position)
        ]
        if len(hits) != 1:
            raise AssertionError((position, hits))
        return int(hits[0])


def compile_formula_prefix_monoid(
    arena: FormulaArena,
    local_masks: Sequence[Expr],
    monoid: FiniteMonoid,
) -> FormulaPrefixMonoidProjection:
    """Compile inclusive prefix products in logarithmic spatial depth.

    ``local_masks[e][i]`` must be one-hot and mean that local position ``i``
    contributes monoid element ``e``.  The compiler intentionally retains only
    vector formulas; it never creates one Python node per spatial coordinate.
    """
    stage = tuple(local_masks)
    if len(stage) != monoid.size or not stage:
        raise ValueError((len(stage), monoid.size))
    width = stage[0].width
    if width <= 0 or any(mask.width != width for mask in stage):
        raise ValueError("local masks must share positive width")

    offset = 1
    stages = 0
    while offset < width:
        # Positions without a preceding block receive the identity element.
        prefix = arena.range_mask(0, min(offset, width), width)
        shifted = []
        for element, mask in enumerate(stage):
            z = arena.shl(mask, offset)
            if element == monoid.identity:
                z = arena.or_(z, prefix)
            shifted.append(z)

        groups: list[list[Expr]] = [[] for _ in range(monoid.size)]
        for after in range(monoid.size):
            for before in range(monoid.size):
                result = monoid.composition[after][before]
                groups[result].append(arena.and_(stage[after], shifted[before]))
        stage = tuple(arena.or_many(items, width) for items in groups)
        offset <<= 1
        stages += 1

    return FormulaPrefixMonoidProjection(stage, monoid, stages)


PREDICATE_AND_MONOID = FiniteMonoid(
    (
        (0, 0),  # False & x
        (0, 1),  # True & x = x
    ),
    1,
)


@dataclass(frozen=True, slots=True)
class FormulaPrefixPredicateProjection:
    """Inclusive ``all(predicate)`` prefixes with first-failure rank/select.

    Prefix truth is monotone: once one local position fails, every longer
    prefix fails.  The local predicate is therefore compiled through the same
    finite spatial monoid as carry actions, and the first failure is selected
    with logarithmically many random-access prefix queries instead of a scan.
    """

    prefix: FormulaPrefixMonoidProjection

    @property
    def width(self) -> int:
        return self.prefix.width

    @property
    def stages(self) -> int:
        return self.prefix.stages

    def prefix_holds_at(self, arena: FormulaArena, position: int) -> bool:
        return self.prefix.state_at(arena, int(position)) == 1

    def first_false(self, arena: FormulaArena) -> int:
        """Return the first failing coordinate, or ``width`` if none fails."""
        lo, hi = 0, self.width
        while lo < hi:
            arena.metadata_increment("prefix_predicate_select_probes")
            mid = (lo + hi) // 2
            if self.prefix_holds_at(arena, mid):
                lo = mid + 1
            else:
                hi = mid
        return lo


def compile_formula_prefix_predicate(
    arena: FormulaArena,
    predicate: Expr,
) -> FormulaPrefixPredicateProjection:
    """Compile a closed local predicate into an exact first-failure index."""
    key = ("formula-prefix-predicate", predicate.id, predicate.width)
    cached = arena.metadata_get(key)
    if isinstance(cached, FormulaPrefixPredicateProjection):
        return cached
    prefix = compile_formula_prefix_monoid(
        arena,
        (arena.not_(predicate), predicate),
        PREDICATE_AND_MONOID,
    )
    out = FormulaPrefixPredicateProjection(prefix)
    arena.metadata_set(key, out)
    return out


RESET_PREFIX_MONOID = FiniteMonoid(
    (
        (0, 0, 0),  # RESET0 o anything
        (0, 1, 2),  # ID o x = x
        (2, 2, 2),  # RESET1 o anything
    ),
    1,
)


def compile_reset_prefix_monoid(
    arena: FormulaArena,
    reset0: Expr,
    propagate: Expr,
    reset1: Expr,
) -> FormulaPrefixMonoidProjection:
    """Compile the three reset/propagate carry functions in two masks.

    The monoid elements are ``RESET0, ID, RESET1``.  A prefix function is
    represented by ``P`` (the function is ID) and ``G`` (its output on input
    zero is one).  Composition ``after o before`` is therefore

        P' = P_after & P_before
        G' = G_after | (P_after & G_before).

    This is the same finite monoid as the generic one-hot compiler but avoids
    constructing/evaluating three one-hot masks at every spatial doubling
    stage.  The returned projection is still one-hot for shared random-access
    consumers.
    """
    if not (reset0.width == propagate.width == reset1.width) or reset0.width <= 0:
        raise ValueError("reset/propagate masks must share positive width")
    width = reset0.width
    p = propagate
    g = reset1
    offset = 1
    stages = 0
    while offset < width:
        leading_identity = arena.range_mask(0, min(offset, width), width)
        before_p = arena.or_(arena.shl(p, offset), leading_identity)
        before_g = arena.shl(g, offset)
        g = arena.or_(g, arena.and_(p, before_g))
        p = arena.and_(p, before_p)
        offset <<= 1
        stages += 1
    # Exact one-hot view of the same prefix function.
    const1 = g
    ident = p
    const0 = arena.not_(arena.or_(p, g))
    return FormulaPrefixMonoidProjection(
        (const0, ident, const1), RESET_PREFIX_MONOID, stages
    )


__all__ = [
    "FiniteMonoid",
    "FormulaPrefixMonoidProjection",
    "compile_formula_prefix_monoid",
    "PREDICATE_AND_MONOID",
    "FormulaPrefixPredicateProjection",
    "compile_formula_prefix_predicate",
    "RESET_PREFIX_MONOID",
    "compile_reset_prefix_monoid",
]
