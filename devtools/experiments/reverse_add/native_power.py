"""Bounded expression-plane reference for reverse/add temporal powers.

The important contract in this module is representational, not merely
extensional: :func:`native_two_step` never constructs the first successor as a
``FormulaRoot`` and never calls :func:`number_compiler.arithmetic.formula.derived.successor`.

For source pair planes ``S`` we build, in one formula DAG,

    S -> L/R -> tau(S,L,R) -> K(tau) -> S2(S,L,R,K)

where ``tau`` is an internal tuple of hash-consed :class:`Expr` planes.
Although intermediate FormulaRoot objects are absent, the arbitrary-duration
constructor still chains successor expression planes and stores growth/width
histories. It is not the source-bound pumped cylinder grammar and must not be
installed as a production constructor.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass

from number_compiler.arithmetic.fields.digit_formula import DigitSpec
from number_compiler.arithmetic.formula.formula import (
    FormulaArena,
    FormulaRoot,
    canonical_root_key,
)
from number_compiler.arithmetic.formula.pair_algebra import (
    branch_coefficient_planes,
    carry_plane_scan,
    check_pair_planes,
    threshold_plane_views,
)
from number_compiler.arithmetic.formula.types import Expr, RadixSpec


@dataclass(frozen=True, slots=True)
class NativeTwoStepCompilation:
    """Public result of one native two-step formula construction.

    Only final semantic roots are retained.  In particular, the internal
    first-step coefficient family ``tau`` and second carry ``K`` are not stored
    here or in arena metadata.
    """

    pair: FormulaRoot
    first_growth: int
    second_growth: int
    source_width: int
    first_width: int

    @property
    def growth(self) -> int:
        return self.first_growth + self.second_growth


@dataclass(frozen=True, slots=True)
class NativePowerCompilation:
    """Exact arbitrary finite power with all intermediate states eliminated.

    ``growths``/``widths`` are scalar observations of this *closed* source.
    Intermediate pair families remain lexical ``Expr`` tuples and are never
    promoted to ``FormulaRoot`` or cache identities.  Construction is linear in
    ``steps`` and therefore is a semantic/reference compiler, not the strict
    binary ``J_0/J_1`` backend.
    """

    pair: FormulaRoot
    growths: tuple[int, ...]
    widths: tuple[int, ...]

    @property
    def steps(self) -> int:
        return len(self.growths)

    @property
    def growth(self) -> int:
        return sum(self.growths)


@dataclass(frozen=True, slots=True)
class NativeFourStepCompilation:
    """Result of one algebraically eliminated four-step construction.

    Only the final pair root and scalar growth/width events survive.  The three
    intermediate pair coefficient families are lexical Expr tuples and are not
    semantic/cache objects.
    """

    pair: FormulaRoot
    growths: tuple[int, int, int, int]
    widths: tuple[int, int, int, int, int]

    @property
    def growth(self) -> int:
        return sum(self.growths)


def _normalized_digit_root(
    arena: FormulaArena,
    pair_planes: Sequence[Expr],
    carry: Expr,
    growth: int,
    spec: RadixSpec,
) -> FormulaRoot:
    """Exact digits obtained by normalizing an inline pair coefficient family."""
    pair_planes = check_pair_planes(pair_planes, spec)
    width = pair_planes[0].width
    if carry.width != width:
        raise ValueError((carry.width, width))
    incoming = arena.shl(carry, 1)
    dspec = DigitSpec(spec.base)
    args = pair_planes + (incoming, carry)
    planes = tuple(
        arena.coeffmap("DIGIT_NORMALIZE", bit, spec.base, spec.plane_count, args)
        for bit in range(dspec.plane_count)
    )
    if not growth:
        return FormulaRoot(planes)

    # K_width = 1 is the ordinary terminal radix carry, so append final digit 1.
    out_width = width + 1
    terminal = arena.range_mask(width, out_width, out_width)
    out: list[Expr] = []
    for bit, plane in enumerate(planes):
        extended = arena.resize(plane, out_width)
        if bit == 0:
            extended = arena.or_(extended, terminal)
        out.append(extended)
    return FormulaRoot(tuple(out))


def _native_first_inline(
    arena: FormulaArena,
    source: FormulaRoot,
    spec: RadixSpec,
) -> tuple[tuple[Expr, ...], int]:
    """Return the internal first coefficient family ``tau`` and ``g1`` only."""
    if source.plane_count != spec.plane_count:
        raise ValueError((source.plane_count, spec.plane_count))
    _carry, tau, growth, _width = _native_step(arena, source.planes, spec)
    return tau, growth


def _native_step(
    arena: FormulaArena,
    planes: tuple[Expr, ...],
    spec: RadixSpec,
) -> tuple[Expr, tuple[Expr, ...], int, int]:
    carry = carry_plane_scan(arena, planes, spec)
    growth = arena.eval_closed_bit(carry, planes[0].width - 1)
    next_planes = branch_coefficient_planes(arena, planes, growth, spec, carry)
    return carry, next_planes, growth, next_planes[0].width


_NativeStep = tuple[Expr, tuple[Expr, ...], int, int]


def _native_two_step_terms(
    arena: FormulaArena,
    source: FormulaRoot,
    spec: RadixSpec,
) -> tuple[tuple[Expr, ...], Expr, int, int]:
    """Build only the eliminated internal terms ``tau,K`` and growth events.

    The returned Expr families are lexical temporaries.  Callers must not place
    them in arena metadata or promote ``tau`` to FormulaRoot.
    """
    tau, g1 = _native_first_inline(arena, source, spec)
    Kout, _next, g2, _width = _native_step(arena, tau, spec)
    return tau, Kout, g1, g2


def compile_native_two_step(
    arena: FormulaArena,
    source: FormulaRoot,
    spec: RadixSpec,
) -> NativeTwoStepCompilation:
    """Compile the exact native two-step recurrence into one formula DAG.

    Construction is exactly::

        S -> L/R -> tau(S,L,R) -> K(tau) -> S2(tau,K)

    ``tau`` is an internal Expr family.  No FormulaRoot is constructed for it,
    no first-step summary/value sets are registered, and ``successor()`` is not
    called.  Width events are obtained from the two terminal carry predicates;
    this API therefore expects a closed source formula, as does the ordinary
    reference successor path used by this package.
    """
    if source.plane_count != spec.plane_count:
        raise ValueError((source.plane_count, spec.plane_count))

    cache_key = ("native-two-step", spec.base, canonical_root_key(source))
    cached = arena.metadata_get(cache_key)
    if isinstance(cached, NativeTwoStepCompilation):
        return cached

    tau, Kout, g1, g2 = _native_two_step_terms(arena, source, spec)
    first_width = tau[0].width

    # S^(2) is the ordinary pair recurrence on tau,K, but tau here is only an
    # Expr definition family.  Hash-consed references perform algebraic
    # substitution in the same final DAG; there is no S[t+1] semantic root.
    pair_planes = branch_coefficient_planes(arena, tau, g2, spec, Kout)
    pair = FormulaRoot(pair_planes)

    compiled = NativeTwoStepCompilation(
        pair=pair,
        first_growth=g1,
        second_growth=g2,
        source_width=source.width,
        first_width=first_width,
    )
    # Cache only the completed native operator result.  tau/K are not retained
    # as independently addressable compiler or semantic objects.
    arena.metadata_set(cache_key, compiled)
    return compiled


def native_two_step(
    arena: FormulaArena, source: FormulaRoot, spec: RadixSpec
) -> FormulaRoot:
    """Return the native exact ``T^2`` pair FormulaRoot."""
    return compile_native_two_step(arena, source, spec).pair


def native_two_step_digits(
    arena: FormulaArena, source: FormulaRoot, spec: RadixSpec
) -> FormulaRoot:
    """Return exact radix digits two reverse-add steps after ``source``.

    The digit projector shares the same eliminated equations but is intentionally
    lazy: calling ``native_two_step()`` does not pay for digit-output nodes.
    """
    cache_key = ("native-two-step-digits", spec.base, canonical_root_key(source))
    cached = arena.metadata_get(cache_key)
    if isinstance(cached, FormulaRoot):
        return cached
    tau, Kout, _g1, g2 = _native_two_step_terms(arena, source, spec)
    digits = _normalized_digit_root(arena, tau, Kout, g2, spec)
    arena.metadata_set(cache_key, digits)
    return digits


def _native_four_step_chain(
    arena: FormulaArena,
    source: FormulaRoot,
    spec: RadixSpec,
) -> tuple[_NativeStep, _NativeStep, _NativeStep, _NativeStep]:
    """Build the four lexical native steps once for either observer."""
    c1, tau1, g1, w1 = _native_step(arena, source.planes, spec)
    c2, tau2, g2, w2 = _native_step(arena, tau1, spec)
    c3, tau3, g3, w3 = _native_step(arena, tau2, spec)
    c4, tau4, g4, w4 = _native_step(arena, tau3, spec)
    return (
        (c1, tau1, g1, w1),
        (c2, tau2, g2, w2),
        (c3, tau3, g3, w3),
        (c4, tau4, g4, w4),
    )


def compile_native_four_step(
    arena: FormulaArena,
    source: FormulaRoot,
    spec: RadixSpec,
) -> NativeFourStepCompilation:
    """Compile native ``T^4`` from the four-step equations in one formula DAG.

    This function intentionally does not call ``successor()``,
    ``compile_native_two_step()`` or ``native_two_step()``.  Each intermediate
    coefficient family is a root-free Expr definition that is immediately
    substituted into the next carry scan / pair formula.
    """
    if source.plane_count != spec.plane_count:
        raise ValueError((source.plane_count, spec.plane_count))
    cache_key = ("native-four-step", spec.base, canonical_root_key(source))
    cached = arena.metadata_get(cache_key)
    if isinstance(cached, NativeFourStepCompilation):
        return cached

    (
        (_unused_c1_binding, _unused_tau1_binding, g1, w1),
        (_unused_c2_binding, _unused_tau2_binding, g2, w2),
        (_unused_c3_binding, _unused_tau3_binding, g3, w3),
        (
            _unused_c4_binding,
            _tau4,
            g4,
            _w4,
        ),
    ) = _native_four_step_chain(arena, source, spec)
    pair = FormulaRoot(_tau4)

    compiled = NativeFourStepCompilation(
        pair=pair,
        growths=(g1, g2, g3, g4),
        widths=(source.width, w1, w2, w3, pair.width),
    )
    arena.metadata_set(cache_key, compiled)
    return compiled


def native_four_step(
    arena: FormulaArena, source: FormulaRoot, spec: RadixSpec
) -> FormulaRoot:
    """Return native exact ``T^4`` without composing two T^2 semantic roots."""
    return compile_native_four_step(arena, source, spec).pair


def native_four_step_digits(
    arena: FormulaArena, source: FormulaRoot, spec: RadixSpec
) -> FormulaRoot:
    """Return exact radix digits four reverse-add steps after ``source``."""
    cache_key = ("native-four-step-digits", spec.base, canonical_root_key(source))
    cached = arena.metadata_get(cache_key)
    if isinstance(cached, FormulaRoot):
        return cached

    # Rebuild the eliminated lexical terms.  Hash-consing reuses any nodes
    # already created by native_four_step(), but no intermediate root/cache key
    # is introduced.
    _step1, _step2, (_c3, tau3, _g3, _w3), (c4, _tau4, g4, _w4) = (
        _native_four_step_chain(arena, source, spec)
    )
    digits = _normalized_digit_root(arena, tau3, c4, g4, spec)
    arena.metadata_set(cache_key, digits)
    return digits


def compile_native_power(
    arena: FormulaArena,
    source: FormulaRoot,
    steps: int,
    spec: RadixSpec,
) -> NativePowerCompilation:
    """Compile ``T**steps`` into one final FormulaRoot without semantic intermediates.

    This generalizes the native T²/T⁴ construction to any finite non-negative
    ``steps``.  Every temporal layer is substituted as an internal ``Expr``
    definition family.  Only the completed pair root receives a cache identity.

    The closed-source growth event at each layer is still selected with
    ``eval_closed_bit``.  Consequently this routine is intentionally *not*
    callable from ``powered_jump_scope`` and is not evidence for an unbounded
    polylogarithmic J backend.  Its role is an exact eliminated-equation oracle
    and a direct construction target for residual-lowering research.
    """
    steps = int(steps)
    if steps < 0:
        raise ValueError(steps)
    if source.plane_count != spec.plane_count:
        raise ValueError((source.plane_count, spec.plane_count))
    if steps == 0:
        return NativePowerCompilation(source, (), (source.width,))

    cache_key = ("native-power", steps, spec.base, canonical_root_key(source))
    cached = arena.metadata_get(cache_key)
    if isinstance(cached, NativePowerCompilation):
        return cached

    family: tuple[Expr, ...] = tuple(source.planes)
    widths = [source.width]
    growths: list[int] = []
    for _ in range(steps):
        carry = carry_plane_scan(arena, family, spec)
        growth = arena.eval_closed_bit(carry, family[0].width - 1)
        growths.append(growth)
        family = branch_coefficient_planes(arena, family, growth, spec, carry)
        widths.append(family[0].width)

    compiled = NativePowerCompilation(
        pair=FormulaRoot(family),
        growths=tuple(growths),
        widths=tuple(widths),
    )
    arena.metadata_set(cache_key, compiled)
    return compiled


def native_power(
    arena: FormulaArena,
    source: FormulaRoot,
    steps: int,
    spec: RadixSpec,
) -> FormulaRoot:
    """Return the exact eliminated ``T**steps`` pair root."""
    return compile_native_power(arena, source, steps, spec).pair


def native_power_digits(
    arena: FormulaArena,
    source: FormulaRoot,
    steps: int,
    spec: RadixSpec,
) -> FormulaRoot:
    """Return exact radix digits ``steps`` reverse-add transitions later.

    Pair fields determine the *next* normalized number, so this projector is
    defined for positive powers.  ``steps == 0`` cannot in general recover the
    original digit word from pair sums alone.
    """
    steps = int(steps)
    if steps <= 0:
        raise ValueError("native_power_digits requires steps >= 1")
    if source.plane_count != spec.plane_count:
        raise ValueError((source.plane_count, spec.plane_count))
    cache_key = ("native-power-digits", steps, spec.base, canonical_root_key(source))
    cached = arena.metadata_get(cache_key)
    if isinstance(cached, FormulaRoot):
        return cached

    family: tuple[Expr, ...] = tuple(source.planes)
    final_carry: Expr | None = None
    final_growth = 0
    for step in range(1, steps + 1):
        carry = carry_plane_scan(arena, family, spec)
        growth = arena.eval_closed_bit(carry, family[0].width - 1)
        if step == steps:
            final_carry = carry
            final_growth = growth
            break
        family = branch_coefficient_planes(arena, family, growth, spec, carry)
    if final_carry is None:
        raise AssertionError("missing final carry")
    digits = _normalized_digit_root(arena, family, final_carry, final_growth, spec)
    arena.metadata_set(cache_key, digits)
    return digits


def native_two_step_reset_sets(
    arena: FormulaArena,
    source: FormulaRoot,
    spec: RadixSpec,
) -> tuple[Expr, Expr, Expr]:
    """Return ``(M2_<, M2_=, M2_>)`` directly over the original source.

    These are exactly ``[tau<b-1]``, ``[tau=b-1]`` and ``[tau>b-1]`` after
    substituting the inline first-step coefficient formulas.  No ``Y_v`` or
    intermediate FormulaRoot is created.
    """
    tau, _g1 = _native_first_inline(arena, source, spec)
    return threshold_plane_views(arena, tau, spec)


def native_two_step_value_sets(
    arena: FormulaArena,
    source: FormulaRoot,
    spec: RadixSpec,
) -> tuple[Expr, ...]:
    """Return final exact sets ``Z_w={i:S^(2)_i=w}`` for ``w=0..2b-2``.

    No first-step ``Y_v`` set family is ever constructed.
    """
    pair = native_two_step(arena, source, spec)
    return tuple(
        arena.predicate("EQ", value, pair.planes) for value in range(spec.pair_max + 1)
    )


__all__ = [
    "NativeFourStepCompilation",
    "NativePowerCompilation",
    "NativeTwoStepCompilation",
    "compile_native_four_step",
    "compile_native_power",
    "compile_native_two_step",
    "native_four_step",
    "native_four_step_digits",
    "native_power",
    "native_power_digits",
    "native_two_step",
    "native_two_step_digits",
    "native_two_step_reset_sets",
    "native_two_step_value_sets",
]
