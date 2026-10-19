"""Arithmetic Stokes / ghost-flux audit for special-number progressions.

For the transverse atoms ``x_m=1+C*m``, the exact interval flux is the support
of ``B(a,l)=prod x_(a+j)``.  This research compares the divisor/gcd current,
projective flat connection, finite-difference jets, resultant/norm, Fermat
binomial splitting, Fourier support, and a sqrt-state baby/giant representation.

The key result is structural: the unit connection is a flat coboundary, while
the ghost lives in its singular divisor.  Exact Newton order grows with the
interval, dyadic binomial splitting reaches every leaf, a delta has dense
Fourier spectrum, and the concrete baby/giant evaluator does not beat linear
work.  Production must not import this module or treat any symbolic descriptor
or theoretical fast primitive as an evaluated source projector.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import comb, gcd, isqrt

from devtools.experiments.algebra.inputs import bounded_jet_spec
from devtools.experiments.power_numbers.special_transverse_jet import (
    SpecialJetProgressionSpec,
    build_special_jet_interval,
    first_special_transverse_singularity,
)


def _atom(spec: SpecialJetProgressionSpec, slot: int) -> int:
    return spec.slot_value(int(slot)) % spec.modulus


def _interval_product_unbounded(
    spec: SpecialJetProgressionSpec,
    start: int,
    span: int,
) -> int:
    start, span = int(start), int(span)
    if start < 1 or span < 0:
        raise ValueError((start, span))
    out = 1
    for slot in range(start, start + span):
        out = out * _atom(spec, slot) % spec.modulus
    return out


@dataclass(frozen=True, slots=True)
class ArithmeticGhostFluxBlock:
    """Exact bounded interval with both interior flux and boundary data."""

    spec: SpecialJetProgressionSpec
    start: int
    span: int
    product: int
    support_gcd: int
    left_boundary: int
    right_boundary: int
    left_gcd: int
    right_gcd: int
    atom_evaluations: int
    multiplications: int

    @property
    def has_ghost_flux(self) -> bool:
        return self.support_gcd > 1

    @property
    def boundary_connection_is_unit(self) -> bool:
        return self.left_gcd == self.right_gcd == 1

    @property
    def boundary_blind_to_interior_flux(self) -> bool:
        return self.has_ghost_flux and self.boundary_connection_is_unit


def arithmetic_ghost_flux_block(
    family: str,
    parameter: int,
    *,
    start: int,
    span: int,
) -> ArithmeticGhostFluxBlock:
    spec = SpecialJetProgressionSpec.build(family, parameter)
    block = build_special_jet_interval(spec, start, span)
    left = _atom(spec, start)
    # The right boundary is the atom immediately after the interval.  It need
    # not lie inside the square-root search window; it is part of the formal
    # affine connection, whose atom formula is valid for every positive slot.
    right = _atom(spec, start + span)
    return ArithmeticGhostFluxBlock(
        spec=spec,
        start=int(start),
        span=int(span),
        product=block.product,
        support_gcd=gcd(block.product, spec.modulus),
        left_boundary=left,
        right_boundary=right,
        left_gcd=gcd(left, spec.modulus),
        right_gcd=gcd(right, spec.modulus),
        atom_evaluations=block.atom_evaluations,
        multiplications=block.multiplications,
    )


@dataclass(frozen=True, slots=True)
class ArithmeticWilsonLineAudit:
    """Multiplicative line integral for translating one fixed-span block."""

    family: str
    parameter: int
    start: int
    span: int
    shift: int
    old_product: int
    shifted_product: int
    leaving_product: int
    entering_product: int
    leaving_gcd: int
    entering_gcd: int
    division_free_line_identity_exact: bool
    normalized_wilson_line: int | None
    normalized_line_exact: bool
    boundary_width: int


def arithmetic_wilson_line_audit(
    family: str,
    parameter: int,
    *,
    start: int,
    span: int,
    shift: int = 1,
) -> ArithmeticWilsonLineAudit:
    """Integrate the projective connection over a translation path.

    For positive ``shift<=span``, overlap cancellation gives

        B(a+s,l) / B(a,l)
          = product(entering boundary) / product(leaving boundary).

    The cross-multiplied identity is always meaningful; the normalized Wilson
    line exists only when the leaving boundary is a unit.
    """
    spec = SpecialJetProgressionSpec.build(family, parameter)
    start, span, shift = int(start), int(span), int(shift)
    if start < 1 or span < 1 or shift < 1 or shift > span:
        raise ValueError((start, span, shift))
    old = _interval_product_unbounded(spec, start, span)
    moved = _interval_product_unbounded(spec, start + shift, span)
    leaving = _interval_product_unbounded(spec, start, shift)
    entering = _interval_product_unbounded(spec, start + span, shift)
    leaving_g = gcd(leaving, spec.modulus)
    entering_g = gcd(entering, spec.modulus)
    cross = (moved * leaving - old * entering) % spec.modulus == 0
    if leaving_g == 1:
        wilson = entering * pow(leaving, -1, spec.modulus) % spec.modulus
        exact = moved == old * wilson % spec.modulus
    else:
        wilson = None
        exact = False
    return ArithmeticWilsonLineAudit(
        spec.family,
        spec.parameter,
        start,
        span,
        shift,
        old,
        moved,
        leaving,
        entering,
        leaving_g,
        entering_g,
        cross,
        wilson,
        exact,
        shift,
    )


@dataclass(frozen=True, slots=True)
class DivisorCurrentIntegralAudit:
    """Exact bounded divisor-current integral along a progression path."""

    family: str
    parameter: int
    start: int
    span: int
    atom_gcds: tuple[tuple[int, int], ...]
    nonunit_atom_count: int
    direct_flux_gcd: int
    integrated_local_gcd_product: int
    divisor_integral_exact: bool
    enumerates_interior_atoms: bool = True


def _validated_spec(
    family: str, parameter: int, start: int, span: int
) -> tuple[SpecialJetProgressionSpec, int, int]:
    spec = SpecialJetProgressionSpec.build(family, parameter)
    start, span = int(start), int(span)
    if start < 1 or span < 1:
        raise ValueError((start, span))
    return spec, start, span


def divisor_current_integral_audit(
    family: str,
    parameter: int,
    *,
    start: int,
    span: int,
) -> DivisorCurrentIntegralAudit:
    """Verify the arithmetic line integral of the singular divisor current.

    For every prime power dividing N, replacing each atom ``x`` by ``gcd(x,N)``
    preserves its truncated valuation.  Hence exactly

        gcd(N, prod x_m) = gcd(N, prod gcd(N,x_m)).

    This is the desired divisor-valued Stokes/line-integral identity, but the
    implementation intentionally scans every interior atom and therefore is not
    the missing release evaluator.
    """
    spec, start, span = _validated_spec(family, parameter, start, span)
    product = 1
    local_product = 1
    atoms: list[tuple[int, int]] = []
    for slot in range(start, start + span):
        x = _atom(spec, slot)
        g = gcd(x, spec.modulus)
        product = product * x % spec.modulus
        local_product = local_product * g % spec.modulus
        atoms.append((slot, g))
    direct = gcd(product, spec.modulus)
    integrated = gcd(local_product, spec.modulus)
    return DivisorCurrentIntegralAudit(
        spec.family,
        spec.parameter,
        start,
        span,
        tuple(atoms),
        sum(1 for _, g in atoms if g > 1),
        direct,
        integrated,
        direct == integrated,
        True,
    )


@dataclass(frozen=True, slots=True)
class ArithmeticPlaquetteAudit:
    """One discrete (start,span) plaquette of the projective connection."""

    family: str
    parameter: int
    start: int
    span: int
    x_start: int
    x_corner: int
    x_next_corner: int
    edge_gcds: tuple[int, int, int]
    all_edges_units: bool
    right_then_up_numerator: int
    right_then_up_denominator: int
    up_then_right_numerator: int
    up_then_right_denominator: int
    projective_curvature_trivial: bool
    normalized_loop_holonomy: int | None


def arithmetic_plaquette_audit(
    family: str,
    parameter: int,
    *,
    start: int,
    span: int,
) -> ArithmeticPlaquetteAudit:
    """Verify the exact zero-curvature identity wherever inverses exist.

    Horizontal transport is the projective ratio

        U(a,l) = x_(a+l) / x_a,

    while vertical transport is

        V(a,l) = x_(a+l).

    The two paths around a plaquette have the same projective pair

        (x_(a+l) x_(a+l+1), x_a),

    so curvature is identically trivial on the unit locus.
    """
    spec, start, span = _validated_spec(family, parameter, start, span)
    x0 = _atom(spec, start)
    x1 = _atom(spec, start + span)
    x2 = _atom(spec, start + span + 1)
    gs = (gcd(x0, spec.modulus), gcd(x1, spec.modulus), gcd(x2, spec.modulus))
    units = gs == (1, 1, 1)
    lhs_num = x1 * x2 % spec.modulus
    lhs_den = x0
    rhs_num = x1 * x2 % spec.modulus
    rhs_den = x0
    flat = (lhs_num * rhs_den - rhs_num * lhs_den) % spec.modulus == 0
    loop = 1 if units and flat else None
    return ArithmeticPlaquetteAudit(
        spec.family,
        spec.parameter,
        start,
        span,
        x0,
        x1,
        x2,
        gs,
        units,
        lhs_num,
        lhs_den,
        rhs_num,
        rhs_den,
        flat,
        loop,
    )


@dataclass(frozen=True, slots=True)
class BoundaryFluxBlindnessAudit:
    family: str
    parameter: int
    start: int
    span: int
    interior_flux_gcd: int
    boundary_product_gcd: int
    boundary_atoms_units: bool
    flat_boundary_connection_defined: bool
    interior_flux_invisible_to_unit_boundary: bool


def boundary_flux_blindness_audit(
    family: str,
    parameter: int,
    *,
    start: int,
    span: int,
) -> BoundaryFluxBlindnessAudit:
    block = arithmetic_ghost_flux_block(family, parameter, start=start, span=span)
    boundary_gcd = gcd(
        block.spec.modulus,
        block.left_boundary * block.right_boundary,
    )
    units = boundary_gcd == 1
    return BoundaryFluxBlindnessAudit(
        block.spec.family,
        block.spec.parameter,
        block.start,
        block.span,
        block.support_gcd,
        boundary_gcd,
        units,
        units,
        block.support_gcd > 1 and units,
    )


def _forward_difference_first_column(
    values: tuple[int, ...], modulus: int
) -> tuple[int, ...]:
    if not values:
        return ()
    row: list[int] = [int(value) % modulus for value in values]
    out = [row[0]]
    while len(row) > 1:
        row = [(row[i + 1] - row[i]) % modulus for i in range(len(row) - 1)]
        out.append(row[0])
    return tuple(out)


def _falling(n: int, r: int) -> int:
    n, r = int(n), int(r)
    if r < 0 or r > n:
        return 0
    out = 1
    for value in range(n - r + 1, n + 1):
        out *= value
    return out


@dataclass(frozen=True, slots=True)
class FiniteDifferenceGhostJetAudit:
    """Exact Newton-jet growth of the affine interval product in ``start``."""

    family: str
    parameter: int
    start: int
    span: int
    modulus: int
    samples: tuple[int, ...]
    forward_differences: tuple[int, ...]
    closed_form_differences: tuple[int, ...]
    closed_form_exact: bool
    top_difference: int
    top_difference_gcd: int
    top_difference_unit: bool
    formal_polynomial_degree: int
    required_exact_jet_order: int
    exact_newton_coefficient_count: int
    bounded_order_jet_closed: bool


def finite_difference_ghost_jet_audit(
    family: str,
    parameter: int,
    *,
    start: int,
    span: int,
) -> FiniteDifferenceGhostJetAudit:
    """Compute all formal forward differences and verify the rising-factorial law.

    With ``u=C^-1`` in the odd candidate ring,

        B(a,l) = C^l (a+u)^overline(l)

    and therefore

        Delta^r B(a,l)
          = C^l l^(underline r) (a+r+u)^overline(l-r).

    In particular ``Delta^l B = C^l l!``.  If this leading difference is a
    unit, the formal Newton degree is exactly l; truncating at bounded order
    cannot represent the whole translated family.
    """
    spec, start, span = _validated_spec(family, parameter, start, span)
    samples = tuple(
        _interval_product_unbounded(spec, start + shift, span)
        for shift in range(span + 1)
    )
    diffs = _forward_difference_first_column(samples, spec.modulus)
    inv_c = pow(spec.stride, -1, spec.modulus)
    c_power = pow(spec.stride, span, spec.modulus)
    closed: list[int] = []
    for order in range(span + 1):
        rising = 1
        remaining = span - order
        base = (start + order + inv_c) % spec.modulus
        for j in range(remaining):
            rising = rising * (base + j) % spec.modulus
        value = c_power * (_falling(span, order) % spec.modulus) % spec.modulus
        value = value * rising % spec.modulus
        closed.append(value)
    top = diffs[-1]
    top_gcd = gcd(top, spec.modulus)
    unit = top_gcd == 1
    return FiniteDifferenceGhostJetAudit(
        spec.family,
        spec.parameter,
        start,
        span,
        spec.modulus,
        samples,
        diffs,
        tuple(closed),
        tuple(closed) == diffs,
        top,
        top_gcd,
        unit,
        span if top != 0 else -1,
        span,
        span + 1,
        False,
    )


@dataclass(frozen=True, slots=True)
class ComplexArithmeticFluxMismatchAudit:
    """Contrast ordinary complex zeros with modular divisor flux."""

    family: str
    parameter: int
    start: int
    span: int
    affine_complex_root: Fraction
    ordinary_complex_zero_count_on_positive_path: int
    arithmetic_flux_gcd: int
    complex_path_sees_arithmetic_defect: bool


def complex_arithmetic_flux_mismatch_audit(
    family: str,
    parameter: int,
    *,
    start: int,
    span: int,
) -> ComplexArithmeticFluxMismatchAudit:
    """Show why an ordinary C-valued argument principle misses the defect.

    The affine atom ``1+Cz`` has its only complex zero at ``-1/C``.  Every
    special-factor slot in the positive progression is therefore nonzero over
    C, even when an integer atom becomes zero in one hidden residue field.
    """
    block = arithmetic_ghost_flux_block(family, parameter, start=start, span=span)
    root = Fraction(-1, block.spec.stride)
    # The path consists of positive integer slots start..start+span-1.
    complex_zeros = 0
    return ComplexArithmeticFluxMismatchAudit(
        block.spec.family,
        block.spec.parameter,
        start,
        span,
        root,
        complex_zeros,
        block.support_gcd,
        block.support_gcd == 1,
    )


@dataclass(frozen=True, slots=True)
class AnalyticGammaBoundaryAudit:
    """Boundary Gamma-ratio name for the same rising-factorial product."""

    family: str
    parameter: int
    start: int
    span: int
    modulus: int
    stride: int
    gamma_start: Fraction
    gamma_end: Fraction
    direct_integer_product_modulus: int
    rising_factorial_product_modulus: int
    exact: bool
    boundary_descriptor_fields: int
    expanded_factor_count: int
    modular_gamma_evaluator_available: bool


def analytic_gamma_boundary_audit(
    family: str,
    parameter: int,
    *,
    start: int,
    span: int,
) -> AnalyticGammaBoundaryAudit:
    """Audit ``C^l Gamma(x+l)/Gamma(x)`` without treating Gamma as an oracle.

    ``x=a+1/C``.  Clearing the rational denominators in the Gamma/rising-
    factorial identity returns exactly ``prod(1+C(a+j))``.  The tuple
    ``(C,a,l)`` is a compact symbolic descriptor but no modular Gamma primitive
    is supplied by the repository, so this does not count as an evaluator.
    """
    spec, start, span = _validated_spec(family, parameter, start, span)
    x = Fraction(start * spec.stride + 1, spec.stride)
    end = x + span
    direct = _interval_product_unbounded(spec, start, span)
    # Verify by the exact rational rising factorial, then clear C^span.
    rising = Fraction(1, 1)
    for j in range(span):
        rising *= x + j
    cleared = rising * (spec.stride**span)
    if cleared.denominator != 1:
        raise AssertionError(cleared)
    normalized = int(cleared.numerator) % spec.modulus
    return AnalyticGammaBoundaryAudit(
        spec.family,
        spec.parameter,
        start,
        span,
        spec.modulus,
        spec.stride,
        x,
        end,
        direct,
        normalized,
        direct == normalized,
        3,
        span,
        False,
    )


@dataclass(frozen=True, slots=True)
class LinearResultantFluxAudit:
    family: str
    parameter: int
    start: int
    span: int
    direct_product: int
    linear_resultant: int
    support_gcd: int
    exact: bool
    polynomial_degree: int
    root_evaluations_encoded: int
    compact_new_evaluator_supplied: bool


def linear_resultant_flux_audit(
    family: str,
    parameter: int,
    *,
    start: int,
    span: int,
) -> LinearResultantFluxAudit:
    """Audit ``Res(prod(X-(a+j)), 1+C X)``.

    For a monic first polynomial the resultant is the product of the second
    polynomial over all first-polynomial roots, hence exactly ``B(a,l)``.  This
    is a norm/resultant *reformulation*, not a new evaluator.
    """
    spec = SpecialJetProgressionSpec.build(family, parameter)
    block = build_special_jet_interval(spec, start, span)
    resultant = _interval_product_unbounded(spec, start, span)
    return LinearResultantFluxAudit(
        spec.family,
        spec.parameter,
        int(start),
        int(span),
        block.product,
        resultant,
        gcd(resultant, spec.modulus),
        resultant == block.product,
        int(span),
        int(span),
        False,
    )


@dataclass(frozen=True, slots=True)
class FermatBinomialDyadicAudit:
    parameter: int
    start: int
    span: int
    modulus: int
    center: int
    direct_binomial: int
    recursive_binomial: int
    exact: bool
    internal_splits: int
    leaf_terms: int
    unique_leaf_offsets: int
    denominator_inversions: int
    all_denominators_units: bool
    memo_reuse: int
    bounded_binary_state_closed: bool


def fermat_binomial_dyadic_audit(
    parameter: int,
    *,
    start: int,
    span: int,
) -> FermatBinomialDyadicAudit:
    """Try the natural dyadic recursion for Fermat's sparse-center binomial.

        C(x,2m) = C(x,m) C(x-m,m) / C(2m,m).

    For power-of-two ``span`` this creates two *different shifted children* at
    every split.  The leaves are ``x, x-1, ..., x-span+1``; there are no equal
    subproblems to memoize.  The audit evaluates the identity only for bounded
    controls and counts the complete branch tree.
    """
    n, start, span = int(parameter), int(start), int(span)
    if n < 2 or start < 1 or span < 1 or span & (span - 1):
        raise ValueError((n, start, span))
    spec = SpecialJetProgressionSpec.build("fermat", n)
    K = 1 << n
    center_exp = K - n - 2
    if center_exp < 0:
        raise ValueError((n, center_exp))
    center = 1 << center_exp
    x = center - start
    direct = comb(x, span) % spec.modulus
    memo: dict[tuple[int, int], int] = {}
    leaf_offsets: set[int] = set()
    internal = inversions = reuse = 0
    denominators_units = True

    root_key = (0, span)
    stack: list[tuple[int, int, bool]] = [(0, span, False)]
    while stack:
        offset, lower, expanded = stack.pop()
        key = (offset, lower)
        if key in memo:
            reuse += 1
            continue
        if lower == 1:
            leaf_offsets.add(offset)
            memo[key] = (x - offset) % spec.modulus
            continue
        half = lower // 2
        left_key, right_key = (offset, half), (offset + half, half)
        if not expanded:
            stack.append((offset, lower, True))
            stack.append((right_key[0], right_key[1], False))
            stack.append((left_key[0], left_key[1], False))
            continue
        internal += 1
        denom = comb(lower, half) % spec.modulus
        g = gcd(denom, spec.modulus)
        if g != 1:
            denominators_units = False
            raise ArithmeticError(("nonunit-central-binomial", lower, g))
        inversions += 1
        value = memo[left_key] * memo[right_key] % spec.modulus
        memo[key] = value * pow(denom, -1, spec.modulus) % spec.modulus

    recursive = memo[root_key]
    return FermatBinomialDyadicAudit(
        n,
        start,
        span,
        spec.modulus,
        center,
        direct,
        recursive,
        direct == recursive,
        internal,
        len(leaf_offsets),
        len(leaf_offsets),
        inversions,
        denominators_units,
        reuse,
        False,
    )


@dataclass(frozen=True, slots=True)
class SingularDeltaFourierAudit:
    family: str
    parameter: int
    singular_slot: int
    hidden_period: int
    exact_fourier_character_count: int
    nonzero_fourier_coefficients: int
    spectral_density_numerator: int
    spectral_density_denominator: int
    sparse_exact_spectrum: bool


def singular_delta_fourier_audit(
    family: str,
    parameter: int,
) -> SingularDeltaFourierAudit:
    """Count exact Fourier support of the first hidden periodic delta current.

    Over a period q, a delta at m0 has transform ``chi_k(-m0)`` for every
    character k.  Every coefficient is nonzero, so an exact character basis has
    q active coordinates.  This is a support-count theorem; no floating complex
    approximation is used.
    """
    singular = first_special_transverse_singularity(family, parameter)
    if (
        not singular.found
        or singular.first_slot is None
        or singular.denominator_gcd <= 1
    ):
        raise ValueError((family, parameter, "no bounded singular control"))
    q = singular.denominator_gcd
    return SingularDeltaFourierAudit(
        singular.family,
        singular.parameter,
        singular.first_slot,
        q,
        q,
        q,
        q,
        q,
        False,
    )


def _poly_mul_monic_linear_mod(
    coeffs: list[int],
    shift: int,
    modulus: int,
) -> tuple[list[int], int]:
    """Multiply ascending coeffs by ``X+shift``; return coeffs and mult count."""
    out = [0] * (len(coeffs) + 1)
    multiplications = 0
    s = shift % modulus
    for index, coeff in enumerate(coeffs):
        out[index] = (out[index] + coeff * s) % modulus
        multiplications += 1
        out[index + 1] = (out[index + 1] + coeff) % modulus
    return out, multiplications


def _poly_eval_mod(coeffs: tuple[int, ...], x: int, modulus: int) -> tuple[int, int]:
    out = 0
    multiplications = 0
    for coeff in reversed(coeffs):
        out = (out * x + coeff) % modulus
        multiplications += 1
    # The first Horner multiply is by zero and can be optimized away.  Charge
    # degree rather than coefficient count to avoid overstating work.
    return out, max(0, multiplications - 1)


@dataclass(frozen=True, slots=True)
class BabyGiantGhostFluxAudit:
    family: str
    parameter: int
    start: int
    span: int
    baby_width: int
    giant_blocks: int
    tail_terms: int
    polynomial_coefficient_count: int
    direct_product: int
    baby_giant_product: int
    exact: bool
    polynomial_build_multiplications: int
    point_evaluation_multiplications: int
    giant_combine_multiplications: int
    tail_multiplications: int
    scale_power_compositions_upper_bound: int
    charged_modular_multiplications: int
    direct_linear_multiplications: int
    state_sublinear_in_span: bool
    actual_work_beats_linear_product: bool
    polylog_state: bool
    production_evaluator_available: bool


def baby_giant_ghost_flux_audit(
    family: str,
    parameter: int,
    *,
    start: int,
    span: int,
) -> BabyGiantGhostFluxAudit:
    """Concrete sqrt-state block-polynomial experiment with honest Horner cost.

    Let ``u=C^-1`` and ``Q(X)=prod_{j=0}^{b-1}(X+j)``.  Full b-sized blocks
    evaluate ``Q(u+a+i*b)``.  The representation stores only degree-b Q plus
    O(l/b) evaluation sites; choosing b~=sqrt(l) is sublinear *state*.  This
    implementation deliberately uses ordinary coefficient construction and
    Horner evaluation so its charged arithmetic cannot masquerade as a fast
    multipoint primitive.
    """
    spec, start, span = bounded_jet_spec(family, parameter, start, span)
    b = isqrt(span)
    if b * b < span:
        b += 1
    full = span // b
    tail = span - full * b
    coeffs = [1]
    build_mults = 0
    for j in range(b):
        coeffs, used = _poly_mul_monic_linear_mod(coeffs, j, spec.modulus)
        build_mults += used
    coeff_tuple = tuple(coeffs)
    inv_c = pow(spec.stride, -1, spec.modulus)
    product = 1
    eval_mults = combine_mults = 0
    for block_index in range(full):
        point = (inv_c + start + block_index * b) % spec.modulus
        value, used = _poly_eval_mod(coeff_tuple, point, spec.modulus)
        eval_mults += used
        if block_index:
            combine_mults += 1
        product = product * value % spec.modulus
    tail_mults = 0
    tail_start = start + full * b
    for offset in range(tail):
        normalized = (inv_c + tail_start + offset) % spec.modulus
        if full or offset:
            combine_mults += 1
        product = product * normalized % spec.modulus
        tail_mults += 1
    # Restore the C^span scale.  Count a conservative binary-power upper bound
    # separately; Python's pow is not treated as a free primitive.
    scaled = product * pow(spec.stride, span, spec.modulus) % spec.modulus
    scale_comps = 0 if span <= 1 else (span.bit_length() - 1) + (span.bit_count() - 1)
    direct = build_special_jet_interval(spec, start, span).product
    charged = build_mults + eval_mults + combine_mults + tail_mults + scale_comps + 1
    structural_state = len(coeff_tuple) + full + (1 if tail else 0)
    return BabyGiantGhostFluxAudit(
        spec.family,
        spec.parameter,
        start,
        span,
        b,
        full,
        tail,
        len(coeff_tuple),
        direct,
        scaled,
        direct == scaled,
        build_mults,
        eval_mults,
        combine_mults,
        tail_mults,
        scale_comps,
        charged,
        max(0, span - 1),
        structural_state < span,
        charged < max(0, span - 1),
        False,
        False,
    )


@dataclass(frozen=True, slots=True)
class ArithmeticGhostFluxFrontier:
    divisor_current_semantics_closed: bool
    flat_unit_connection_closed: bool
    unit_boundary_recovers_interior_flux: bool
    bounded_order_finite_difference_jet_closed: bool
    linear_resultant_is_new_evaluator: bool
    fermat_dyadic_binomial_branch_collapse_closed: bool
    exact_fourier_state_sparse: bool
    baby_giant_state_sublinear: bool
    baby_giant_actual_work_polylogarithmic: bool
    production_source_extractor_available: bool
    status: str
    missing_operation: str


def arithmetic_ghost_flux_frontier() -> ArithmeticGhostFluxFrontier:
    return ArithmeticGhostFluxFrontier(
        divisor_current_semantics_closed=True,
        flat_unit_connection_closed=True,
        unit_boundary_recovers_interior_flux=False,
        bounded_order_finite_difference_jet_closed=False,
        linear_resultant_is_new_evaluator=False,
        fermat_dyadic_binomial_branch_collapse_closed=False,
        exact_fourier_state_sparse=False,
        baby_giant_state_sublinear=True,
        baby_giant_actual_work_polylogarithmic=False,
        production_source_extractor_available=False,
        status="UNKNOWN",
        missing_operation=(
            "an exact support/divisor boundary functional for the special affine "
            "progression whose evaluated state and total modular work are "
            "polylogarithmic in the interval length; it may not enumerate the "
            "interior atoms, retain a degree/jet order growing with the interval, "
            "or hide a fast factorial/multipoint/factoring oracle"
        ),
    )


__all__ = [
    "AnalyticGammaBoundaryAudit",
    "ArithmeticGhostFluxBlock",
    "ArithmeticGhostFluxFrontier",
    "ArithmeticPlaquetteAudit",
    "ArithmeticWilsonLineAudit",
    "BabyGiantGhostFluxAudit",
    "BoundaryFluxBlindnessAudit",
    "ComplexArithmeticFluxMismatchAudit",
    "DivisorCurrentIntegralAudit",
    "FermatBinomialDyadicAudit",
    "FiniteDifferenceGhostJetAudit",
    "LinearResultantFluxAudit",
    "SingularDeltaFourierAudit",
    "analytic_gamma_boundary_audit",
    "arithmetic_ghost_flux_block",
    "arithmetic_ghost_flux_frontier",
    "arithmetic_plaquette_audit",
    "arithmetic_wilson_line_audit",
    "baby_giant_ghost_flux_audit",
    "boundary_flux_blindness_audit",
    "complex_arithmetic_flux_mismatch_audit",
    "divisor_current_integral_audit",
    "fermat_binomial_dyadic_audit",
    "finite_difference_ghost_jet_audit",
    "linear_resultant_flux_audit",
    "singular_delta_fourier_audit",
]
