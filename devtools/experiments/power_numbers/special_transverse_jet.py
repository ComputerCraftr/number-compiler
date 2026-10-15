"""Arithmetic transverse-jet/holonomy audit for Fermat and Mersenne candidates.

The terminal germ can be visualized as a circle with a transverse coordinate,
but the useful lift is arithmetic rather than analytic.  For an odd candidate
``N`` the transverse defect of the Frobenius/Freshman's-dream map is

    Delta_N(z,t) = (z+t)^N - z^N - t^N
                 = sum_{k=1}^{N-1} C(N,k) z^(N-k) t^k.

The coefficients obey the exact discrete connection

    (k+1) C(N,k+1) = (N-k) C(N,k),

hence modulo ``N``

    (k+1) c_(k+1) = -k c_k.

Starting from ``c_1=0``, the zero transverse sheet therefore transports
perfectly while ``k+1`` is a unit modulo ``N``.  The first failure of
invertibility is a genuine arithmetic singularity.  For a composite candidate
its first such index is the smallest prime factor.

For the special families those possible singular indices lie in a known
arithmetic progression:

    Fermat F_n (n>=2): q = 1 + 2^(n+2) m
    Mersenne M_p       : q = 1 + 2 p m  (prime exponent p).

This module projects the transverse connection onto those admissible indices.
A block denominator/holonomy is the progression product

    B(a,l) = prod_{j=0}^{l-1} (1 + C (a+j)).

``gcd(B,N)`` is a cancellation-free range observer: it is one iff the whole
block contains no nonunit denominator and is nontrivial when a hidden factor is
present.  The one-step shift has the exact left/right forcing law

    B(a+1,l) * (1+C a) = B(a,l) * (1+C(a+l)).

Thus rolling by one slot is constant-state while the outgoing term is a unit;
a nonunit denominator itself emits a natural gcd packet.

The critical complexity audit is the powered shift.  Translating a length-l
block by ``s`` slots cancels only the overlap and leaves ``min(l,|s|)`` entering
and leaving boundary factors.  In particular the equal-span shift needed to
construct the right sibling of a dyadic block has *zero overlap* and reopens
all l factors.  A balanced product tree has logarithmic parallel depth but
l-1 semantic multiplications / l atom evaluations.  The geometry therefore
provides an exact defect observer and a local forcing law, but not a bounded-
state binary evaluator for a previously unseen interval.

Everything here is research-only.  Production must not import this module or
promote the enumerative window product as the missing terminal theorem.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import comb, factorial, gcd, isqrt

from devtools.verification.special_factor_reference import (
    batched_special_factor_witness,
)
from number_compiler.arithmetic.fields.radix import bit_width
from number_compiler.sequences.power_numbers.numbers import (
    fermat_number,
    mersenne_number,
)
from number_compiler.sequences.prime.set import is_prime_u64


@dataclass(frozen=True, slots=True)
class SpecialJetProgressionSpec:
    """Admissible special-factor progression through the square-root bound."""

    family: str
    parameter: int
    modulus: int
    stride: int
    max_slot: int

    def __post_init__(self) -> None:
        if self.family not in ("fermat", "mersenne"):
            raise ValueError(self.family)
        if (
            min(
                int(self.parameter),
                int(self.modulus),
                int(self.stride),
                int(self.max_slot),
            )
            < 0
        ):
            raise ValueError(self)
        if self.modulus < 3 or not self.modulus & 1 or self.stride <= 0:
            raise ValueError(self)

    @classmethod
    def build(cls, family: str, parameter: int) -> SpecialJetProgressionSpec:
        family = str(family)
        parameter = int(parameter)
        if family == "fermat":
            if parameter < 2:
                raise ValueError("Fermat factor progression q=1 mod 2^(n+2) needs n>=2")
            modulus = fermat_number(parameter)
            stride = 1 << (parameter + 2)
        elif family == "mersenne":
            if parameter < 3 or not (parameter & 1) or not is_prime_u64(parameter):
                raise ValueError(
                    "Mersenne factor progression q=1 mod 2p needs prime odd p"
                )
            modulus = mersenne_number(parameter)
            stride = 2 * parameter
        else:
            raise ValueError(family)
        max_slot = max(0, (isqrt(modulus) - 1) // stride)
        return cls(family, parameter, modulus, stride, max_slot)

    def slot_value(self, slot: int) -> int:
        slot = int(slot)
        if slot < 1:
            raise ValueError(slot)
        return 1 + self.stride * slot

    @property
    def candidate_count(self) -> int:
        return self.max_slot

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "special-transverse-jet-progression",
            self.family,
            self.parameter,
            self.stride,
            self.max_slot,
        )


@dataclass(frozen=True, slots=True)
class TransverseJetSingularityAudit:
    family: str
    parameter: int
    modulus: int
    stride: int
    max_slot: int
    slots_tested: int
    first_slot: int | None
    singular_index: int | None
    denominator_gcd: int
    coefficient_modulus: int | None
    coefficient_gcd: int | None
    prior_admissible_denominators_units: bool
    candidate_derived: bool = True

    @property
    def found(self) -> bool:
        return self.first_slot is not None

    @property
    def emits_proper_factor(self) -> bool:
        return 1 < self.denominator_gcd < self.modulus


def transverse_jet_coefficient_mod(modulus: int, order: int) -> int:
    """Return ``C(N,k) mod N`` for a bounded research order ``k``."""
    modulus, order = int(modulus), int(order)
    if modulus < 2 or not 0 <= order <= modulus:
        raise ValueError((modulus, order))
    return comb(modulus, order) % modulus


def first_special_transverse_singularity(
    family: str,
    parameter: int,
) -> TransverseJetSingularityAudit:
    """Scan only admissible factor slots and expose the first connection pole.

    This is intentionally an enumerative research differential.  It performs
    one gcd per slot and is *not* a production source projector.
    """
    spec = SpecialJetProgressionSpec.build(family, parameter)
    tested = 0
    first_slot = singular = None
    singular_gcd = 1
    for slot in range(1, spec.max_slot + 1):
        k = spec.slot_value(slot)
        g = gcd(k, spec.modulus)
        tested += 1
        if g > 1:
            first_slot, singular, singular_gcd = slot, k, g
            break
    coefficient = coefficient_gcd = None
    if singular is not None:
        coefficient = transverse_jet_coefficient_mod(spec.modulus, singular)
        coefficient_gcd = gcd(coefficient, spec.modulus)
    return TransverseJetSingularityAudit(
        spec.family,
        spec.parameter,
        spec.modulus,
        spec.stride,
        spec.max_slot,
        tested,
        first_slot,
        singular,
        singular_gcd,
        coefficient,
        coefficient_gcd,
        True,
    )


@dataclass(frozen=True, slots=True)
class SpecialJetIntervalBlock:
    """One evaluated progression-product interval modulo the candidate."""

    spec: SpecialJetProgressionSpec
    start: int
    span: int
    product: int
    atom_evaluations: int
    multiplications: int
    parallel_depth: int

    def __post_init__(self) -> None:
        start, span = int(self.start), int(self.span)
        if start < 1 or span < 1 or start + span - 1 > self.spec.max_slot:
            raise ValueError((start, span, self.spec.max_slot))
        if int(self.product) != self.product % self.spec.modulus:
            raise ValueError((self.product, self.spec.modulus))
        if self.atom_evaluations != span or self.multiplications != span - 1:
            raise ValueError((self.atom_evaluations, self.multiplications, span))
        if self.parallel_depth < 0:
            raise ValueError(self.parallel_depth)

    @classmethod
    def atom(
        cls, spec: SpecialJetProgressionSpec, slot: int
    ) -> SpecialJetIntervalBlock:
        slot = int(slot)
        if not 1 <= slot <= spec.max_slot:
            raise ValueError((slot, spec.max_slot))
        return cls(spec, slot, 1, spec.slot_value(slot) % spec.modulus, 1, 0, 0)

    def then(self, other: SpecialJetIntervalBlock) -> SpecialJetIntervalBlock:
        if not isinstance(other, SpecialJetIntervalBlock):
            raise TypeError(type(other))
        if self.spec != other.spec or other.start != self.start + self.span:
            raise ValueError((self, other))
        return SpecialJetIntervalBlock(
            self.spec,
            self.start,
            self.span + other.span,
            self.product * other.product % self.spec.modulus,
            self.atom_evaluations + other.atom_evaluations,
            self.multiplications + other.multiplications + 1,
            max(self.parallel_depth, other.parallel_depth) + 1,
        )

    @property
    def support_gcd(self) -> int:
        return gcd(self.product, self.spec.modulus)

    @property
    def status(self) -> str:
        g = self.support_gcd
        if g == 1:
            return "CLEAR"
        if g == self.spec.modulus:
            return "FULL"
        return "SPLIT"

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "special-jet-interval",
            self.spec.canonical_key,
            self.start,
            self.span,
            self.product,
        )


def build_special_jet_interval(
    spec: SpecialJetProgressionSpec,
    start: int,
    span: int,
) -> SpecialJetIntervalBlock:
    """Build an exact balanced interval product; charge every leaf/multiply."""
    start, span = int(start), int(span)
    if start < 1 or span < 1 or start + span - 1 > spec.max_slot:
        raise ValueError((start, span, spec.max_slot))
    level = [
        SpecialJetIntervalBlock.atom(spec, slot) for slot in range(start, start + span)
    ]
    while len(level) > 1:
        nxt: list[SpecialJetIntervalBlock] = []
        for index in range(0, len(level), 2):
            if index + 1 == len(level):
                nxt.append(level[index])
            else:
                nxt.append(level[index].then(level[index + 1]))
        level = nxt
    return level[0]


@dataclass(frozen=True, slots=True)
class JetHolonomyShiftAudit:
    family: str
    parameter: int
    start: int
    span: int
    shift: int
    overlap: int
    boundary_width: int
    old_product: int
    shifted_product: int
    leaving_product: int
    entering_product: int
    leaving_gcd: int
    entering_gcd: int
    cross_identity_exact: bool
    inverse_update_available: bool
    inverse_update_exact: bool

    @property
    def local_forcing_is_singular(self) -> bool:
        return self.leaving_gcd > 1


def _product_slots_mod(
    spec: SpecialJetProgressionSpec,
    slots: tuple[int, ...],
) -> int:
    out = 1
    for slot in slots:
        out = out * spec.slot_value(slot) % spec.modulus
    return out


def jet_holonomy_shift_audit(
    family: str,
    parameter: int,
    *,
    start: int,
    span: int,
    shift: int = 1,
) -> JetHolonomyShiftAudit:
    """Audit the exact overlap/boundary law for a translated interval.

    The returned cross identity does not require division.  ``inverse_update``
    is available only if the whole leaving boundary is a unit modulo ``N``.
    """
    spec = SpecialJetProgressionSpec.build(family, parameter)
    start, span, shift = int(start), int(span), int(shift)
    if span < 1 or shift == 0:
        raise ValueError((span, shift))
    new_start = start + shift
    if start < 1 or new_start < 1:
        raise ValueError((start, shift))
    if start + span - 1 > spec.max_slot or new_start + span - 1 > spec.max_slot:
        raise ValueError((start, span, shift, spec.max_slot))

    old_slots = tuple(range(start, start + span))
    new_slots = tuple(range(new_start, new_start + span))
    old_set, new_set = set(old_slots), set(new_slots)
    leaving = tuple(slot for slot in old_slots if slot not in new_set)
    entering = tuple(slot for slot in new_slots if slot not in old_set)
    if len(leaving) != len(entering):
        raise AssertionError((leaving, entering))
    overlap = span - len(leaving)
    width = len(leaving)

    old_product = _product_slots_mod(spec, old_slots)
    shifted_product = _product_slots_mod(spec, new_slots)
    leaving_product = _product_slots_mod(spec, leaving)
    entering_product = _product_slots_mod(spec, entering)
    cross = (
        shifted_product * leaving_product - old_product * entering_product
    ) % spec.modulus == 0
    leaving_gcd = gcd(leaving_product, spec.modulus)
    entering_gcd = gcd(entering_product, spec.modulus)
    available = leaving_gcd == 1
    if available:
        predicted = (
            old_product * entering_product * pow(leaving_product, -1, spec.modulus)
        ) % spec.modulus
        exact = predicted == shifted_product
    else:
        exact = False
    return JetHolonomyShiftAudit(
        spec.family,
        spec.parameter,
        start,
        span,
        shift,
        overlap,
        width,
        old_product,
        shifted_product,
        leaving_product,
        entering_product,
        leaving_gcd,
        entering_gcd,
        cross,
        available,
        exact,
    )


@dataclass(frozen=True, slots=True)
class DyadicJetTranslationAudit:
    span: int
    one_step_boundary_width: int
    sibling_shift: int
    sibling_overlap: int
    sibling_boundary_width: int
    reduced_ratio_numerator_degree: int
    reduced_ratio_denominator_degree: int
    exact_new_boundary_terms: int
    bounded_state_sibling_translation_closed: bool


def dyadic_jet_translation_audit(span: int) -> DyadicJetTranslationAudit:
    """Symbolic state-growth audit for shifting to an adjacent equal block."""
    span = int(span)
    if span < 1:
        raise ValueError(span)
    # For two length-span intervals separated by shift s, overlap cancellation
    # leaves min(span, |s|) factors on each boundary.  The dyadic sibling has
    # s=span, so there is no overlap and every factor is new.
    width = span
    return DyadicJetTranslationAudit(
        span=span,
        one_step_boundary_width=1,
        sibling_shift=span,
        sibling_overlap=0,
        sibling_boundary_width=width,
        reduced_ratio_numerator_degree=width,
        reduced_ratio_denominator_degree=width,
        exact_new_boundary_terms=width,
        bounded_state_sibling_translation_closed=False,
    )


@dataclass(frozen=True, slots=True)
class JetWindowSearchAudit:
    family: str
    parameter: int
    modulus: int
    stride: int
    candidate_count: int
    root_gcd: int
    status: str
    product_atom_evaluations: int
    product_multiplications: int
    product_parallel_depth: int
    descent_gcd_calls: int
    located_slot: int | None
    located_value: int | None
    proper_factor: int | None
    existing_factor_window_candidate_count: int
    existing_factor_window_product_multiplications: int
    existing_factor_window_product_depth: int
    existing_factor_window_proper_factor: int | None
    same_product_tree_work: bool
    same_witness_when_composite: bool
    candidate_derived: bool = True
    factor_enumeration: int = 0


def _balanced_slot_levels(
    spec: SpecialJetProgressionSpec,
) -> tuple[tuple[tuple[int, int], ...], ...]:
    """Return ``(first_slot, product_mod_N)`` levels for left-first descent."""
    if spec.max_slot < 1:
        return ()
    levels: list[tuple[tuple[int, int], ...]] = [
        tuple(
            (slot, spec.slot_value(slot) % spec.modulus)
            for slot in range(1, spec.max_slot + 1)
        )
    ]
    # We only need products and the first leaf index at each node.  Pairing is
    # the same balanced schedule used by the existing special-factor window.
    while len(levels[-1]) > 1:
        current = levels[-1]
        nxt: list[tuple[int, int]] = []
        for index in range(0, len(current), 2):
            if index + 1 == len(current):
                nxt.append(current[index])
            else:
                first = current[index][0]
                product = current[index][1] * current[index + 1][1] % spec.modulus
                nxt.append((first, product))
        levels.append(tuple(nxt))
    return tuple(levels)


def special_jet_window_search_audit(
    family: str,
    parameter: int,
) -> JetWindowSearchAudit:
    """Evaluate the complete admissible sqrt-window and descend one gcd hit.

    The root product is an exact candidate-derived composite observer but its
    construction enumerates every admissible slot.  This routine exists to
    measure that cost and compare it with ``batched_special_factor_witness``.
    """
    spec = SpecialJetProgressionSpec.build(family, parameter)
    if spec.max_slot < 1:
        raise ValueError((family, parameter, "empty special factor window"))
    levels = _balanced_slot_levels(spec)
    root_product = levels[-1][0][1]
    root_gcd = gcd(root_product, spec.modulus)
    if root_gcd == 1:
        status = "CLEAR"
    elif root_gcd == spec.modulus:
        status = "FULL"
    else:
        status = "SPLIT"

    gcd_calls = 1
    located_slot = located_value = proper = None
    if root_gcd > 1:
        node_index = 0
        for level_index in range(len(levels) - 2, -1, -1):
            current = levels[level_index]
            left_index = node_index * 2
            left_gcd = gcd(current[left_index][1], spec.modulus)
            gcd_calls += 1
            if left_gcd > 1:
                node_index = left_index
                continue
            right_index = left_index + 1
            if right_index >= len(current):
                raise AssertionError((level_index, node_index, current))
            right_gcd = gcd(current[right_index][1], spec.modulus)
            gcd_calls += 1
            if right_gcd <= 1:
                raise AssertionError((level_index, left_gcd, right_gcd))
            node_index = right_index
        located_slot = levels[0][node_index][0]
        located_value = spec.slot_value(located_slot)
        proper = gcd(located_value, spec.modulus)
        gcd_calls += 1
        if not 1 < proper < spec.modulus:
            raise AssertionError((located_slot, located_value, proper))

    existing = batched_special_factor_witness(family, parameter, spec.max_slot)
    same_work = (
        existing.candidate_count == spec.max_slot
        and existing.product_multiplications == spec.max_slot - 1
        and existing.product_depth == len(levels) - 1
    )
    same_witness = (proper is None and existing.proper_factor is None) or (
        proper is not None and existing.proper_factor == proper
    )
    return JetWindowSearchAudit(
        spec.family,
        spec.parameter,
        spec.modulus,
        spec.stride,
        spec.max_slot,
        root_gcd,
        status,
        spec.max_slot,
        spec.max_slot - 1,
        len(levels) - 1,
        gcd_calls,
        located_slot,
        located_value,
        proper,
        existing.candidate_count,
        existing.product_multiplications,
        existing.product_depth,
        existing.proper_factor,
        same_work,
        same_witness,
    )


@dataclass(frozen=True, slots=True)
class JetWindowComplexityAudit:
    family: str
    parameter: int
    modulus_bits: int
    stride: int
    candidate_count: int
    candidate_count_bits: int
    balanced_product_work: int
    balanced_parallel_depth: int
    residue_state_bits: int
    descriptor_bits: int
    work_linear_in_window: bool
    depth_logarithmic_in_window: bool


def special_jet_window_complexity(
    family: str,
    parameter: int,
) -> JetWindowComplexityAudit:
    spec = SpecialJetProgressionSpec.build(family, parameter)
    count = spec.max_slot
    depth = 0 if count <= 1 else (count - 1).bit_length()
    descriptor_bits = bit_width(parameter) + bit_width(spec.stride) + bit_width(count)
    return JetWindowComplexityAudit(
        spec.family,
        spec.parameter,
        spec.modulus.bit_length(),
        spec.stride,
        count,
        bit_width(count),
        max(0, count - 1),
        depth,
        spec.modulus.bit_length(),
        descriptor_bits,
        True,
        True,
    )


@dataclass(frozen=True, slots=True)
class FermatJetBinomialNormalFormAudit:
    parameter: int
    start: int
    span: int
    modulus: int
    stride: int
    center_power_exponent: int
    center: int
    direct_product: int
    binomial_normal_form: int
    exact: bool
    binomial_lower_index: int
    expanded_factor_count: int
    compact_modular_binomial_evaluator_available: bool = False


def fermat_jet_binomial_normal_form_audit(
    parameter: int,
    *,
    start: int,
    span: int,
) -> FermatJetBinomialNormalFormAudit:
    """Rewrite the Fermat holonomy as a falling binomial around a power of two.

    For ``F_n=2^K+1`` and ``C=2^(n+2)``, put

        A = 2^(K-n-2).

    Then ``C*A=2^K=-1 (mod F_n)`` and therefore

        prod_{j=0}^{l-1}(1+C(a+j))
          = (-C)^l l! binom(A-a,l)  (mod F_n).

    This is an exact sparse-center normal form, but the lower binomial index is
    still the interval length ``l``.  Naming the expression does not provide a
    compact modular evaluator for it.
    """
    n, start, span = int(parameter), int(start), int(span)
    spec = SpecialJetProgressionSpec.build("fermat", n)
    if start < 1 or span < 1 or start + span - 1 > spec.max_slot:
        raise ValueError((start, span, spec.max_slot))
    K = 1 << n
    exponent = K - n - 2
    if exponent < 0:
        raise ValueError((n, exponent))
    center = 1 << exponent
    if spec.stride * center != spec.modulus - 1:
        raise AssertionError((spec.stride, center, spec.modulus))
    direct = build_special_jet_interval(spec, start, span).product
    normal = (
        pow(-spec.stride, span, spec.modulus)
        * (factorial(span) % spec.modulus)
        * (comb(center - start, span) % spec.modulus)
    ) % spec.modulus
    return FermatJetBinomialNormalFormAudit(
        n,
        start,
        span,
        spec.modulus,
        spec.stride,
        exponent,
        center,
        direct,
        normal,
        direct == normal,
        span,
        span,
        False,
    )


@dataclass(frozen=True, slots=True)
class TransverseJetFrontier:
    transverse_defect_semantics_closed: bool
    special_progression_projection_closed: bool
    one_step_left_right_holonomy_closed: bool
    dyadic_sibling_translation_bounded_state_closed: bool
    full_window_evaluator_polylog_work: bool
    production_source_extractor_available: bool
    status: str
    missing_operation: str


def transverse_jet_frontier() -> TransverseJetFrontier:
    return TransverseJetFrontier(
        transverse_defect_semantics_closed=True,
        special_progression_projection_closed=True,
        one_step_left_right_holonomy_closed=True,
        dyadic_sibling_translation_bounded_state_closed=False,
        full_window_evaluator_polylog_work=False,
        production_source_extractor_available=False,
        status="UNKNOWN",
        missing_operation=(
            "sublinear/polylogarithmic evaluation of the admissible arithmetic-"
            "progression (rising-factorial) holonomy without enumerating its "
            "boundary factors or materializing an equivalent factor window"
        ),
    )


__all__ = [
    "DyadicJetTranslationAudit",
    "FermatJetBinomialNormalFormAudit",
    "JetHolonomyShiftAudit",
    "JetWindowComplexityAudit",
    "JetWindowSearchAudit",
    "SpecialJetIntervalBlock",
    "SpecialJetProgressionSpec",
    "TransverseJetFrontier",
    "TransverseJetSingularityAudit",
    "build_special_jet_interval",
    "dyadic_jet_translation_audit",
    "fermat_jet_binomial_normal_form_audit",
    "first_special_transverse_singularity",
    "jet_holonomy_shift_audit",
    "special_jet_window_complexity",
    "special_jet_window_search_audit",
    "transverse_jet_coefficient_mod",
    "transverse_jet_frontier",
]
