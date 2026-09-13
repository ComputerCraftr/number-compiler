"""Canonical immutable specifications and result records for the number compiler.

This module deliberately contains no compilation algorithms.  Keeping semantic
specifications/results separate prevents the registry and CLI from regrowing
into another multi-purpose sequence implementation.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING, Generic, Sequence, TypeVar

from number_compiler.arithmetic.fields.symbolic_extent import Extent
from number_compiler.arithmetic.polynomials.primary_jet import PrimaryJetBlock
from number_compiler.sequences.collatz.orbit import COLLATZ_PIECEWISE_MORPHISM
from number_compiler.sequences.power_numbers.numbers import MersenneNumberSpec
from number_compiler.sequences.prime.lane_quotient import PrimeLaneQuotientCompilation
from number_compiler.sequences.prime.wheel_cyclotomic import (
    PrimeWheelCyclotomicAutomaton,
)

if TYPE_CHECKING:
    from number_compiler.arithmetic.fields.adic_morphism import (
        PadicRadialQuotient,
        ValuationSensitivityMorphism,
    )
    from number_compiler.arithmetic.formula.symmetry_frame import (
        ReverseAddSymmetryLinearAction,
    )
    from number_compiler.arithmetic.polynomials.cyclotomic_transport import (
        PowerTwoCyclotomicRadialQuotient,
    )
    from number_compiler.projection.output_quotient import SpecialSourceGuard
    from number_compiler.sequences.collatz.frame import CollatzFutureValuationRoot
    from number_compiler.sequences.collatz.pair import CollatzValuationProjectionBlock


def _canonical_int_tuple(values: Sequence[int], *, minimum: int) -> tuple[int, ...]:
    out = tuple(values)
    if any(type(value) is not int for value in out):
        raise TypeError("indices/exponents must be exact integers")
    if any(v < minimum for v in out):
        raise ValueError(out)
    if out != tuple(sorted(set(out))):
        raise ValueError("indices/exponents must be sorted and unique")
    return out


@dataclass(frozen=True, slots=True)
class ReverseAddSequenceSpec:
    seed: int
    base: int = 10
    steps: int = 64

    def __post_init__(self) -> None:
        if any(type(value) is not int for value in (self.seed, self.base, self.steps)):
            raise TypeError("reverse/add parameters must be exact integers")
        if self.seed < 0 or self.base < 2 or self.steps < 0:
            raise ValueError(self)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("reverse_add", self.seed, self.base, self.steps)


@dataclass(frozen=True, slots=True)
class CollatzSequenceSpec:
    seed: int
    radix: int = 2
    max_steps: int = 256

    def __post_init__(self) -> None:
        if any(
            type(value) is not int for value in (self.seed, self.radix, self.max_steps)
        ):
            raise TypeError("Collatz parameters must be exact integers")
        if (
            self.seed <= 0
            or self.radix < 2
            or self.max_steps < 0
            or not (self.radix in (2, 3) or self.radix % 6 == 0)
        ):
            raise ValueError(self)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("collatz", self.seed, self.radix, self.max_steps)


@dataclass(frozen=True, slots=True)
class PrimeBlockSequenceSpec:
    start: int
    length: int
    word_bits: int = 62
    random_access: bool = False

    def __post_init__(self) -> None:
        if any(
            type(value) is not int
            for value in (self.start, self.length, self.word_bits)
        ):
            raise TypeError("prime-block parameters must be exact integers")
        if type(self.random_access) is not bool:
            raise TypeError("random_access must be a Boolean")
        if (
            self.start < 3
            or not (self.start & 1)
            or self.length < 0
            or self.word_bits < 2
        ):
            raise ValueError(self)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "prime_block",
            self.start,
            self.length,
            self.word_bits,
            self.random_access,
        )


@dataclass(frozen=True, slots=True)
class FermatSequenceSpec:
    indices: tuple[int, ...] = (0, 1, 2, 3, 4, 5, 6)
    test_through: int = 5
    reinterpret_radices: tuple[int, ...] = (2,)

    def __post_init__(self) -> None:
        if type(self.test_through) is not int:
            raise TypeError("test_through must be an exact integer")
        object.__setattr__(
            self, "indices", _canonical_int_tuple(self.indices, minimum=0)
        )
        object.__setattr__(
            self,
            "reinterpret_radices",
            _canonical_int_tuple(self.reinterpret_radices, minimum=2),
        )
        if self.test_through < 0:
            raise ValueError(self.test_through)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        # ``test_through`` is retained only as a compatibility policy knob for
        # explicit theorem queries; it does not change the numeric source.
        return ("fermat", self.indices, self.reinterpret_radices)

    @property
    def theorem_policy_key(self) -> tuple[object, ...]:
        return (*self.canonical_key, "test_through", self.test_through)


@dataclass(frozen=True, slots=True)
class MersenneSequenceSpec:
    exponents: tuple[int, ...] = (2, 3, 5, 7, 11, 13, 17, 19, 23, 31)
    test_through: int = 31
    reinterpret_radices: tuple[int, ...] = (2,)

    def __post_init__(self) -> None:
        if type(self.test_through) is not int:
            raise TypeError("test_through must be an exact integer")
        object.__setattr__(
            self, "exponents", _canonical_int_tuple(self.exponents, minimum=2)
        )
        object.__setattr__(
            self,
            "reinterpret_radices",
            _canonical_int_tuple(self.reinterpret_radices, minimum=2),
        )
        if self.test_through < 0:
            raise ValueError(self.test_through)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("mersenne", self.exponents, self.reinterpret_radices)

    @property
    def theorem_policy_key(self) -> tuple[object, ...]:
        return (*self.canonical_key, "test_through", self.test_through)


SequenceSpec = (
    ReverseAddSequenceSpec
    | CollatzSequenceSpec
    | PrimeBlockSequenceSpec
    | FermatSequenceSpec
    | MersenneSequenceSpec
)


@dataclass(frozen=True, slots=True)
class FactoredRadixProjection:
    factor_limit: int
    group_count: int
    total_group_bits: int
    residues: tuple[int, ...]
    morphism_compositions: int
    morphism_description_bits: int
    gcd_calls: int
    noncoprime_groups: int
    small_factor_witness: int | None = None


@dataclass(frozen=True, slots=True)
class RadixTermMetrics:
    index: int
    radix: int
    width: Extent
    runs: int
    word_nodes: int
    word_description_bits: int
    formula_nodes: int = 0
    formula_description_bits: int = 0
    value: int | None = None
    primary_jet: PrimaryJetBlock | None = None
    factored_projection: FactoredRadixProjection | None = None


@dataclass(frozen=True, slots=True)
class ReverseAddCompilation:
    spec: ReverseAddSequenceSpec
    terms: tuple[RadixTermMetrics, ...]
    live_rows_average: float | None
    live_rows_max: int | None
    live_carry_bits_ratio: float | None
    cyclotomic_memory_max: tuple[tuple[int, int], ...]
    cyclotomic_radial_modes: tuple[PowerTwoCyclotomicRadialQuotient, ...] = ()
    growth_state_classes: int = 0
    growth_state_max_bits: int = 0
    carry_reset_max_bits: int = 0
    symmetry_frame_modes: tuple[ReverseAddSymmetryLinearAction, ...] = ()

    @property
    def growths(self) -> tuple[int, ...]:
        widths: list[int] = []
        for term in self.terms:
            if not isinstance(term.width, int):
                raise ValueError("growth differences require projected integer widths")
            widths.append(term.width)
        return tuple(b - a for a, b in zip(widths[:-1], widths[1:], strict=True))


@dataclass(frozen=True, slots=True)
class CollatzRawFieldQuotient:
    radix: int
    sentinel_digit: int
    odd_steps: int
    valuation_sum: int
    increase_symbols: int
    nonincreasing_symbols: int
    valuation_digit_checks: int
    source_digits: int
    stripped_digits: int
    residual_transform_digits: int
    scalar_carry_peak: int


@dataclass(frozen=True, slots=True)
class CollatzCompilation:
    spec: CollatzSequenceSpec
    terms: tuple[RadixTermMetrics, ...]
    branches: tuple[str, ...]
    normalized_padic_radial: PadicRadialQuotient | None = None
    raw_field_quotient: CollatzRawFieldQuotient | None = None
    valuation_projection: CollatzValuationProjectionBlock | None = None
    valuation_state_classes: int = 0
    valuation_state_max_bits: int = 0
    future_valuation_roots: tuple[CollatzFutureValuationRoot, ...] = ()

    @property
    def successor_morphism_key(self) -> tuple[object, ...]:
        return COLLATZ_PIECEWISE_MORPHISM.canonical_key


@dataclass(frozen=True, slots=True)
class PrimeFactoredAutomatonCompilation:
    group_count: int
    total_group_bits: int
    start_morphism_compositions: int
    first_index: int | None
    first_jump_compositions: int
    first_gcd_calls: int
    start_primary_jet: PrimaryJetBlock | None = None
    first_primary_jet: PrimaryJetBlock | None = None
    cyclotomic_group_count: int = 0
    cyclotomic_state_bits: int = 0
    cyclotomic_descriptor_bits: int = 0
    cyclotomic_prime_candidates: int = 0
    cyclotomic_root_trials: int = 0
    cyclotomic_first_calls: int = 0
    selected_random_access: str = "packed"


@dataclass(frozen=True, slots=True)
class PrimeBlockCompilation:
    spec: PrimeBlockSequenceSpec
    decision: PrimeLaneQuotientCompilation
    automaton: PrimeFactoredAutomatonCompilation | None = None
    translation_sensitivity: ValuationSensitivityMorphism | None = None
    wheel_automaton: PrimeWheelCyclotomicAutomaton | None = None


@dataclass(frozen=True, slots=True)
class SpecialDepthCertificateSummary:
    """Prime/composite decision from the internal special-number depth quotient.

    ``status`` is one of ``prime``, ``composite`` or ``unknown``.  Raw source
    compilation never asks for this object.  On an explicitly demanded theorem
    query, compact constraint propagation runs first; unavailable candidate
    recovery stays unknown. Recurrence oracles are not production fallbacks.
    An explicitly requested proper-factor witness can establish compositeness.
    """

    family: str
    parameter: int
    modulus_bits: int
    status: str
    method: str
    quotient_classes: int = 0
    quotient_state_bits: int = 0
    construction_states: int = 0
    construction_raw_squarings: int = 0
    specialization_raw_squarings: int = 0
    target_depth: int | None = None
    scalable_construction: bool = False
    carrier_states_enumerated: int = 0
    character_queries: int = 0
    reciprocity_descents: int = 0
    gcd_witnesses: int = 0
    stable_image_states: int = 0
    image_depth_classes: int = 0
    moore_equals_image_depth: bool | None = None
    factor_witness: int | None = None

    def __post_init__(self) -> None:
        if self.family not in ("fermat", "mersenne"):
            raise ValueError(self.family)
        if self.status not in ("prime", "composite", "unknown"):
            raise ValueError(self.status)
        if self.parameter < 0 or self.modulus_bits <= 0:
            raise ValueError((self.parameter, self.modulus_bits))
        counts = (
            self.quotient_classes,
            self.quotient_state_bits,
            self.construction_states,
            self.construction_raw_squarings,
            self.specialization_raw_squarings,
            self.carrier_states_enumerated,
            self.character_queries,
            self.reciprocity_descents,
            self.gcd_witnesses,
            self.stable_image_states,
            self.image_depth_classes,
        )
        if any(value < 0 for value in counts):
            raise ValueError(counts)
        if self.scalable_construction and self.carrier_states_enumerated:
            raise ValueError("scalable certificate cannot enumerate a carrier")

    @property
    def decided(self) -> bool:
        return self.status != "unknown"

    @property
    def passes(self) -> bool:
        """Compatibility spelling for callers that only need the prime bit."""
        return self.status == "prime"


@dataclass(frozen=True, slots=True)
class FermatCompiledTerm:
    index: int
    number_bits: Extent
    cyclotomic_order: Extent
    radix_word: RadixTermMetrics
    primality: SpecialDepthCertificateSummary | None
    projection_method: str = "deferred"
    factor_witness: int | None = None
    reinterpretations: tuple[RadixTermMetrics, ...] = ()
    shifted_sensitivity: ValuationSensitivityMorphism | None = None
    digit_projection: None = None
    source_guard: SpecialSourceGuard | None = None


_SpecialSpecT = TypeVar("_SpecialSpecT")
_SpecialTermT = TypeVar("_SpecialTermT")


@dataclass(frozen=True, slots=True)
class SpecialCompilation(Generic[_SpecialSpecT, _SpecialTermT]):
    """Shared immutable container for sparse special-number compilations.

    Fermat and Mersenne previously duplicated this two-field wrapper even
    though family semantics live entirely in their term/spec records.
    Compatibility aliases below keep the public spellings without retaining
    parallel runtime carrier classes.
    """

    spec: _SpecialSpecT
    terms: tuple[_SpecialTermT, ...]


FermatCompilation = SpecialCompilation[FermatSequenceSpec, FermatCompiledTerm]


@dataclass(frozen=True, slots=True)
class MersenneCompiledTerm:
    exponent: int
    number_bits: int
    radix_word: RadixTermMetrics
    composite_exponent_factor: MersenneNumberSpec | None
    primality: SpecialDepthCertificateSummary | None
    projection_method: str = "deferred"
    factor_witness: int | None = None
    reinterpretations: tuple[RadixTermMetrics, ...] = ()
    successor_sensitivity: ValuationSensitivityMorphism | None = None
    digit_projection: None = None
    source_guard: SpecialSourceGuard | None = None


MersenneCompilation = SpecialCompilation[MersenneSequenceSpec, MersenneCompiledTerm]


SequenceCompilation = (
    ReverseAddCompilation
    | CollatzCompilation
    | PrimeBlockCompilation
    | SpecialCompilation[FermatSequenceSpec, FermatCompiledTerm]
    | SpecialCompilation[MersenneSequenceSpec, MersenneCompiledTerm]
)


__all__ = [
    "ReverseAddSequenceSpec",
    "CollatzSequenceSpec",
    "PrimeBlockSequenceSpec",
    "FermatSequenceSpec",
    "MersenneSequenceSpec",
    "SequenceSpec",
    "FactoredRadixProjection",
    "RadixTermMetrics",
    "ReverseAddCompilation",
    "CollatzRawFieldQuotient",
    "CollatzCompilation",
    "PrimeFactoredAutomatonCompilation",
    "PrimeBlockCompilation",
    "SpecialDepthCertificateSummary",
    "FermatCompiledTerm",
    "SpecialCompilation",
    "FermatCompilation",
    "MersenneCompiledTerm",
    "MersenneCompilation",
    "SequenceCompilation",
]
