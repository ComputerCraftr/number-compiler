"""Canonical family capabilities and lazy execution/observation bindings."""

from __future__ import annotations

from collections.abc import Mapping
from types import MappingProxyType
from typing import Final

from number_compiler.api.cli_types import (
    AntihydraObservationOptions,
    CollatzEventObservationOptions,
    CollatzTermObservationOptions,
    CommaObservationOptions,
    DoubleReverseObservationOptions,
    PrimeObservationOptions,
    ReverseAddObservationOptions,
    SpecialObservationOptions,
)
from number_compiler.api.family_types import (
    AdapterBinding,
    AdmitObserver,
    FamilyCapability,
    FamilySpec,
    ObservationAdapter,
    ObservationValueBinding,
    ObserveObserver,
    PrepareObserver,
    ProjectionAdapter,
    SizeBound,
    VerificationAdapter,
)
from number_compiler.api.matrix_contracts import (
    MatrixCapability,
    MatrixClock,
    MatrixCoordinate,
    MatrixLaw,
)
from number_compiler.api.observation_types import (
    IndexUnit,
    ObservationAdapterBinding,
    ObservationId,
    OptionSpec,
    OptionValueKind,
    SelectorId,
)
from number_compiler.api.query_types import (
    AntihydraTermQuery,
    AntihydraVerifyQuery,
    CollatzEventQuery,
    CollatzTermQuery,
    CommaTermQuery,
    DoubleReverseTermQuery,
    FermatTermQuery,
    MersenneTermQuery,
    PrimeTermQuery,
    ReverseAddTermQuery,
)
from number_compiler.arithmetic.contracts.family_identity import FamilyId

_OBSERVATION_MODULE = "number_compiler.api.observation_adapters"
_NOOP_PREPARE = "prepare_noop"
_NOOP_ADMIT = "admit_noop"
_NOOP_OBSERVE = "observe_noop"


def _observation(
    prepare: str = _NOOP_PREPARE,
    admit: str = _NOOP_ADMIT,
    observe: str = _NOOP_OBSERVE,
    *,
    module: str = _OBSERVATION_MODULE,
) -> ObservationAdapterBinding:
    return ObservationAdapterBinding(module, prepare, admit, observe)


_COMMON_OBSERVER_OPTIONS = {
    "defect": OptionSpec(None, (ObservationId.NUMBER_THEORY_ROOT,)),
    "modulus": OptionSpec(
        257,
        (
            ObservationId.ARITHMETIC_MODULAR,
            ObservationId.ARITHMETIC_TWISTED,
            ObservationId.SPATIAL_TAPE,
            ObservationId.TEMPORAL_SPACETIME,
            ObservationId.ARITHMETIC_HASSE,
            ObservationId.ARITHMETIC_FACTOR,
            ObservationId.TEMPORAL_ACCUMULATOR,
            ObservationId.TEMPORAL_INNOVATION_BORROW,
        ),
    ),
    "width": OptionSpec(
        2,
        (
            ObservationId.SPATIAL_MIRROR,
            ObservationId.ARITHMETIC_TWISTED,
            ObservationId.SPATIAL_TAPE,
            ObservationId.TEMPORAL_SPACETIME,
            ObservationId.TEMPORAL_DIAGONAL_CARRY,
            ObservationId.ARITHMETIC_HASSE,
            ObservationId.ARITHMETIC_FACTOR,
        ),
        flag_name="spatial_width",
    ),
    "sign": OptionSpec(
        -1,
        (
            ObservationId.ARITHMETIC_TWISTED,
            ObservationId.SPATIAL_TAPE,
            ObservationId.TEMPORAL_SPACETIME,
            ObservationId.ARITHMETIC_FACTOR,
        ),
    ),
    "precision": OptionSpec(
        8, (ObservationId.ARITHMETIC_HENSEL, ObservationId.ARITHMETIC_MAHLER)
    ),
    "target": OptionSpec(0, (ObservationId.ARITHMETIC_HENSEL,)),
    "s_weight": OptionSpec(1, (ObservationId.ARITHMETIC_TROPICAL,)),
    "z_weight": OptionSpec(1, (ObservationId.ARITHMETIC_TROPICAL,)),
    "time_width": OptionSpec(2, (ObservationId.TEMPORAL_SPACETIME,)),
    "time_sign": OptionSpec(1, (ObservationId.TEMPORAL_SPACETIME,)),
}


def _opts(*names: str) -> tuple[tuple[str, OptionSpec], ...]:
    return tuple((name, _COMMON_OBSERVER_OPTIONS[name]) for name in names)


_CAPABILITY_ENTRIES: dict[FamilyId, FamilySpec] = {
    FamilyId.REVERSE_ADD: FamilySpec(
        FamilyCapability(
            IndexUnit.ITERATIONS,
            ("seed", "base"),
            (
                ObservationId.METRICS,
                ObservationId.SPATIAL_MIRROR,
                ObservationId.TEMPORAL_MACRO,
                ObservationId.TEMPORAL_MATRIX,
                ObservationId.TEMPORAL_RESIDUE99,
                ObservationId.TEMPORAL_ACCUMULATOR99,
                ObservationId.TEMPORAL_OPEN_RING,
                ObservationId.TEMPORAL_SEED_ORBIT,
                ObservationId.TEMPORAL_STENCIL,
                ObservationId.SPATIAL_BANK_MORPHISM,
            ),
        ),
        ReverseAddTermQuery,
        AdapterBinding("number_compiler.api.projections.reverse_add", "project"),
        _observation("prepare_reverse", "admit_reverse", "observe_reverse"),
        term_observation=ObservationValueBinding(
            ReverseAddObservationOptions,
            (
                "width",
                "max_digits",
                "pair_bank_position",
                "bank_morphism_count",
                "grammar_period",
            ),
        ),
        observer_options=_opts("width")
        + (
            (
                "max_digits",
                OptionSpec(
                    4096, (ObservationId.SPATIAL_MIRROR, ObservationId.TEMPORAL_STENCIL)
                ),
            ),
            (
                "pair_bank_position",
                OptionSpec(
                    0,
                    (
                        ObservationId.SPATIAL_BANK_MORPHISM,
                        ObservationId.TEMPORAL_OPEN_RING,
                    ),
                    flag_name="spatial_pair_bank_position",
                ),
            ),
            (
                "bank_morphism_count",
                OptionSpec(
                    16,
                    (
                        ObservationId.SPATIAL_BANK_MORPHISM,
                        ObservationId.TEMPORAL_OPEN_RING,
                    ),
                    flag_name="spatial_bank_morphism_count",
                ),
            ),
            (
                "grammar_period",
                OptionSpec(
                    2,
                    (ObservationId.SPATIAL_BANK_MORPHISM,),
                    flag_name="temporal_grammar_period",
                ),
            ),
        ),
        bounded_observations=(
            ObservationId.SPATIAL_MIRROR,
            ObservationId.TEMPORAL_STENCIL,
            ObservationId.SPATIAL_BANK_MORPHISM,
        ),
        output_bound=SizeBound.SEED,
        observation_constraints=(
            (
                ObservationId.TEMPORAL_OPEN_RING,
                "base",
                10,
                "temporal open ring requires decimal base",
            ),
            (
                ObservationId.TEMPORAL_SEED_ORBIT,
                "base",
                10,
                "seed-orbit Q19 morphism requires decimal base",
            ),
            (
                ObservationId.TEMPORAL_MACRO,
                "base",
                10,
                "boundary-macro observation requires decimal base",
            ),
            (
                ObservationId.TEMPORAL_MATRIX,
                "base",
                10,
                "temporal-matrix requires decimal base",
            ),
            (
                ObservationId.TEMPORAL_STENCIL,
                "base",
                10,
                "temporal-stencil requires decimal base",
            ),
            (
                ObservationId.TEMPORAL_RESIDUE99,
                "base",
                10,
                "temporal residue99 requires decimal base",
            ),
            (
                ObservationId.TEMPORAL_ACCUMULATOR99,
                "base",
                10,
                "temporal accumulator99 requires decimal base",
            ),
            (
                ObservationId.SPATIAL_BANK_MORPHISM,
                "base",
                10,
                "reverse/add spatial bank morphism requires decimal base",
            ),
        ),
        matrix=MatrixCapability(
            "number_compiler.api.matrix_observation",
            "reverse_transfer",
            MatrixCoordinate.PAIR_DEPTH,
            128,
            12,
            innovation=True,
            minimum_coordinate=1,
        ),
    ),
    FamilyId.DOUBLE_REVERSE: FamilySpec(
        FamilyCapability(
            IndexUnit.ITERATIONS,
            ("seed",),
            (
                ObservationId.METRICS,
                ObservationId.TEMPORAL_MATRIX,
                ObservationId.TEMPORAL_CLOSED_FORM,
                ObservationId.TEMPORAL_RESIDUE99,
                ObservationId.TEMPORAL_SEED_MORPHISM,
                ObservationId.TEMPORAL_DEFECT_CLOCK,
                ObservationId.TEMPORAL_CARRY_SAFETY,
                ObservationId.SPATIAL_STENCIL,
                ObservationId.TEMPORAL_BANK,
                ObservationId.TEMPORAL_OPEN_RING,
                ObservationId.TEMPORAL_BIRTH_LAYERS,
                ObservationId.SPATIAL_PAIR_BANK,
                ObservationId.SPATIAL_BANK_MORPHISM,
                ObservationId.SPATIAL_BANK_WINDOW,
                ObservationId.TEMPORAL_GRAMMAR,
                ObservationId.TEMPORAL_RADIX_WALSH,
                ObservationId.ARITHMETIC_RADIX25_SHIFT,
            ),
        ),
        DoubleReverseTermQuery,
        AdapterBinding("number_compiler.api.projections.double_reverse", "project"),
        _observation(observe="observe_double_reverse"),
        term_observation=ObservationValueBinding(
            DoubleReverseObservationOptions,
            (
                "modulus",
                "stencil_position",
                "pair_bank_position",
                "bank_morphism_count",
                "grammar_position",
                "grammar_period",
                "radix_places",
                "walsh_start",
                "open_ring_lookback",
                "period_samples",
                "defect_digits",
                "period_stride",
                "period_depth",
                "period_max_lag",
                "period_drivers",
                "prefix_horizon",
            ),
        ),
        observer_options=(
            (
                "prefix_horizon",
                OptionSpec(
                    128,
                    (
                        ObservationId.TEMPORAL_SEED_MORPHISM,
                        ObservationId.TEMPORAL_DEFECT_CLOCK,
                    ),
                    flag_name="temporal_prefix_horizon",
                    help="maximum exact chronological prefix before dyadic powering",
                ),
            ),
            (
                "period_samples",
                OptionSpec(
                    0,
                    (
                        ObservationId.TEMPORAL_SEED_MORPHISM,
                        ObservationId.TEMPORAL_DEFECT_CLOCK,
                    ),
                    flag_name="temporal_period_samples",
                    help="number of four-phase center samples (0 omits scan)",
                ),
            ),
            (
                "defect_digits",
                OptionSpec(
                    0,
                    (
                        ObservationId.TEMPORAL_DEFECT_CLOCK,
                        ObservationId.TEMPORAL_SEED_MORPHISM,
                    ),
                    flag_name="temporal_defect_digits",
                    help="decimal suffix digits in a joined four-symbol carry-defect clock",
                ),
            ),
            (
                "period_stride",
                OptionSpec(
                    1,
                    (
                        ObservationId.TEMPORAL_SEED_MORPHISM,
                        ObservationId.TEMPORAL_DEFECT_CLOCK,
                    ),
                    flag_name="temporal_period_stride",
                    help="spacing in four-generation blocks",
                ),
            ),
            (
                "period_depth",
                OptionSpec(
                    2,
                    (ObservationId.TEMPORAL_SEED_MORPHISM,),
                    flag_name="temporal_period_depth",
                    help="maximum inward center-window radius",
                ),
            ),
            (
                "period_max_lag",
                OptionSpec(
                    16,
                    (
                        ObservationId.TEMPORAL_SEED_MORPHISM,
                        ObservationId.TEMPORAL_DEFECT_CLOCK,
                    ),
                    flag_name="temporal_period_max_lag",
                    help="maximum sampled lag to check for finite-window returns",
                ),
            ),
            (
                "period_drivers",
                OptionSpec(
                    False,
                    (ObservationId.TEMPORAL_SEED_MORPHISM,),
                    value_kind=OptionValueKind.BOOLEAN,
                    flag_name="temporal_period_drivers",
                    help="also certify actual four-tick carry/F5 center drivers",
                ),
            ),
            (
                "open_ring_lookback",
                OptionSpec(
                    8,
                    (
                        ObservationId.TEMPORAL_OPEN_RING,
                        ObservationId.TEMPORAL_BIRTH_LAYERS,
                    ),
                    flag_name="temporal_open_ring_lookback",
                ),
            ),
            (
                "modulus",
                OptionSpec(
                    None,
                    (ObservationId.TEMPORAL_CLOSED_FORM,),
                    flag_name="temporal_closed_form_modulus",
                ),
            ),
            (
                "stencil_position",
                OptionSpec(
                    0,
                    (ObservationId.SPATIAL_STENCIL,),
                    flag_name="spatial_stencil_position",
                ),
            ),
            (
                "pair_bank_position",
                OptionSpec(
                    0,
                    (
                        ObservationId.SPATIAL_PAIR_BANK,
                        ObservationId.SPATIAL_BANK_MORPHISM,
                        ObservationId.SPATIAL_BANK_WINDOW,
                        ObservationId.TEMPORAL_OPEN_RING,
                    ),
                    flag_name="spatial_pair_bank_position",
                ),
            ),
            (
                "bank_morphism_count",
                OptionSpec(
                    16,
                    (
                        ObservationId.SPATIAL_BANK_MORPHISM,
                        ObservationId.SPATIAL_BANK_WINDOW,
                        ObservationId.TEMPORAL_OPEN_RING,
                        ObservationId.TEMPORAL_BIRTH_LAYERS,
                    ),
                    flag_name="spatial_bank_morphism_count",
                ),
            ),
            (
                "grammar_position",
                OptionSpec(
                    0,
                    (
                        ObservationId.TEMPORAL_GRAMMAR,
                        ObservationId.TEMPORAL_RADIX_WALSH,
                    ),
                    flag_name="temporal_grammar_position",
                ),
            ),
            (
                "grammar_period",
                OptionSpec(
                    2,
                    (
                        ObservationId.TEMPORAL_GRAMMAR,
                        ObservationId.TEMPORAL_RADIX_WALSH,
                        ObservationId.SPATIAL_BANK_MORPHISM,
                    ),
                    flag_name="temporal_grammar_period",
                ),
            ),
            (
                "radix_places",
                OptionSpec(
                    8,
                    (
                        ObservationId.ARITHMETIC_RADIX25_SHIFT,
                        ObservationId.TEMPORAL_RADIX_WALSH,
                    ),
                    flag_name="arithmetic_radix_places",
                ),
            ),
            (
                "walsh_start",
                OptionSpec(
                    0,
                    (ObservationId.TEMPORAL_RADIX_WALSH,),
                    flag_name="temporal_walsh_start",
                ),
            ),
        ),
        output_bound=SizeBound.SEED,
        matrix=MatrixCapability(
            "number_compiler.api.matrix_observation",
            "double_reverse_transfer",
            MatrixCoordinate.PAIR_DEPTH,
            4096,
            16,
            step_multiple=2,
            minimum_coordinate=1,
            max_trace_steps=128,
        ),
    ),
    FamilyId.COLLATZ: FamilySpec(
        FamilyCapability(
            IndexUnit.PHYSICAL_ITERATIONS,
            ("seed", "radix"),
            (
                ObservationId.METRICS,
                ObservationId.TEMPORAL_MATRIX,
                ObservationId.TEMPORAL_CLOCK,
                ObservationId.TEMPORAL_ACCUMULATOR,
                ObservationId.TEMPORAL_DOUBLE_ACCUMULATOR,
                ObservationId.TEMPORAL_DIAGONAL_CARRY,
                ObservationId.TEMPORAL_MACRO,
                ObservationId.TEMPORAL_INNOVATION_BORROW,
            ),
            (
                ObservationId.TEMPORAL_CLOCK,
                ObservationId.ARITHMETIC_MODULAR,
                ObservationId.ARITHMETIC_TWISTED,
                ObservationId.ARITHMETIC_HASSE,
                ObservationId.ARITHMETIC_HENSEL,
                ObservationId.ARITHMETIC_TROPICAL,
                ObservationId.ARITHMETIC_FACTOR,
                ObservationId.SAFETY_EXECUTION,
            ),
            event_unit=IndexUnit.ACCELERATED_ODD_EVENTS,
        ),
        CollatzTermQuery,
        AdapterBinding("number_compiler.api.projections.collatz", "project"),
        _observation("prepare_collatz", "admit_collatz", "observe_collatz"),
        event_query_type=CollatzEventQuery,
        term_observation=ObservationValueBinding(
            CollatzTermObservationOptions,
            (
                "accumulator_modulus",
                "innovation_modulus",
                "clock_max_events",
                "clock_max_digits",
            ),
        ),
        event_observation=ObservationValueBinding(
            CollatzEventObservationOptions,
            (
                "modulus",
                "twisted_width",
                "twisted_sign",
                "hasse_order",
                "precision",
                "target",
                "s_weight",
                "z_weight",
            ),
        ),
        observer_options=(
            (
                "modulus",
                OptionSpec(
                    257,
                    (
                        ObservationId.ARITHMETIC_MODULAR,
                        ObservationId.ARITHMETIC_TWISTED,
                        ObservationId.ARITHMETIC_HASSE,
                        ObservationId.ARITHMETIC_HENSEL,
                        ObservationId.ARITHMETIC_TROPICAL,
                        ObservationId.ARITHMETIC_FACTOR,
                    ),
                    flag_name="arithmetic_modulus",
                ),
            ),
            (
                "precision",
                OptionSpec(
                    8,
                    (ObservationId.ARITHMETIC_HENSEL,),
                    flag_name="arithmetic_hensel_precision",
                ),
            ),
            (
                "target",
                OptionSpec(
                    0,
                    (ObservationId.ARITHMETIC_HENSEL,),
                    flag_name="arithmetic_hensel_target",
                ),
            ),
            (
                "s_weight",
                OptionSpec(
                    1,
                    (ObservationId.ARITHMETIC_TROPICAL,),
                    flag_name="arithmetic_tropical_s_weight",
                ),
            ),
            (
                "z_weight",
                OptionSpec(
                    1,
                    (ObservationId.ARITHMETIC_TROPICAL,),
                    flag_name="arithmetic_tropical_z_weight",
                ),
            ),
        )
        + (
            (
                "twisted_width",
                OptionSpec(
                    2,
                    (ObservationId.ARITHMETIC_TWISTED,),
                    flag_name="arithmetic_twisted_width",
                ),
            ),
            (
                "twisted_sign",
                OptionSpec(
                    -1,
                    (ObservationId.ARITHMETIC_TWISTED,),
                    flag_name="arithmetic_twisted_sign",
                ),
            ),
            (
                "hasse_order",
                OptionSpec(
                    2,
                    (ObservationId.ARITHMETIC_HASSE,),
                    flag_name="arithmetic_hasse_order",
                ),
            ),
        )
        + (
            (
                "accumulator_modulus",
                OptionSpec(
                    257,
                    (ObservationId.TEMPORAL_ACCUMULATOR,),
                    flag_name="temporal_accumulator_modulus",
                ),
            ),
            (
                "innovation_modulus",
                OptionSpec(
                    257,
                    (ObservationId.TEMPORAL_INNOVATION_BORROW,),
                    flag_name="temporal_innovation_borrow_modulus",
                ),
            ),
            (
                "clock_max_events",
                OptionSpec(
                    4096,
                    (ObservationId.TEMPORAL_CLOCK,),
                    flag_name="temporal_clock_max_events",
                ),
            ),
            (
                "clock_max_digits",
                OptionSpec(
                    4096,
                    (
                        ObservationId.TEMPORAL_CLOCK,
                        ObservationId.TEMPORAL_DIAGONAL_CARRY,
                    ),
                    flag_name="temporal_clock_max_digits",
                ),
            ),
        ),
        bounded_observations=(ObservationId.TEMPORAL_CLOCK,),
        clock_budget=(
            ObservationId.TEMPORAL_CLOCK,
            "clock_max_events",
            "seed",
            "clock_max_digits",
        ),
        selector_restrictions=(
            (
                SelectorId.EVENTS,
                ("output_base", "max_output_bits"),
                "event observations have no term output to format or limit",
            ),
            (
                SelectorId.EVENTS,
                ("radix",),
                "--radix applies to Collatz --nth terms, not --events",
            ),
        ),
        output_bound=SizeBound.COLLATZ_SEED_AT_ZERO,
        matrix=MatrixCapability(
            "number_compiler.api.matrix_observation",
            "collatz_transfer",
            MatrixCoordinate.LOW_BORDER,
            128,
            0,
            default_coordinate=None,
            law=MatrixLaw.PARITY_WEIGHTED_CARRY,
        ),
    ),
    FamilyId.ANTIHYDRA: FamilySpec(
        FamilyCapability(
            IndexUnit.MACRO_RETURNS_AFTER_STARTUP,
            (),
            (
                ObservationId.METRICS,
                ObservationId.TEMPORAL_MATRIX,
                ObservationId.SAFETY_LEDGER,
                ObservationId.TEMPORAL_CLOCK,
                ObservationId.ARITHMETIC_MODULAR,
                ObservationId.SPATIAL_TAPE,
                ObservationId.ARITHMETIC_TWISTED,
                ObservationId.TEMPORAL_SPACETIME,
                ObservationId.TEMPORAL_DIAGONAL_CARRY,
                ObservationId.ARITHMETIC_HASSE,
                ObservationId.ARITHMETIC_HENSEL,
                ObservationId.ARITHMETIC_MAHLER,
                ObservationId.ARITHMETIC_TROPICAL,
                ObservationId.ARITHMETIC_FACTOR,
            ),
        ),
        AntihydraTermQuery,
        AdapterBinding("number_compiler.api.projections.antihydra", "project"),
        _observation(
            "prepare_antihydra",
            "admit_antihydra",
            "observe_antihydra",
            module="number_compiler.api.antihydra_adapters",
        ),
        verify_query_type=AntihydraVerifyQuery,
        verify_flag="verify_nonhalting",
        verification=AdapterBinding(
            "number_compiler.api.observation_adapters", "verify_antihydra"
        ),
        description=(
            "antihydra: --nth uses macro_returns_after_startup; term zero is the seed. "
            "Certificate verification is a separate selector."
        ),
        term_observation=ObservationValueBinding(
            AntihydraObservationOptions,
            (
                "modulus",
                "width",
                "sign",
                "precision",
                "time_width",
                "time_sign",
                "max_observer_terms",
            ),
        ),
        observer_options=_opts(
            "modulus", "width", "sign", "precision", "time_width", "time_sign"
        )
        + (
            (
                "max_observer_terms",
                OptionSpec(
                    1_000_000,
                    (
                        ObservationId.TEMPORAL_SPACETIME,
                        ObservationId.TEMPORAL_DIAGONAL_CARRY,
                    ),
                ),
            ),
        ),
        matrix=MatrixCapability(
            "number_compiler.api.matrix_observation",
            "antihydra_transfer",
            MatrixCoordinate.CENTER_SPLIT,
            32,
            256,
            default_coordinate=None,
            law=MatrixLaw.AFFINE_PREFIX_SAFETY,
        ),
    ),
    FamilyId.A367620: FamilySpec(
        FamilyCapability(
            IndexUnit.OEIS_INDEX,
            (),
            (
                ObservationId.METRICS,
                ObservationId.TEMPORAL_CLOCK,
                ObservationId.ARITHMETIC_TROPICAL,
                ObservationId.SAFETY_CERTIFICATE,
            ),
        ),
        CommaTermQuery,
        AdapterBinding("number_compiler.api.projections.comma", "project"),
        _observation("prepare_noop", "admit_comma", "observe_comma"),
        term_observation=ObservationValueBinding(CommaObservationOptions),
        description=(
            "a367620: one-based OEIS index; fixed decimal source 20. "
            "Exact values require a checked infinite-path prefix. "
            "Use --no-value --info certificate to inspect availability."
        ),
    ),
    FamilyId.PRIME: FamilySpec(
        FamilyCapability(IndexUnit.PRIME_INDEX, ("start",), (ObservationId.METRICS,)),
        PrimeTermQuery,
        AdapterBinding("number_compiler.api.projections.prime", "project"),
        _observation(),
        term_observation=ObservationValueBinding(PrimeObservationOptions),
        output_bound=SizeBound.PRIME_UPPER,
        scalar_value=AdapterBinding(
            "number_compiler.api.projections.prime_value", "value"
        ),
    ),
    FamilyId.FERMAT: FamilySpec(
        FamilyCapability(
            IndexUnit.FERMAT_INDEX,
            (),
            (
                ObservationId.METRICS,
                ObservationId.TEMPORAL_MATRIX,
                ObservationId.NUMBER_THEORY_PRIMALITY,
                ObservationId.NUMBER_THEORY_FACTOR,
                ObservationId.NUMBER_THEORY_ROOT,
            ),
        ),
        FermatTermQuery,
        AdapterBinding(
            "number_compiler.api.projections.power_numbers", "project_fermat"
        ),
        _observation("prepare_noop", "admit_fermat", "observe_special"),
        term_observation=ObservationValueBinding(
            SpecialObservationOptions,
            (
                "defect",
                "max_digits",
                "max_candidate_bits",
                "max_factor_products",
                "ordered_carry_windows",
            ),
        ),
        observer_options=_opts("defect")
        + (
            ("max_digits", OptionSpec(4096, ())),
            ("max_candidate_bits", OptionSpec(1_000_000, ())),
            ("max_factor_products", OptionSpec(4096, ())),
            (
                "ordered_carry_windows",
                OptionSpec(
                    False,
                    (ObservationId.NUMBER_THEORY_PRIMALITY,),
                    value_kind=OptionValueKind.BOOLEAN,
                ),
            ),
        ),
        candidate_bound=SizeBound.DYADIC,
        candidate_information=(
            ObservationId.NUMBER_THEORY_PRIMALITY,
            ObservationId.NUMBER_THEORY_FACTOR,
            ObservationId.NUMBER_THEORY_ROOT,
        ),
        output_bound=SizeBound.DYADIC,
        matrix=MatrixCapability(
            "number_compiler.api.matrix_observation",
            "fermat_transfer",
            MatrixCoordinate.DIGIT_POSITION,
            4096,
            256,
            max_source_index=16,
            law=MatrixLaw.ORDERED_TRIPLING_CARRY,
            clock=MatrixClock.TRIPLING,
            max_trace_steps=64,
        ),
    ),
    FamilyId.MERSENNE: FamilySpec(
        FamilyCapability(
            IndexUnit.MERSENNE_EXPONENT,
            (),
            (
                ObservationId.METRICS,
                ObservationId.TEMPORAL_MATRIX,
                ObservationId.NUMBER_THEORY_PRIMALITY,
                ObservationId.NUMBER_THEORY_FACTOR,
                ObservationId.NUMBER_THEORY_ROOT,
            ),
        ),
        MersenneTermQuery,
        AdapterBinding(
            "number_compiler.api.projections.power_numbers", "project_mersenne"
        ),
        _observation("prepare_noop", "admit_noop", "observe_special"),
        term_observation=ObservationValueBinding(
            SpecialObservationOptions,
            ("defect", "max_digits", "max_candidate_bits", "max_factor_products"),
        ),
        observer_options=_opts("defect")
        + (
            ("max_digits", OptionSpec(4096, ())),
            ("max_candidate_bits", OptionSpec(1_000_000, ())),
            ("max_factor_products", OptionSpec(4096, ())),
        ),
        information_minima=(
            (
                2,
                (
                    ObservationId.NUMBER_THEORY_PRIMALITY,
                    ObservationId.NUMBER_THEORY_FACTOR,
                    ObservationId.NUMBER_THEORY_ROOT,
                ),
                "special theorem parameter must be at least 2",
            ),
        ),
        candidate_bound=SizeBound.INDEX,
        candidate_information=(
            ObservationId.NUMBER_THEORY_PRIMALITY,
            ObservationId.NUMBER_THEORY_FACTOR,
            ObservationId.NUMBER_THEORY_ROOT,
        ),
        output_bound=SizeBound.INDEX,
        matrix=MatrixCapability(
            "number_compiler.api.matrix_observation",
            "mersenne_transfer",
            MatrixCoordinate.DIGIT_POSITION,
            4096,
            64,
            max_source_index=1_000_000,
            law=MatrixLaw.NORM_ONE_TRACE,
            clock=MatrixClock.TRACE_SQUARING,
            max_trace_steps=64,
        ),
    ),
}
CAPABILITIES: Final[Mapping[FamilyId, FamilySpec]] = MappingProxyType(
    _CAPABILITY_ENTRIES
)
del _CAPABILITY_ENTRIES


def family_spec(family: FamilyId) -> FamilySpec:
    """Return a registered family using its already-admitted identifier."""
    if type(family) is not FamilyId:
        raise TypeError("family lookup requires an admitted FamilyId")
    try:
        return CAPABILITIES[family]
    except KeyError as exc:
        raise ValueError(f"unknown family: {family}") from exc


__all__ = [
    "CAPABILITIES",
    "AdapterBinding",
    "AdmitObserver",
    "FamilyCapability",
    "FamilySpec",
    "ObservationAdapter",
    "ObservationAdapterBinding",
    "ObservationValueBinding",
    "ObserveObserver",
    "OptionSpec",
    "PrepareObserver",
    "ProjectionAdapter",
    "VerificationAdapter",
    "family_spec",
]
