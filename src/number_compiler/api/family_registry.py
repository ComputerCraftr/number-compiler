"""Canonical family capabilities and lazy execution/observation bindings."""

from __future__ import annotations

from dataclasses import dataclass, fields
from importlib import import_module
from typing import cast

from number_compiler.api.cli_types import (
    AntihydraObservationOptions,
    CollatzEventObservationOptions,
    CollatzTermObservationOptions,
    CommaObservationOptions,
    DoubleReverseObservationOptions,
    PresentationOptions,
    PrimeObservationOptions,
    QueryRequest,
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
    VerificationAdapter,
)
from number_compiler.api.observation_types import (
    FamilyId,
    IndexUnit,
    ObservationAdapterBinding,
    ObservationId,
    OptionSpec,
    OutputFormat,
    SelectorId,
    family_id,
)
from number_compiler.api.query_types import (
    AntihydraTermQuery,
    AntihydraVerifyQuery,
    CollatzEventQuery,
    CollatzTermQuery,
    CommaTermQuery,
    DoubleReverseTermQuery,
    ExecutionQuery,
    FermatTermQuery,
    MersenneTermQuery,
    PrimeTermQuery,
    ReverseAddTermQuery,
    TermQuery,
)

_OBSERVATION_MODULE = "number_compiler.api.observation_adapters"
_NOOP_PREPARE = "prepare_noop"
_NOOP_ADMIT = "admit_noop"
_NOOP_OBSERVE = "observe_noop"


def _observation(
    prepare: str = _NOOP_PREPARE,
    admit: str = _NOOP_ADMIT,
    observe: str = _NOOP_OBSERVE,
) -> ObservationAdapterBinding:
    return ObservationAdapterBinding(_OBSERVATION_MODULE, prepare, admit, observe)


_COMMON_OBSERVER_OPTIONS = {
    "defect": OptionSpec(None, ("number-theory.root",)),
    "modulus": OptionSpec(
        257,
        (
            "arithmetic.modular",
            "arithmetic.twisted",
            "spatial.tape",
            "temporal.spacetime",
            "arithmetic.hasse",
            "arithmetic.factor",
            "temporal.accumulator",
            "temporal.innovation-borrow",
        ),
    ),
    "width": OptionSpec(
        2,
        (
            "spatial.mirror",
            "arithmetic.twisted",
            "spatial.tape",
            "temporal.spacetime",
            "arithmetic.hasse",
            "arithmetic.factor",
        ),
        flag_name="spatial_width",
    ),
    "sign": OptionSpec(
        -1,
        (
            "arithmetic.twisted",
            "spatial.tape",
            "temporal.spacetime",
            "arithmetic.factor",
        ),
    ),
    "precision": OptionSpec(8, ("arithmetic.hensel", "arithmetic.mahler")),
    "target": OptionSpec(0, ("arithmetic.hensel",)),
    "s_weight": OptionSpec(1, ("arithmetic.tropical",)),
    "z_weight": OptionSpec(1, ("arithmetic.tropical",)),
    "time_width": OptionSpec(2, ("temporal.spacetime",)),
    "time_sign": OptionSpec(1, ("temporal.spacetime",)),
}


def _opts(*names: str) -> tuple[tuple[str, OptionSpec], ...]:
    return tuple((name, _COMMON_OBSERVER_OPTIONS[name]) for name in names)


CAPABILITIES: dict[FamilyId, FamilySpec] = {
    FamilyId.REVERSE_ADD: FamilySpec(
        FamilyCapability(
            "iterations",
            ("seed", "base"),
            (
                "metrics",
                "spatial.mirror",
                "temporal.macro",
                "temporal.matrix",
                "temporal.residue99",
                "temporal.open-ring",
                "temporal.stencil",
                "spatial.bank-morphism",
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
                "modulus",
                "pair_bank_position",
                "bank_morphism_count",
                "grammar_period",
            ),
        ),
        observer_options=_opts("width")
        + (
            (
                "max_digits",
                OptionSpec(4096, ("spatial.mirror", "temporal.stencil")),
            ),
            (
                "modulus",
                OptionSpec(
                    None, ("temporal.matrix",), flag_name="temporal_matrix_modulus"
                ),
            ),
            (
                "pair_bank_position",
                OptionSpec(
                    0,
                    ("spatial.bank-morphism", "temporal.open-ring"),
                    flag_name="spatial_pair_bank_position",
                ),
            ),
            (
                "bank_morphism_count",
                OptionSpec(
                    16,
                    ("spatial.bank-morphism", "temporal.open-ring"),
                    flag_name="spatial_bank_morphism_count",
                ),
            ),
            (
                "grammar_period",
                OptionSpec(
                    2, ("spatial.bank-morphism",), flag_name="temporal_grammar_period"
                ),
            ),
        ),
        bounded_observations=(
            ObservationId.SPATIAL_MIRROR,
            ObservationId.TEMPORAL_STENCIL,
            ObservationId.SPATIAL_BANK_MORPHISM,
        ),
        output_bound="seed",
        observation_constraints=(
            (
                ObservationId.TEMPORAL_OPEN_RING,
                "base",
                10,
                "temporal open ring requires decimal base",
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
                ObservationId.SPATIAL_BANK_MORPHISM,
                "base",
                10,
                "reverse/add spatial bank morphism requires decimal base",
            ),
        ),
    ),
    FamilyId.DOUBLE_REVERSE: FamilySpec(
        FamilyCapability(
            "iterations",
            ("seed",),
            (
                "metrics",
                "temporal.closed-form",
                "temporal.residue99",
                "temporal.carry-safety",
                "spatial.stencil",
                "temporal.bank",
                "temporal.open-ring",
                "temporal.birth-layers",
                "spatial.pair-bank",
                "spatial.bank-morphism",
                "spatial.bank-window",
                "temporal.grammar",
                "temporal.radix-walsh",
                "arithmetic.radix25-shift",
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
            ),
        ),
        observer_options=(
            (
                "open_ring_lookback",
                OptionSpec(
                    8,
                    ("temporal.open-ring", "temporal.birth-layers"),
                    flag_name="temporal_open_ring_lookback",
                ),
            ),
            (
                "modulus",
                OptionSpec(
                    None,
                    ("temporal.closed-form",),
                    flag_name="temporal_closed_form_modulus",
                ),
            ),
            (
                "stencil_position",
                OptionSpec(
                    0,
                    ("spatial.stencil",),
                    flag_name="spatial_stencil_position",
                ),
            ),
            (
                "pair_bank_position",
                OptionSpec(
                    0,
                    (
                        "spatial.pair-bank",
                        "spatial.bank-morphism",
                        "spatial.bank-window",
                        "temporal.open-ring",
                    ),
                    flag_name="spatial_pair_bank_position",
                ),
            ),
            (
                "bank_morphism_count",
                OptionSpec(
                    16,
                    (
                        "spatial.bank-morphism",
                        "spatial.bank-window",
                        "temporal.open-ring",
                        "temporal.birth-layers",
                    ),
                    flag_name="spatial_bank_morphism_count",
                ),
            ),
            (
                "grammar_position",
                OptionSpec(
                    0,
                    ("temporal.grammar", "temporal.radix-walsh"),
                    flag_name="temporal_grammar_position",
                ),
            ),
            (
                "grammar_period",
                OptionSpec(
                    2,
                    (
                        "temporal.grammar",
                        "temporal.radix-walsh",
                        "spatial.bank-morphism",
                    ),
                    flag_name="temporal_grammar_period",
                ),
            ),
            (
                "radix_places",
                OptionSpec(
                    8,
                    ("arithmetic.radix25-shift", "temporal.radix-walsh"),
                    flag_name="arithmetic_radix_places",
                ),
            ),
            (
                "walsh_start",
                OptionSpec(
                    0, ("temporal.radix-walsh",), flag_name="temporal_walsh_start"
                ),
            ),
        ),
        output_bound="seed",
    ),
    FamilyId.COLLATZ: FamilySpec(
        FamilyCapability(
            "physical_iterations",
            ("seed", "radix"),
            (
                "metrics",
                "temporal.clock",
                "temporal.accumulator",
                "temporal.macro",
                "temporal.innovation-borrow",
            ),
            (
                "temporal.clock",
                "arithmetic.modular",
                "arithmetic.twisted",
                "arithmetic.hasse",
                "arithmetic.hensel",
                "arithmetic.tropical",
                "arithmetic.factor",
                "safety.execution",
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
                        "arithmetic.modular",
                        "arithmetic.twisted",
                        "arithmetic.hasse",
                        "arithmetic.hensel",
                        "arithmetic.tropical",
                        "arithmetic.factor",
                    ),
                    flag_name="arithmetic_modulus",
                ),
            ),
            (
                "precision",
                OptionSpec(
                    8,
                    ("arithmetic.hensel",),
                    flag_name="arithmetic_hensel_precision",
                ),
            ),
            (
                "target",
                OptionSpec(
                    0,
                    ("arithmetic.hensel",),
                    flag_name="arithmetic_hensel_target",
                ),
            ),
            (
                "s_weight",
                OptionSpec(
                    1,
                    ("arithmetic.tropical",),
                    flag_name="arithmetic_tropical_s_weight",
                ),
            ),
            (
                "z_weight",
                OptionSpec(
                    1,
                    ("arithmetic.tropical",),
                    flag_name="arithmetic_tropical_z_weight",
                ),
            ),
        )
        + (
            (
                "twisted_width",
                OptionSpec(
                    2,
                    ("arithmetic.twisted",),
                    flag_name="arithmetic_twisted_width",
                ),
            ),
            (
                "twisted_sign",
                OptionSpec(
                    -1,
                    ("arithmetic.twisted",),
                    flag_name="arithmetic_twisted_sign",
                ),
            ),
            (
                "hasse_order",
                OptionSpec(
                    2,
                    ("arithmetic.hasse",),
                    flag_name="arithmetic_hasse_order",
                ),
            ),
        )
        + (
            (
                "accumulator_modulus",
                OptionSpec(
                    257,
                    ("temporal.accumulator",),
                    flag_name="temporal_accumulator_modulus",
                ),
            ),
            (
                "innovation_modulus",
                OptionSpec(
                    257,
                    ("temporal.innovation-borrow",),
                    flag_name="temporal_innovation_borrow_modulus",
                ),
            ),
            (
                "clock_max_events",
                OptionSpec(
                    4096,
                    ("temporal.clock",),
                    flag_name="temporal_clock_max_events",
                ),
            ),
            (
                "clock_max_digits",
                OptionSpec(
                    4096,
                    ("temporal.clock",),
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
        output_bound="collatz_seed_at_zero",
    ),
    FamilyId.ANTIHYDRA: FamilySpec(
        FamilyCapability(
            "macro_returns_after_startup",
            (),
            (
                "metrics",
                "safety.ledger",
                "temporal.clock",
                "arithmetic.modular",
                "spatial.tape",
                "arithmetic.twisted",
                "temporal.spacetime",
                "arithmetic.hasse",
                "arithmetic.hensel",
                "arithmetic.mahler",
                "arithmetic.tropical",
                "arithmetic.factor",
            ),
        ),
        AntihydraTermQuery,
        AdapterBinding("number_compiler.api.projections.antihydra", "project"),
        _observation("prepare_antihydra", "admit_noop", "observe_antihydra"),
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
        + (("max_observer_terms", OptionSpec(1_000_000, ("temporal.spacetime",))),),
    ),
    FamilyId.A367620: FamilySpec(
        FamilyCapability(
            "oeis_index",
            (),
            ("metrics", "temporal.clock", "arithmetic.tropical", "safety.certificate"),
        ),
        CommaTermQuery,
        AdapterBinding("number_compiler.api.projections.comma", "project"),
        _observation("prepare_comma", "admit_comma", "observe_comma"),
        term_observation=ObservationValueBinding(CommaObservationOptions),
        description=(
            "a367620: one-based OEIS index; fixed decimal source 20. "
            "Exact values require a checked infinite-path prefix. "
            "Use --no-value --info certificate to inspect availability."
        ),
    ),
    FamilyId.PRIME: FamilySpec(
        FamilyCapability("prime_index", ("start",), ("metrics",)),
        PrimeTermQuery,
        AdapterBinding("number_compiler.api.projections.prime", "project"),
        _observation(),
        term_observation=ObservationValueBinding(PrimeObservationOptions),
        output_bound="prime_upper",
    ),
    FamilyId.FERMAT: FamilySpec(
        FamilyCapability(
            "fermat_index",
            (),
            (
                "metrics",
                "number-theory.primality",
                "number-theory.factor",
                "number-theory.root",
            ),
        ),
        FermatTermQuery,
        AdapterBinding(
            "number_compiler.api.projections.power_numbers", "project_fermat"
        ),
        _observation("prepare_special", "admit_noop", "observe_special"),
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
        candidate_bound="dyadic",
        candidate_information=(
            ObservationId.NUMBER_THEORY_PRIMALITY,
            ObservationId.NUMBER_THEORY_FACTOR,
            ObservationId.NUMBER_THEORY_ROOT,
        ),
        output_bound="dyadic",
    ),
    FamilyId.MERSENNE: FamilySpec(
        FamilyCapability(
            "mersenne_exponent",
            (),
            (
                "metrics",
                "number-theory.primality",
                "number-theory.factor",
                "number-theory.root",
            ),
        ),
        MersenneTermQuery,
        AdapterBinding(
            "number_compiler.api.projections.power_numbers", "project_mersenne"
        ),
        _observation("prepare_special", "admit_noop", "observe_special"),
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
        candidate_bound="index",
        candidate_information=(
            ObservationId.NUMBER_THEORY_PRIMALITY,
            ObservationId.NUMBER_THEORY_FACTOR,
            ObservationId.NUMBER_THEORY_ROOT,
        ),
        output_bound="index",
    ),
}


def family_spec(family: str | FamilyId) -> FamilySpec:
    try:
        return CAPABILITIES[family_id(family)]
    except ValueError as exc:
        raise ValueError(f"unknown family: {family}") from exc


def family_listing() -> tuple[str, ...]:
    """Return the canonical `--list-families` lines from registered metadata."""
    lines: list[str] = []
    for family, spec in CAPABILITIES.items():
        lines.append(
            f"{family}: --nth N ({spec.unit}); info: {', '.join(spec.nth_info)}"
        )
        lines.append("  --nth-power10 K (exact index 10^K, K >= 0)")
        if spec.event_query_type is not None:
            lines.append(
                "  --events E (accelerated_odd_events); info: "
                + ", ".join(spec.event_info)
            )
        if spec.verify_flag is not None:
            lines.append(f"  --{spec.verify_flag.replace('_', '-')} PATH")
    return tuple(lines)


def presentation_options() -> dict[str, OptionSpec]:
    """Derive shared CLI presentation flags from their typed-record defaults."""
    result: dict[str, OptionSpec] = {}
    for field in fields(PresentationOptions):
        if field.name == "index":
            continue
        default = field.default
        kind = "boolean" if type(default) is bool else "integer"
        choices: tuple[str, ...] = ()
        if field.name == "format":
            kind = "choice"
            choices = tuple(value.value for value in OutputFormat)
        result[field.name] = OptionSpec(
            default,
            (),
            name=field.name,
            value_kind=kind,
            choices=choices,
        )
    max_index_bits = next(
        field for field in fields(QueryRequest) if field.name == "max_index_bits"
    )
    result["max_index_bits"] = OptionSpec(
        max_index_bits.default,
        (),
        name="max_index_bits",
    )
    return result


def resolve_projection_adapter(query: TermQuery) -> ProjectionAdapter:
    """Load only the projection code for the already-selected family query."""
    family = getattr(query, "family", None)
    spec = CAPABILITIES.get(family) if type(family) is FamilyId else None
    if spec is None or type(query) is not spec.query_type:
        raise TypeError("unsupported family query type")
    binding = spec.projection
    adapter = getattr(import_module(binding.module), binding.attribute)
    if not callable(adapter):
        raise TypeError("registered projection adapter is not callable")
    return cast(ProjectionAdapter, adapter)


@dataclass(frozen=True, slots=True)
class ResolvedObservationAdapter:
    prepare: PrepareObserver
    admit: AdmitObserver
    observe: ObserveObserver


def resolve_observation_adapter(
    family: str | FamilyId,
    identifier: ObservationId | None = None,
) -> ResolvedObservationAdapter:
    specification = family_spec(family)
    if identifier is None:
        binding = specification.observation
    else:
        selected = next(
            (
                item
                for item in specification.observation_specs
                if item.identifier is identifier
            ),
            None,
        )
        if selected is None or selected.adapter is None:
            raise ValueError(
                f"observation is not registered for {family}: {identifier}"
            )
        binding = selected.adapter
    module = import_module(binding.module)
    functions = tuple(
        getattr(module, name)
        for name in (binding.prepare, binding.admit, binding.observe)
    )
    if any(not callable(function) for function in functions):
        raise TypeError("registered observation adapter is not callable")
    return ResolvedObservationAdapter(
        cast(PrepareObserver, functions[0]),
        cast(AdmitObserver, functions[1]),
        cast(ObserveObserver, functions[2]),
    )


def resolve_verification_adapter(query: ExecutionQuery) -> VerificationAdapter:
    """Load the selected family's verifier for its exact typed query."""
    spec = family_spec(query.family)
    if spec.verify_query_type is None or type(query) is not spec.verify_query_type:
        raise TypeError("unsupported certificate verification query type")
    binding = spec.verification
    if binding is None:
        raise ValueError("family has no certificate verifier")
    verifier = getattr(import_module(binding.module), binding.attribute)
    if not callable(verifier):
        raise TypeError("registered certificate verifier is not callable")
    return cast(VerificationAdapter, verifier)


def option_argv(name: str, value: object) -> list[str]:
    """Render one canonical family/observer option for reproducible probes."""
    if name.startswith("--"):
        flag = name
    else:
        flag = "--" + name.replace("_", "-")
    if isinstance(value, bool):
        return [flag] if value else []
    return [flag, str(value)]


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
    "ResolvedObservationAdapter",
    "VerificationAdapter",
    "family_listing",
    "family_spec",
    "option_argv",
    "presentation_options",
    "resolve_observation_adapter",
    "resolve_projection_adapter",
    "resolve_verification_adapter",
]
