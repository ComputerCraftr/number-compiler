"""Canonical family capabilities and lazy execution/observation bindings."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import MISSING, dataclass, fields
from importlib import import_module
from typing import TYPE_CHECKING, Any, Protocol, cast, get_args

from number_compiler.api.cli_types import (
    AntihydraObservationOptions,
    CollatzEventObservationOptions,
    CollatzTermObservationOptions,
    CommaObservationOptions,
    DoubleReverseObservationOptions,
    NoObservations,
    ObservationOptions,
    OutputFormat,
    PresentationOptions,
    PrimeObservationOptions,
    QueryRequest,
    ReverseAddObservationOptions,
    SpecialObservationOptions,
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
    QueryOptionError,
    ReverseAddTermQuery,
    TermQuery,
)

if TYPE_CHECKING:
    from number_compiler.api.cli_context import QueryContext
    from number_compiler.api.number_api import NumberCompiler, ProjectedNumberTerm
    from number_compiler.api.output_schema import JsonValue, VerificationResult


class ProjectionAdapter(Protocol):
    def __call__(
        self, compiler: NumberCompiler, query: TermQuery
    ) -> ProjectedNumberTerm: ...


@dataclass(frozen=True, slots=True)
class FamilyCapability:
    unit: str
    parameters: tuple[str, ...]
    nth_info: tuple[str, ...]
    event_info: tuple[str, ...] = ()


@dataclass(frozen=True, slots=True)
class OptionSpec:
    """One CLI option default and the information packets that consume it."""

    default: object | None
    information: tuple[str, ...]
    required: bool = False
    name: str = ""
    value_kind: str = "integer"
    help: str = ""
    choices: tuple[str, ...] = ()

    @property
    def flag(self) -> str:
        return "--" + self.name.replace("_", "-")


@dataclass(frozen=True, slots=True)
class AdapterBinding:
    module: str
    attribute: str


@dataclass(frozen=True, slots=True)
class ObservationAdapterBinding:
    module: str
    prepare: str
    admit: str
    observe: str


@dataclass(frozen=True, slots=True)
class ObservationValueBinding:
    options_type: type[Any]
    fields: tuple[str, ...] = ()


class VerificationAdapter(Protocol):
    def __call__(self, query: ExecutionQuery) -> VerificationResult: ...


@dataclass(frozen=True, slots=True)
class FamilySpec:
    capability: FamilyCapability
    query_type: type[TermQuery]
    projection: AdapterBinding
    observation: ObservationAdapterBinding
    event_query_type: type[Any] | None = None
    event_coordinate: str = "events"
    verify_query_type: type[Any] | None = None
    verify_coordinate: str = "certificate"
    verify_flag: str | None = None
    verification: AdapterBinding | None = None
    description: str | None = None
    term_observation: ObservationValueBinding | None = None
    event_observation: ObservationValueBinding | None = None
    observer_options: tuple[tuple[str, OptionSpec], ...] = ()
    bounded_observations: tuple[str, ...] = ()
    information_minima: tuple[tuple[int, tuple[str, ...], str], ...] = ()
    observation_constraints: tuple[tuple[str, str, int, str], ...] = ()
    selector_restrictions: tuple[tuple[str, tuple[str, ...], str], ...] = ()
    clock_budget: tuple[str, str, str, str] | None = None
    candidate_bound: str | None = None
    candidate_information: tuple[str, ...] = ()
    output_bound: str | None = None

    @property
    def unit(self) -> str:
        return self.capability.unit

    @property
    def parameters(self) -> tuple[str, ...]:
        return self.capability.parameters

    @property
    def nth_info(self) -> tuple[str, ...]:
        return self.capability.nth_info

    @property
    def event_info(self) -> tuple[str, ...]:
        return self.capability.event_info

    def observer_options_map(self) -> dict[str, OptionSpec]:
        available = set(self.nth_info + self.event_info)
        return {
            name: OptionSpec(
                option.default,
                supported,
                option.required,
                name,
                option.value_kind,
                option.help,
                option.choices,
            )
            for name, option in self.observer_options
            if (
                supported := tuple(
                    info for info in option.information if info in available
                )
            )
            or not option.information
        }

    def query_options(self) -> dict[str, OptionSpec]:
        result: dict[str, OptionSpec] = {}
        for query_type in (self.query_type, self.event_query_type):
            if query_type is None:
                continue
            for field in fields(query_type):
                if field.name in {
                    "index",
                    self.event_coordinate,
                    self.verify_coordinate,
                }:
                    continue
                default = None if field.default is MISSING else field.default
                result[field.name] = OptionSpec(
                    default,
                    (),
                    field.default is MISSING,
                    field.name,
                    help=f"{field.name.replace('_', ' ')} for {self.capability.unit}",
                )
        return result

    def parser_options(self) -> dict[str, OptionSpec]:
        result = self.query_options()
        for name, observer in self.observer_options_map().items():
            current = result.get(name)
            if current is None:
                result[name] = OptionSpec(
                    observer.default,
                    observer.information,
                    observer.required,
                    name,
                    observer.value_kind,
                    observer.help
                    or f"used by --info {', '.join(observer.information)}",
                    observer.choices,
                )
            else:
                result[name] = OptionSpec(
                    current.default if observer.default is None else observer.default,
                    observer.information,
                    current.required or observer.required,
                    name,
                    observer.value_kind,
                    observer.help or current.help,
                    observer.choices or current.choices,
                )
        return result

    def build_term_query(self, index: int, values: Mapping[str, object]) -> TermQuery:
        return cast(
            TermQuery, self._build_query(self.query_type, index, values, "index")
        )

    def build_event_query(
        self, coordinate: int, values: Mapping[str, object]
    ) -> ExecutionQuery:
        if self.event_query_type is None:
            raise ValueError("family does not support event queries")
        return cast(
            ExecutionQuery,
            self._build_query(
                self.event_query_type, coordinate, values, self.event_coordinate
            ),
        )

    def build_verify_query(self, certificate: str) -> ExecutionQuery:
        if self.verify_query_type is None:
            raise ValueError("family does not support certificate verification")
        return cast(
            ExecutionQuery,
            self.verify_query_type(**{self.verify_coordinate: certificate}),
        )

    def build_observations(
        self, selector: str, information: tuple[str, ...], values: Mapping[str, object]
    ) -> ObservationOptions:
        if not information:
            return NoObservations()
        binding = (
            self.event_observation if selector == "events" else self.term_observation
        )
        if binding is None:
            raise ValueError("family selector has no observation option record")
        return cast(
            ObservationOptions,
            binding.options_type(
                information, *(values[name] for name in binding.fields)
            ),
        )

    def validate_observation_request(
        self, execution: ExecutionQuery, observations: ObservationOptions
    ) -> None:
        for (
            information,
            field_name,
            required_value,
            error,
        ) in self.observation_constraints:
            if (
                information in observations.info
                and getattr(execution, field_name) != required_value
            ):
                raise QueryOptionError(field_name, error)

    def validate_request(
        self, request: QueryRequest, specified: frozenset[str]
    ) -> None:
        if request.selector == "verify":
            allowed = {self.verify_flag, "format"}
            if (
                self.verify_flag is None
                or request.observations.info
                or request.presentation.no_value
                or specified - allowed
            ):
                raise ValueError(
                    "certificate verification cannot be combined with term options"
                )
            if request.presentation.format == "symbolic":
                raise ValueError("certificate verification has no symbolic value")
            if self.verification is None:
                raise ValueError("family has no certificate verifier")
            return
        info = set(request.observations.info)
        for minimum, information, error in self.information_minima:
            if request.index < minimum and info.intersection(information):
                selector_flag = (
                    "--events"
                    if request.selector == "events"
                    else "--nth-power10"
                    if "nth_power10" in specified
                    else "--nth"
                )
                raise ValueError(f"{selector_flag}: {error}")
        for selector, option_names, message in self.selector_restrictions:
            if request.selector == selector and set(option_names).intersection(
                specified
            ):
                raise ValueError(message)
        if (request.presentation.no_value or request.selector == "events") and not info:
            raise ValueError("information-only queries require --info")
        if request.presentation.format == "symbolic" and (
            request.presentation.no_value or request.selector == "events"
        ):
            raise ValueError("symbolic output requires a term value")
        for name, option in self.observer_options_map().items():
            if (
                name in specified
                and option.information
                and not info.intersection(option.information)
            ):
                raise ValueError(
                    f"--{name.replace('_', '-')} ({name}) requires its matching --info"
                )
        self._validate_clock_budget(request)
        self._validate_candidate_budget(request)
        self._validate_output_limit(request)

    def option_flag(
        self, field_name: str, selector: str, specified: frozenset[str]
    ) -> str | None:
        if field_name == "certificate" and self.verify_flag is not None:
            return "--" + self.verify_flag.replace("_", "-")
        if field_name == "index":
            if selector == "events":
                return "--events"
            return "--nth-power10" if "nth_power10" in specified else "--nth"
        if field_name == self.event_coordinate and selector == "events":
            return "--events"
        option = self.parser_options().get(field_name)
        return None if option is None else option.flag

    def _validate_clock_budget(self, request: QueryRequest) -> None:
        if self.clock_budget is None:
            return
        information, limit_option, source_field, digit_option = self.clock_budget
        if information not in request.observations.info or request.selector != "nth":
            return
        limit = self._integer_field(request.observations, limit_option)
        source = self._integer_field(request.execution, source_field)
        digits = self._integer_field(request.observations, digit_option)
        if request.index > limit or source.bit_length() > digits:
            raise ValueError("physical clock observation budget exceeded")

    def _validate_candidate_budget(self, request: QueryRequest) -> None:
        if self.candidate_bound is None or not set(
            request.observations.info
        ).intersection(self.candidate_information):
            return
        options = request.observations
        if not isinstance(options, SpecialObservationOptions):
            return
        if self._size_exceeds(
            request.execution, self.candidate_bound, options.max_candidate_bits
        ):
            raise ValueError(
                "--max-candidate-bits (max_candidate_bits) is smaller than the special candidate"
            )

    def _validate_output_limit(self, request: QueryRequest) -> None:
        presentation = request.presentation
        if (
            self.output_bound is None
            or presentation.no_value
            or request.selector != "nth"
            or presentation.format == "symbolic"
        ):
            return
        if self._size_exceeds(
            request.execution, self.output_bound, presentation.max_output_bits
        ):
            raise ValueError(
                f"output exceeds --max-output-bits ({presentation.max_output_bits})"
            )

    @staticmethod
    def _size_exceeds(query: ExecutionQuery, rule: str, limit: int) -> bool:
        if rule == "dyadic":
            from number_compiler.arithmetic.fields.symbolic_extent import DyadicExtent

            return DyadicExtent(query.index, 1) > limit
        if rule == "index":
            return query.index > limit
        if rule == "seed":
            return FamilySpec._integer_field(query, "seed").bit_length() > limit
        if rule == "collatz_seed_at_zero":
            return (
                FamilySpec._integer_field(query, "seed").bit_length()
                if query.index == 0
                else 0
            ) > limit
        if rule == "prime_upper":
            start = max(2, FamilySpec._integer_field(query, "start"))
            return (start + query.index).bit_length() > limit
        raise ValueError(f"unknown size-bound rule {rule!r}")

    @staticmethod
    def _integer_field(record: object, name: str) -> int:
        value = getattr(record, name, None)
        if type(value) is not int:
            raise TypeError(f"registered record lacks integer field {name!r}")
        return value

    @staticmethod
    def _build_query(
        query_type: type[Any], coordinate: int, values: Mapping[str, object], key: str
    ) -> Any:
        query_fields = {field.name: field for field in fields(query_type)}
        names = set(query_fields) - {key}
        for name in names:
            field = query_fields[name]
            if field.default is MISSING and values.get(name) is None:
                family = getattr(query_type, "family", "family")
                raise QueryOptionError(
                    name, f"{family} requires --{name.replace('_', '-')}"
                )
        arguments = {name: values[name] for name in names if name in values}
        return query_type(**{key: coordinate}, **arguments)

    def requires_bounded_observer(self, selector: str, info: tuple[str, ...]) -> bool:
        return selector == "nth" and bool(
            set(info).intersection(self.bounded_observations)
        )


class ObservationAdapter(Protocol):
    def prepare(self, context: QueryContext, term: ProjectedNumberTerm) -> None: ...

    def admit(self, context: QueryContext) -> None: ...

    def observe(self, context: QueryContext, name: str) -> dict[str, JsonValue]: ...


class PrepareObserver(Protocol):
    def __call__(self, context: QueryContext, term: ProjectedNumberTerm) -> None: ...


class AdmitObserver(Protocol):
    def __call__(self, context: QueryContext) -> None: ...


class ObserveObserver(Protocol):
    def __call__(self, context: QueryContext, name: str) -> dict[str, JsonValue]: ...


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
    "defect": OptionSpec(None, ("root",)),
    "modulus": OptionSpec(
        257,
        (
            "modular",
            "twisted",
            "tape",
            "spacetime",
            "hasse",
            "factor",
            "accumulator",
            "innovation-borrow",
        ),
    ),
    "width": OptionSpec(
        2, ("mirror", "twisted", "tape", "spacetime", "hasse", "factor")
    ),
    "sign": OptionSpec(-1, ("twisted", "tape", "spacetime", "factor")),
    "precision": OptionSpec(8, ("hensel", "mahler")),
    "target": OptionSpec(0, ("hensel",)),
    "s_weight": OptionSpec(1, ("tropical",)),
    "z_weight": OptionSpec(1, ("tropical",)),
    "time_width": OptionSpec(2, ("spacetime",)),
    "time_sign": OptionSpec(1, ("spacetime",)),
}


def _opts(*names: str) -> tuple[tuple[str, OptionSpec], ...]:
    return tuple((name, _COMMON_OBSERVER_OPTIONS[name]) for name in names)


CAPABILITIES: dict[str, FamilySpec] = {
    "reverse-add": FamilySpec(
        FamilyCapability(
            "iterations", ("seed", "base"), ("metrics", "mirror", "boundary-macro")
        ),
        ReverseAddTermQuery,
        AdapterBinding("number_compiler.api.projections.reverse_add", "project"),
        _observation("prepare_reverse", "admit_reverse", "observe_reverse"),
        term_observation=ObservationValueBinding(
            ReverseAddObservationOptions, ("width", "max_digits")
        ),
        observer_options=_opts("width")
        + (("max_digits", OptionSpec(4096, ("mirror",))),),
        bounded_observations=("mirror",),
        output_bound="seed",
        observation_constraints=(
            (
                "boundary-macro",
                "base",
                10,
                "boundary-macro observation requires decimal base",
            ),
        ),
    ),
    "2rev10": FamilySpec(
        FamilyCapability("iterations", ("seed",), ("metrics", "closed-form")),
        DoubleReverseTermQuery,
        AdapterBinding("number_compiler.api.projections.double_reverse", "project"),
        _observation(observe="observe_double_reverse"),
        term_observation=ObservationValueBinding(
            DoubleReverseObservationOptions, ("modulus",)
        ),
        observer_options=(("modulus", OptionSpec(None, ("closed-form",))),),
        output_bound="seed",
    ),
    "collatz": FamilySpec(
        FamilyCapability(
            "physical_iterations",
            ("seed", "radix"),
            ("metrics", "clock", "accumulator", "boundary-macro", "innovation-borrow"),
            (
                "clock",
                "modular",
                "twisted",
                "hasse",
                "hensel",
                "tropical",
                "factor",
                "safety",
            ),
        ),
        CollatzTermQuery,
        AdapterBinding("number_compiler.api.projections.collatz", "project"),
        _observation("prepare_collatz", "admit_collatz", "observe_collatz"),
        event_query_type=CollatzEventQuery,
        term_observation=ObservationValueBinding(
            CollatzTermObservationOptions, ("modulus", "max_events", "max_digits")
        ),
        event_observation=ObservationValueBinding(
            CollatzEventObservationOptions,
            ("modulus", "width", "sign", "precision", "target", "s_weight", "z_weight"),
        ),
        observer_options=_opts("modulus", "precision", "target", "s_weight", "z_weight")
        + (
            ("width", OptionSpec(2, ("twisted", "hasse"))),
            ("sign", OptionSpec(-1, ("twisted",))),
        )
        + (
            ("max_events", OptionSpec(None, ("clock",))),
            ("max_digits", OptionSpec(None, ("clock",))),
        ),
        bounded_observations=("clock",),
        clock_budget=("clock", "max_events", "seed", "max_digits"),
        selector_restrictions=(
            (
                "events",
                ("output_base", "max_output_bits"),
                "event observations have no term output to format or limit",
            ),
            (
                "events",
                ("radix",),
                "--radix applies to Collatz --nth terms, not --events",
            ),
        ),
        output_bound="collatz_seed_at_zero",
    ),
    "antihydra": FamilySpec(
        FamilyCapability(
            "macro_returns_after_startup",
            (),
            (
                "metrics",
                "ledger",
                "clock",
                "modular",
                "tape",
                "twisted",
                "spacetime",
                "hasse",
                "hensel",
                "mahler",
                "tropical",
                "factor",
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
        + (("max_observer_terms", OptionSpec(1_000_000, ("spacetime",))),),
    ),
    "a367620": FamilySpec(
        FamilyCapability(
            "oeis_index", (), ("metrics", "clock", "tropical", "certificate")
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
    "prime": FamilySpec(
        FamilyCapability("prime_index", ("start",), ("metrics",)),
        PrimeTermQuery,
        AdapterBinding("number_compiler.api.projections.prime", "project"),
        _observation(),
        term_observation=ObservationValueBinding(PrimeObservationOptions),
        output_bound="prime_upper",
    ),
    "fermat": FamilySpec(
        FamilyCapability(
            "fermat_index", (), ("metrics", "primality", "factor", "root")
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
        candidate_information=("primality", "factor", "root"),
        output_bound="dyadic",
    ),
    "mersenne": FamilySpec(
        FamilyCapability(
            "mersenne_exponent", (), ("metrics", "primality", "factor", "root")
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
                ("primality", "factor", "root"),
                "special theorem parameter must be at least 2",
            ),
        ),
        candidate_bound="index",
        candidate_information=("primality", "factor", "root"),
        output_bound="index",
    ),
}


def family_spec(family: str) -> FamilySpec:
    try:
        return CAPABILITIES[family]
    except KeyError as exc:
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
            choices = tuple(get_args(OutputFormat))
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
    spec = CAPABILITIES.get(family) if type(family) is str else None
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


def resolve_observation_adapter(family: str) -> ResolvedObservationAdapter:
    binding = family_spec(family).observation
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
    "FamilyCapability",
    "FamilySpec",
    "ObservationAdapter",
    "OptionSpec",
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
