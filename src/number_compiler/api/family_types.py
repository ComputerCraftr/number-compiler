"""Typed family capability and observation binding declarations."""

from __future__ import annotations

from collections.abc import Callable, Mapping
from dataclasses import MISSING, dataclass, fields, is_dataclass, replace
from enum import StrEnum
from typing import TYPE_CHECKING, Protocol, runtime_checkable

from number_compiler.api.cli_types import (
    AntihydraObservationOptions,
    CollatzEventObservationOptions,
    CollatzTermObservationOptions,
    CommaObservationOptions,
    DoubleReverseObservationOptions,
    NoObservations,
    ObservationOptions,
    PrimeObservationOptions,
    QueryRequest,
    ReverseAddObservationOptions,
    SpecialObservationOptions,
)
from number_compiler.api.matrix_contracts import MatrixCapability
from number_compiler.api.observation_types import (
    OBSERVATION_REGISTRY,
    IndexUnit,
    ObservationAdapterBinding,
    ObservationCategory,
    ObservationId,
    ObservationSpec,
    OptionSpec,
    OutputFormat,
    SelectorId,
    option_default,
)
from number_compiler.api.query_types import (
    AntihydraVerifyQuery,
    CollatzEventQuery,
    ExecutionQuery,
    QueryOptionError,
    TermQuery,
)

if TYPE_CHECKING:
    from number_compiler.api.cli_context import QueryContext
    from number_compiler.api.number_api import NumberCompiler, ProjectedNumberTerm
    from number_compiler.api.output_schema import JsonValue, VerificationResult


_OBSERVATION_OPTION_TYPES = (
    NoObservations,
    ReverseAddObservationOptions,
    DoubleReverseObservationOptions,
    CollatzTermObservationOptions,
    CollatzEventObservationOptions,
    AntihydraObservationOptions,
    CommaObservationOptions,
    PrimeObservationOptions,
    SpecialObservationOptions,
)


@runtime_checkable
class ProjectionAdapter(Protocol):
    def __call__(
        self, compiler: NumberCompiler, query: TermQuery
    ) -> ProjectedNumberTerm: ...


@dataclass(frozen=True, slots=True)
class FamilyCapability:
    unit: IndexUnit
    parameters: tuple[str, ...]
    nth_info: tuple[ObservationId, ...]
    event_info: tuple[ObservationId, ...] = ()
    event_unit: IndexUnit | None = None

    def __post_init__(self) -> None:
        if type(self.unit) is not IndexUnit:
            raise TypeError("family index unit must be declared by IndexUnit")
        if type(self.parameters) is not tuple or any(
            type(parameter) is not str for parameter in self.parameters
        ):
            raise TypeError("family parameters must be a tuple of names")
        if type(self.nth_info) is not tuple or any(
            type(identifier) is not ObservationId for identifier in self.nth_info
        ):
            raise TypeError("term observations must be declared ObservationIds")
        if type(self.event_info) is not tuple or any(
            type(identifier) is not ObservationId for identifier in self.event_info
        ):
            raise TypeError("event observations must be declared ObservationIds")
        if self.event_unit is not None and type(self.event_unit) is not IndexUnit:
            raise TypeError("event index unit must be declared by IndexUnit")
        term_ids = self.nth_info
        if (
            ObservationId.TEMPORAL_MATRIX in term_ids
            and ObservationId.TEMPORAL_MATRIX_TRACE not in term_ids
        ):
            term_ids += (ObservationId.TEMPORAL_MATRIX_TRACE,)
        if (
            any(
                OBSERVATION_REGISTRY[item].category is ObservationCategory.TEMPORAL
                for item in term_ids
            )
            and ObservationId.TEMPORAL not in term_ids
        ):
            term_ids = (ObservationId.TEMPORAL, *term_ids)
        event_ids = self.event_info
        if (
            any(
                OBSERVATION_REGISTRY[item].category is ObservationCategory.TEMPORAL
                for item in event_ids
            )
            and ObservationId.TEMPORAL not in event_ids
        ):
            event_ids = (ObservationId.TEMPORAL, *event_ids)
        if self.event_unit is not None and not event_ids:
            raise ValueError("an event coordinate unit requires event observations")
        object.__setattr__(self, "nth_info", term_ids)
        object.__setattr__(self, "event_info", event_ids)


@dataclass(frozen=True, slots=True)
class AdapterBinding:
    module: str
    attribute: str

    def __post_init__(self) -> None:
        if type(self.module) is not str or not self.module:
            raise TypeError("adapter module must be a nonempty module path")
        if type(self.attribute) is not str or not self.attribute:
            raise TypeError("adapter attribute must be a nonempty name")


@dataclass(frozen=True, slots=True)
class ObservationValueBinding:
    options_type: Callable[..., ObservationOptions]
    fields: tuple[str, ...] = ()


class SizeBound(StrEnum):
    DYADIC = "dyadic"
    INDEX = "index"
    SEED = "seed"
    COLLATZ_SEED_AT_ZERO = "collatz_seed_at_zero"
    PRIME_UPPER = "prime_upper"


@runtime_checkable
class VerificationAdapter(Protocol):
    def __call__(self, query: ExecutionQuery) -> VerificationResult: ...


@dataclass(frozen=True, slots=True)
class FamilySpec:
    capability: FamilyCapability
    query_type: type[TermQuery]
    projection: AdapterBinding
    observation: ObservationAdapterBinding
    event_query_type: type[CollatzEventQuery] | None = None
    event_coordinate: str = "events"
    verify_query_type: type[AntihydraVerifyQuery] | None = None
    verify_coordinate: str = "certificate"
    verify_flag: str | None = None
    verification: AdapterBinding | None = None
    description: str | None = None
    term_observation: ObservationValueBinding | None = None
    event_observation: ObservationValueBinding | None = None
    observer_options: tuple[tuple[str, OptionSpec], ...] = ()
    bounded_observations: tuple[ObservationId, ...] = ()
    information_minima: tuple[tuple[int, tuple[ObservationId, ...], str], ...] = ()
    observation_constraints: tuple[tuple[ObservationId, str, int, str], ...] = ()
    selector_restrictions: tuple[tuple[SelectorId, tuple[str, ...], str], ...] = ()
    clock_budget: tuple[ObservationId, str, str, str] | None = None
    candidate_bound: SizeBound | None = None
    candidate_information: tuple[ObservationId, ...] = ()
    output_bound: SizeBound | None = None
    matrix: MatrixCapability | None = None

    def __post_init__(self) -> None:
        if type(self.capability) is not FamilyCapability:
            raise TypeError("family specification requires a FamilyCapability")
        if type(self.query_type) is not type or not is_dataclass(self.query_type):
            raise TypeError("family specification requires a typed term query")
        if (
            type(self.projection) is not AdapterBinding
            or type(self.observation) is not ObservationAdapterBinding
        ):
            raise TypeError("family specification requires typed adapter bindings")
        if (
            self.event_query_type is not None
            and self.event_query_type is not CollatzEventQuery
        ):
            raise TypeError("event queries must use the registered event query type")
        if (
            self.verify_query_type is not None
            and self.verify_query_type is not AntihydraVerifyQuery
        ):
            raise TypeError("certificate queries must use the registered verifier type")
        if (
            self.candidate_bound is not None
            and type(self.candidate_bound) is not SizeBound
        ):
            raise TypeError("candidate size bound must be a SizeBound")
        if self.output_bound is not None and type(self.output_bound) is not SizeBound:
            raise TypeError("output size bound must be a SizeBound")
        for identifiers in (self.bounded_observations, self.candidate_information):
            if type(identifiers) is not tuple or any(
                type(identifier) is not ObservationId for identifier in identifiers
            ):
                raise TypeError("family observations must be declared ObservationIds")
        constraints: list[tuple[ObservationId, str, int, str]] = []
        for identifier, field_name, value, message in self.observation_constraints:
            if type(identifier) is not ObservationId:
                raise TypeError("observation constraint requires an ObservationId")
            constraints.append((identifier, field_name, value, message))
            if identifier is ObservationId.TEMPORAL_MATRIX:
                constraints.append(
                    (ObservationId.TEMPORAL_MATRIX_TRACE, field_name, value, message)
                )
        object.__setattr__(
            self, "observation_constraints", tuple(dict.fromkeys(constraints))
        )
        if any(
            type(selector) is not SelectorId
            for selector, _, _ in self.selector_restrictions
        ):
            raise TypeError("selector restrictions require SelectorIds")
        if self.clock_budget is not None:
            identifier = self.clock_budget[0]
            if type(identifier) is not ObservationId:
                raise TypeError("clock budget requires an ObservationId")

    @property
    def observation_specs(self) -> tuple[ObservationSpec, ...]:
        """Family-supported observations with selector scope and category."""
        selectors_by_id: dict[ObservationId, list[SelectorId]] = {}
        for selector, identifiers in (
            (SelectorId.NTH, self.nth_info),
            (SelectorId.EVENTS, self.event_info),
        ):
            for identifier in identifiers:
                selectors_by_id.setdefault(identifier, []).append(selector)
        return tuple(
            ObservationSpec(
                identifier,
                OBSERVATION_REGISTRY[identifier].category,
                tuple(selectors),
                selector_units=tuple(
                    (selector, unit)
                    for selector in selectors
                    if OBSERVATION_REGISTRY[identifier].category
                    is ObservationCategory.TEMPORAL
                    for unit in (
                        self.unit if selector is SelectorId.NTH else self.event_unit,
                    )
                    if unit is not None
                ),
                options=tuple(
                    option
                    for option in self.observer_options_map().values()
                    if identifier in option.information
                ),
                adapter=self.observation,
            )
            for identifier, selectors in selectors_by_id.items()
        )

    @property
    def unit(self) -> IndexUnit:
        return self.capability.unit

    @property
    def event_unit(self) -> IndexUnit | None:
        return self.capability.event_unit

    def unit_for(self, selector: SelectorId) -> IndexUnit | None:
        if selector is SelectorId.NTH:
            return self.unit
        if selector is SelectorId.EVENTS:
            return self.event_unit
        return IndexUnit.CERTIFICATE if selector is SelectorId.VERIFY else None

    @property
    def parameters(self) -> tuple[str, ...]:
        return self.capability.parameters

    @property
    def nth_info(self) -> tuple[ObservationId, ...]:
        return self.capability.nth_info

    @property
    def event_info(self) -> tuple[ObservationId, ...]:
        return self.capability.event_info

    def observer_options_map(self) -> dict[str, OptionSpec]:
        available = set(self.nth_info + self.event_info)
        options = self.observer_options + (
            () if self.matrix is None else self.matrix.options()
        )
        return {
            name: replace(option, information=supported, name=name)
            for name, option in options
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
                default = (
                    None if field.default is MISSING else option_default(field.default)
                )
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
        observer_specs: dict[str, OptionSpec] = {
            option.name: option
            for observation in self.observation_specs
            for option in observation.options
        }
        observer_specs.update(
            {
                name: observer
                for name, observer in self.observer_options_map().items()
                if not observer.information
            }
        )
        for name, observer in observer_specs.items():
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
                    observer.flag_name,
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
                    observer.flag_name or current.flag_name,
                )
        return result

    def build_term_query(self, index: int, values: Mapping[str, object]) -> TermQuery:
        query = self._build_query(
            self.query_type, self.query_type, index, values, "index"
        )
        if not isinstance(query, TermQuery) or type(query) is not self.query_type:
            raise TypeError("family query factory returned a different query type")
        return query

    def build_event_query(
        self, coordinate: int, values: Mapping[str, object]
    ) -> ExecutionQuery:
        if self.event_query_type is None:
            raise ValueError("family does not support event queries")
        query = self._build_query(
            self.event_query_type,
            self.event_query_type,
            coordinate,
            values,
            self.event_coordinate,
        )
        if (
            not isinstance(query, CollatzEventQuery)
            or type(query) is not self.event_query_type
        ):
            raise TypeError("event query factory returned a different query type")
        return query

    def build_verify_query(self, certificate: str) -> ExecutionQuery:
        if self.verify_query_type is None:
            raise ValueError("family does not support certificate verification")
        query = self.verify_query_type(**{self.verify_coordinate: certificate})
        if type(query) is not self.verify_query_type:
            raise TypeError("verification query factory returned a different type")
        return query

    def build_observations(
        self,
        selector: SelectorId,
        information: tuple[ObservationId, ...],
        values: Mapping[str, object],
    ) -> ObservationOptions:
        if not information:
            return NoObservations()
        binding = (
            self.event_observation
            if selector is SelectorId.EVENTS
            else self.term_observation
        )
        if binding is None:
            raise ValueError("family selector has no observation option record")
        if any(type(name) is not ObservationId for name in information):
            raise TypeError("observation selections must be declared ObservationIds")
        options = binding.options_type(
            info=information,
            **{name: values[name] for name in binding.fields},
        )
        if type(options) not in _OBSERVATION_OPTION_TYPES:
            raise TypeError("observation factory returned an unsupported options type")
        return options

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
        if request.selector is SelectorId.VERIFY:
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
            if request.presentation.format is OutputFormat.SYMBOLIC:
                raise ValueError("certificate verification has no symbolic value")
            if self.verification is None:
                raise ValueError("family has no certificate verifier")
            return
        info = set(request.observations.info)
        for minimum, information, error in self.information_minima:
            if request.index < minimum and info.intersection(information):
                selector_flag = (
                    "--events"
                    if request.selector is SelectorId.EVENTS
                    else "--nth-power10"
                    if "nth_power10" in specified
                    else "--nth"
                )
                raise ValueError(f"{selector_flag}: {error}")
        for selector, option_names, message in self.selector_restrictions:
            if request.selector is selector and set(option_names).intersection(
                specified
            ):
                raise ValueError(message)
        if (
            request.presentation.no_value or request.selector is SelectorId.EVENTS
        ) and not info:
            raise ValueError("information-only queries require --info")
        if request.presentation.format is OutputFormat.SYMBOLIC and (
            request.presentation.no_value or request.selector is SelectorId.EVENTS
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
        self, field_name: str, selector: SelectorId, specified: frozenset[str]
    ) -> str | None:
        if field_name == "certificate" and self.verify_flag is not None:
            return "--" + self.verify_flag.replace("_", "-")
        if field_name == "index":
            if selector is SelectorId.EVENTS:
                return "--events"
            return "--nth-power10" if "nth_power10" in specified else "--nth"
        if field_name == self.event_coordinate and selector is SelectorId.EVENTS:
            return "--events"
        option = self.parser_options().get(field_name)
        return None if option is None else option.flag

    def _validate_clock_budget(self, request: QueryRequest) -> None:
        if self.clock_budget is None:
            return
        information, limit_option, source_field, digit_option = self.clock_budget
        if (
            information not in request.observations.info
            or request.selector is not SelectorId.NTH
        ):
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
            or request.selector is not SelectorId.NTH
            or presentation.format is OutputFormat.SYMBOLIC
        ):
            return
        if self._size_exceeds(
            request.execution, self.output_bound, presentation.max_output_bits
        ):
            raise ValueError(
                f"output exceeds --max-output-bits ({presentation.max_output_bits})"
            )

    @staticmethod
    def _size_exceeds(query: ExecutionQuery, rule: SizeBound, limit: int) -> bool:
        if rule is SizeBound.DYADIC:
            from number_compiler.arithmetic.fields.symbolic_extent import DyadicExtent

            return DyadicExtent(query.index, 1) > limit
        if rule is SizeBound.INDEX:
            return query.index > limit
        if rule is SizeBound.SEED:
            return FamilySpec._integer_field(query, "seed").bit_length() > limit
        if rule is SizeBound.COLLATZ_SEED_AT_ZERO:
            return (
                FamilySpec._integer_field(query, "seed").bit_length()
                if query.index == 0
                else 0
            ) > limit
        if rule is SizeBound.PRIME_UPPER:
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
        query_type: type[ExecutionQuery],
        factory: Callable[..., ExecutionQuery],
        coordinate: int,
        values: Mapping[str, object],
        key: str,
    ) -> ExecutionQuery:
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
        return factory(**{key: coordinate}, **arguments)

    def requires_bounded_observer(
        self, selector: SelectorId, info: tuple[ObservationId, ...]
    ) -> bool:
        return selector is SelectorId.NTH and bool(
            set(info).intersection(self.bounded_observations)
        )


class ObservationAdapter(Protocol):
    def prepare(self, context: QueryContext, term: ProjectedNumberTerm) -> None: ...

    def admit(self, context: QueryContext) -> None: ...

    def observe(
        self, context: QueryContext, name: ObservationId
    ) -> dict[str, JsonValue]: ...


@runtime_checkable
class PrepareObserver(Protocol):
    def __call__(self, context: QueryContext, term: ProjectedNumberTerm) -> None: ...


@runtime_checkable
class AdmitObserver(Protocol):
    def __call__(self, context: QueryContext) -> None: ...


@runtime_checkable
class ObserveObserver(Protocol):
    def __call__(
        self, context: QueryContext, name: ObservationId
    ) -> dict[str, JsonValue]: ...


__all__ = [
    "AdapterBinding",
    "AdmitObserver",
    "FamilyCapability",
    "FamilySpec",
    "ObservationAdapter",
    "ObservationAdapterBinding",
    "ObservationValueBinding",
    "OptionSpec",
    "PrepareObserver",
    "ProjectionAdapter",
    "SizeBound",
    "VerificationAdapter",
]
