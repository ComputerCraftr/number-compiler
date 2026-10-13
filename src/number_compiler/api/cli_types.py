"""Typed command presentation and family-specific observation selections."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING, Literal, TypeAlias

from number_compiler.api.query_types import ExecutionQuery
from number_compiler.arithmetic.contracts.input_validation import require_integer

if TYPE_CHECKING:
    from number_compiler.api.output_schema import IndexValue


IndexEncoding: TypeAlias = Literal["integer", "power10"]
OutputFormat: TypeAlias = Literal["value", "symbolic", "json"]


def _validate_info_names(info: tuple[str, ...]) -> None:
    if type(info) is not tuple or any(type(name) is not str for name in info):
        raise TypeError("information names must be an immutable string tuple")


@dataclass(frozen=True, slots=True)
class IndexPresentation:
    """How an already-admitted exact index is displayed to the caller."""

    encoding: IndexEncoding = "integer"
    exponent: int | None = None

    def __post_init__(self) -> None:
        if self.encoding == "integer":
            if self.exponent is not None:
                raise ValueError("integer index presentation has no exponent")
        elif self.encoding == "power10":
            if type(self.exponent) is not int or self.exponent < 0:
                raise ValueError(
                    "power10 index presentation needs a nonnegative exponent"
                )
        else:
            raise ValueError("unsupported compact index encoding")

    def value(self, index: int) -> IndexValue:
        if self.encoding == "integer":
            return index
        if self.exponent is None:
            raise AssertionError("validated power10 presentation lost its exponent")
        return {"encoding": "power10", "exponent": self.exponent}


@dataclass(frozen=True, slots=True)
class PresentationOptions:
    index: IndexPresentation = IndexPresentation()
    format: OutputFormat = "value"
    output_base: int = 10
    max_output_bits: int = 1_000_000
    no_value: bool = False

    def __post_init__(self) -> None:
        if type(self.index) is not IndexPresentation:
            raise TypeError("index presentation must be an IndexPresentation")
        if type(self.format) is not str or self.format not in (
            "value",
            "symbolic",
            "json",
        ):
            raise ValueError("--format: unsupported output format")
        if type(self.output_base) is not int or not 2 <= self.output_base <= 36:
            raise ValueError("--output-base must be an integer from 2 through 36")
        if type(self.max_output_bits) is not int or self.max_output_bits < 1:
            raise ValueError("--max-output-bits must be a positive integer")
        if type(self.no_value) is not bool:
            raise TypeError("no_value must be a boolean")


@dataclass(frozen=True, slots=True)
class NoObservations:
    info: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        _validate_info_names(self.info)


@dataclass(frozen=True, slots=True)
class ReverseAddObservationOptions:
    info: tuple[Literal["metrics", "mirror", "boundary-macro"], ...] = ()
    width: int = 2
    max_digits: int = 4096

    def __post_init__(self) -> None:
        _validate_info_names(self.info)
        require_integer(self.max_digits, "--max-digits", 1)
        require_integer(self.width, "--width", 1)
        width_limit = self.max_digits if "mirror" in self.info else 256
        if self.width > width_limit:
            raise ValueError("mirror sheet exceeds digit budget or width limit")


@dataclass(frozen=True, slots=True)
class DoubleReverseObservationOptions:
    info: tuple[Literal["metrics"], ...] = ()

    def __post_init__(self) -> None:
        _validate_info_names(self.info)


@dataclass(frozen=True, slots=True)
class CollatzTermObservationOptions:
    info: tuple[
        Literal[
            "metrics", "clock", "accumulator", "boundary-macro", "innovation-borrow"
        ],
        ...,
    ] = ()
    modulus: int = 257
    max_events: int = 4096
    max_digits: int = 4096

    def __post_init__(self) -> None:
        _validate_info_names(self.info)
        modulus = require_integer(self.modulus, "--modulus", 2)
        if modulus.bit_length() > 4096:
            raise ValueError("coefficient modulus exceeds bit budget")
        require_integer(self.max_events, "--max-events", 0)
        require_integer(self.max_digits, "--max-digits", 1)
        if "innovation-borrow" in self.info and (
            type(self.modulus) is not int
            or not 3 <= self.modulus <= 4096
            or self.modulus % 2 == 0
        ):
            raise ValueError("innovation-borrow requires an odd modulus in [3, 4096]")
        if "clock" in self.info:
            require_integer(self.max_events, "--max-events", 0)
            require_integer(self.max_digits, "--max-digits", 1)


@dataclass(frozen=True, slots=True)
class CollatzEventObservationOptions:
    info: tuple[
        Literal[
            "clock",
            "modular",
            "twisted",
            "hasse",
            "hensel",
            "tropical",
            "factor",
            "safety",
        ],
        ...,
    ] = ()
    modulus: int = 257
    width: int = 2
    sign: int = -1
    precision: int = 8
    target: int = 0
    s_weight: int = 1
    z_weight: int = 1

    def __post_init__(self) -> None:
        _validate_info_names(self.info)
        modulus = require_integer(self.modulus, "--modulus", 1)
        if modulus.bit_length() > 4096:
            raise ValueError("coefficient modulus exceeds bit budget")
        require_integer(self.width, "--width", 1, 256)
        require_integer(self.precision, "--precision", 0, 4096)
        require_integer(self.sign, "--sign")
        if self.sign not in (-1, 1):
            raise ValueError("cylinder sign must be -1 or +1")
        require_integer(self.target, "--target")
        require_integer(self.s_weight, "--s-weight")
        require_integer(self.z_weight, "--z-weight")


@dataclass(frozen=True, slots=True)
class AntihydraObservationOptions:
    info: tuple[
        Literal[
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
        ],
        ...,
    ] = ()
    modulus: int = 257
    width: int = 2
    sign: int = -1
    precision: int = 8
    time_width: int = 2
    time_sign: int = 1
    max_observer_terms: int = 1_000_000

    def __post_init__(self) -> None:
        _validate_info_names(self.info)
        modulus = require_integer(self.modulus, "--modulus", 2)
        if modulus.bit_length() > 4096:
            raise ValueError("coefficient modulus exceeds bit budget")
        require_integer(self.width, "--width", 1, 256)
        require_integer(self.sign, "--sign")
        require_integer(self.precision, "--precision", 0, 4096)
        require_integer(self.time_width, "--time-width", 1, 256)
        require_integer(self.time_sign, "--time-sign")
        require_integer(self.max_observer_terms, "--max-observer-terms", 0)
        if self.sign not in (-1, 1) or self.time_sign not in (-1, 1):
            raise ValueError("cylinder signs must be -1 or +1")
        if {"hensel", "mahler"}.intersection(self.info) and self.precision == 0:
            raise ValueError("--precision must be positive for Hensel/Mahler observers")
        if "hasse" in self.info and self.width > 8:
            raise ValueError("Hasse order must be from 1 through 8")
        if "spacetime" in self.info:
            if self.width > 64 or self.time_width > 64:
                raise ValueError("spacetime widths must be from 1 through 64")
            require_integer(self.max_observer_terms, "--max-observer-terms", 1)
        if "factor" in self.info and pow(2, self.width, modulus) != self.sign % modulus:
            raise ValueError("factor target is incompatible with the tape cylinder")


@dataclass(frozen=True, slots=True)
class CommaObservationOptions:
    info: tuple[Literal["metrics", "clock", "tropical", "certificate"], ...] = ()

    def __post_init__(self) -> None:
        _validate_info_names(self.info)


@dataclass(frozen=True, slots=True)
class PrimeObservationOptions:
    info: tuple[Literal["metrics"], ...] = ()

    def __post_init__(self) -> None:
        _validate_info_names(self.info)


@dataclass(frozen=True, slots=True)
class SpecialObservationOptions:
    info: tuple[Literal["metrics", "primality", "factor", "root"], ...] = ()
    defect: int | None = None
    max_digits: int = 4096
    max_candidate_bits: int = 1_000_000
    max_factor_products: int = 4096

    def __post_init__(self) -> None:
        _validate_info_names(self.info)
        if self.defect is not None:
            require_integer(self.defect, "--defect", 0)
        require_integer(self.max_digits, "--max-digits", 1)
        require_integer(self.max_candidate_bits, "--max-candidate-bits", 1)
        require_integer(self.max_factor_products, "--max-factor-products", 1)


ObservationOptions: TypeAlias = (
    NoObservations
    | ReverseAddObservationOptions
    | DoubleReverseObservationOptions
    | CollatzTermObservationOptions
    | CollatzEventObservationOptions
    | AntihydraObservationOptions
    | CommaObservationOptions
    | PrimeObservationOptions
    | SpecialObservationOptions
)


@dataclass(frozen=True, slots=True)
class QueryRequest:
    """Typed execution, presentation, and explicitly demanded observations."""

    execution: ExecutionQuery
    presentation: PresentationOptions = PresentationOptions()
    observations: ObservationOptions = NoObservations()
    max_index_bits: int = 1_000_000

    def __post_init__(self) -> None:
        if type(self.presentation) is not PresentationOptions:
            raise TypeError("presentation must be PresentationOptions")
        if type(self.max_index_bits) is not int or self.max_index_bits < 1:
            raise ValueError("maximum index bits must be a positive integer")
        family = getattr(self.execution, "family", None)
        selector = getattr(self.execution, "selector", None)
        if type(family) is not str or type(selector) is not str:
            raise TypeError("execution must carry registered family and selector ids")
        from number_compiler.api.family_registry import family_spec

        spec = family_spec(family)
        expected_query = {
            "nth": spec.query_type,
            "events": spec.event_query_type,
            "verify": spec.verify_query_type,
        }.get(selector)
        if expected_query is None or type(self.execution) is not expected_query:
            raise TypeError("execution must match its registered exact query type")
        if type(self.index) is not int or self.index < 0:
            raise TypeError("execution index must be a nonnegative integer")
        if self.index.bit_length() > self.max_index_bits:
            raise ValueError("index exceeds --max-index-bits")
        if self.presentation.index.encoding == "power10" and not _matches_power10(
            self.index, self.presentation.index.exponent, self.max_index_bits
        ):
            raise ValueError(
                "--nth-power10 presentation does not match execution index"
            )
        if type(self.observations) is NoObservations:
            if self.observations.info:
                raise ValueError("no-observation options cannot name information")
        else:
            binding = (
                spec.event_observation
                if selector == "events"
                else spec.term_observation
            )
            if selector == "verify" or binding is None:
                raise ValueError("execution selector does not accept observations")
            if type(self.observations) is not binding.options_type:
                raise TypeError("observations must match the registered option type")
            if type(self.observations.info) is not tuple or any(
                type(name) is not str for name in self.observations.info
            ):
                raise TypeError("observation names must be an immutable string tuple")
            supported_info = spec.event_info if selector == "events" else spec.nth_info
            if set(self.observations.info) - set(supported_info):
                raise ValueError(
                    "requested information is unavailable for this selector"
                )
            spec.validate_observation_request(self.execution, self.observations)

    @property
    def family(self) -> str:
        return self.execution.family

    @property
    def selector(self) -> str:
        return self.execution.selector

    @property
    def index(self) -> int:
        return self.execution.index

    @property
    def index_unit(self) -> str:
        if self.selector == "events":
            return "accelerated_odd_events"
        if self.selector == "verify":
            return "certificate"
        from number_compiler.api.family_registry import CAPABILITIES

        return CAPABILITIES[self.family].unit

    @property
    def presentation_index(self) -> IndexValue:
        return self.presentation.index.value(self.index)

    @property
    def requires_bounded_observer(self) -> bool:
        from number_compiler.api.family_registry import family_spec

        return family_spec(self.family).requires_bounded_observer(
            self.selector, self.observations.info
        )


def _matches_power10(index: int, exponent: int | None, max_bits: int) -> bool:
    if type(exponent) is not int or exponent < 0 or 3 * exponent >= max_bits:
        return False
    value = 1
    factor = 10
    remaining = exponent
    while remaining:
        if remaining & 1:
            value *= factor
            if value.bit_length() > max_bits:
                return False
        remaining >>= 1
        if remaining:
            factor *= factor
            if factor.bit_length() > max_bits:
                return False
    return value == index


__all__ = [
    "AntihydraObservationOptions",
    "CollatzEventObservationOptions",
    "CollatzTermObservationOptions",
    "CommaObservationOptions",
    "DoubleReverseObservationOptions",
    "IndexPresentation",
    "NoObservations",
    "ObservationOptions",
    "OutputFormat",
    "PresentationOptions",
    "PrimeObservationOptions",
    "QueryRequest",
    "ReverseAddObservationOptions",
    "SpecialObservationOptions",
]
