"""Typed command presentation and family-specific observation selections."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING, TypeAlias

from number_compiler.api.matrix_contracts import MatrixRequest
from number_compiler.api.observation_types import (
    IndexEncoding,
    IndexUnit,
    ObservationId,
    OutputFormat,
    SelectorId,
)
from number_compiler.api.query_types import ExecutionQuery
from number_compiler.arithmetic.contracts.family_identity import FamilyId
from number_compiler.arithmetic.contracts.input_validation import require_integer

if TYPE_CHECKING:
    from number_compiler.api.output_schema import IndexValue


def _validate_info_names(info: tuple[ObservationId, ...]) -> None:
    if type(info) is not tuple or any(type(name) is not ObservationId for name in info):
        raise TypeError("information names must be an immutable ObservationId tuple")


@dataclass(frozen=True, slots=True)
class IndexPresentation:
    """How an already-admitted exact index is displayed to the caller."""

    encoding: IndexEncoding = IndexEncoding.INTEGER
    exponent: int | None = None

    def __post_init__(self) -> None:
        if self.encoding is IndexEncoding.INTEGER:
            if self.exponent is not None:
                raise ValueError("integer index presentation has no exponent")
        elif self.encoding is IndexEncoding.POWER10:
            if type(self.exponent) is not int or self.exponent < 0:
                raise ValueError(
                    "power10 index presentation needs a nonnegative exponent"
                )
        else:
            raise ValueError("unsupported compact index encoding")

    def value(self, index: int) -> IndexValue:
        if self.encoding is IndexEncoding.INTEGER:
            return index
        if self.exponent is None:
            raise AssertionError("validated power10 presentation lost its exponent")
        return {"encoding": "power10", "exponent": self.exponent}


@dataclass(frozen=True, slots=True)
class PresentationOptions:
    index: IndexPresentation = IndexPresentation()
    format: OutputFormat = OutputFormat.VALUE
    output_base: int = 10
    max_output_bits: int = 1_000_000
    no_value: bool = False

    def __post_init__(self) -> None:
        if type(self.index) is not IndexPresentation:
            raise TypeError("index presentation must be an IndexPresentation")
        if type(self.format) is not OutputFormat:
            raise ValueError("--format: unsupported output format")
        if type(self.output_base) is not int or not 2 <= self.output_base <= 36:
            raise ValueError("--output-base must be an integer from 2 through 36")
        if type(self.max_output_bits) is not int or self.max_output_bits < 1:
            raise ValueError("--max-output-bits must be a positive integer")
        if type(self.no_value) is not bool:
            raise TypeError("no_value must be a boolean")


@dataclass(frozen=True, slots=True)
class NoObservations:
    info: tuple[ObservationId, ...] = ()

    def __post_init__(self) -> None:
        _validate_info_names(self.info)


@dataclass(frozen=True, slots=True)
class ReverseAddObservationOptions:
    info: tuple[ObservationId, ...] = ()
    width: int = 2
    max_digits: int = 4096
    modulus: int | None = None
    pair_bank_position: int = 0
    bank_morphism_count: int = 16
    grammar_period: int = 2

    def __post_init__(self) -> None:
        _validate_info_names(self.info)
        require_integer(self.pair_bank_position, "--spatial-pair-bank-position", 0)
        require_integer(self.bank_morphism_count, "--spatial-bank-morphism-count", 1)
        require_integer(self.grammar_period, "--temporal-grammar-period", 1)
        if self.grammar_period > 32:
            raise ValueError("reverse/add bank period must be in 1..32")
        require_integer(self.max_digits, "--max-digits", 1)
        require_integer(self.width, "--width", 1)
        if self.modulus is not None:
            require_integer(self.modulus, "--modulus", 2)
            if self.modulus.bit_length() > 4096:
                raise ValueError("temporal-matrix modulus exceeds bit budget")
        width_limit = (
            self.max_digits if ObservationId.SPATIAL_MIRROR in self.info else 256
        )
        if self.width > width_limit:
            raise ValueError("mirror sheet exceeds digit budget or width limit")


@dataclass(frozen=True, slots=True)
class DoubleReverseObservationOptions:
    info: tuple[ObservationId, ...] = ()
    modulus: int | None = None
    stencil_position: int = 0
    pair_bank_position: int = 0
    bank_morphism_count: int = 16
    grammar_position: int = 0
    grammar_period: int = 2
    radix_places: int = 8
    walsh_start: int = 0
    open_ring_lookback: int = 8
    period_samples: int = 0
    defect_digits: int = 0
    period_stride: int = 1
    period_depth: int = 2
    period_max_lag: int = 16
    period_drivers: bool = False
    prefix_horizon: int = 128

    def __post_init__(self) -> None:
        _validate_info_names(self.info)
        require_integer(self.prefix_horizon, "--temporal-prefix-horizon", 1, 512)
        require_integer(self.period_samples, "--temporal-period-samples", 0, 128)
        require_integer(self.defect_digits, "--temporal-defect-digits", 0, 96)
        require_integer(self.period_stride, "--temporal-period-stride", 1, 4096)
        require_integer(self.period_depth, "--temporal-period-depth", 0, 8)
        require_integer(self.period_max_lag, "--temporal-period-max-lag", 1, 128)
        if type(self.period_drivers) is not bool:
            raise TypeError("temporal period driver demand must be Boolean")
        if self.period_samples * (2 * self.period_depth + 1) > 2048:
            raise ValueError("temporal center period sample budget exceeded")
        require_integer(self.open_ring_lookback, "--temporal-open-ring-lookback", 1)
        if self.open_ring_lookback > 160:
            raise ValueError("birth layer lookback exceeds 160 F-steps")
        if (
            self.open_ring_lookback > 32
            and ObservationId.TEMPORAL_OPEN_RING in self.info
        ):
            raise ValueError("open ring lookback exceeds 32 F-steps")
        require_integer(self.stencil_position, "--spatial-stencil-position", 0)
        require_integer(self.pair_bank_position, "--spatial-pair-bank-position", 0)
        require_integer(self.bank_morphism_count, "--spatial-bank-morphism-count", 1)
        require_integer(self.grammar_position, "--temporal-grammar-position", 0)
        require_integer(self.grammar_period, "--temporal-grammar-period", 1)
        require_integer(self.radix_places, "--arithmetic-radix-places", 1)
        require_integer(self.walsh_start, "--temporal-walsh-start", 0)
        if self.radix_places > 256:
            raise ValueError("radix projection exceeds 256 places")
        if self.grammar_period > 8:
            raise ValueError("temporal bank period exceeds 8 cells")
        if self.modulus is not None:
            require_integer(self.modulus, "--modulus", 1)
            if self.modulus.bit_length() > 4096:
                raise ValueError("closed-form modulus exceeds bit budget")


@dataclass(frozen=True, slots=True)
class CollatzTermObservationOptions:
    info: tuple[ObservationId, ...] = ()
    accumulator_modulus: int = 257
    innovation_modulus: int = 257
    clock_max_events: int = 4096
    clock_max_digits: int = 4096

    def __post_init__(self) -> None:
        _validate_info_names(self.info)
        accumulator_modulus = require_integer(
            self.accumulator_modulus, "--temporal-accumulator-modulus", 2
        )
        innovation_modulus = require_integer(
            self.innovation_modulus, "--temporal-innovation-borrow-modulus", 2
        )
        if (
            max(accumulator_modulus.bit_length(), innovation_modulus.bit_length())
            > 4096
        ):
            raise ValueError("coefficient modulus exceeds bit budget")
        require_integer(self.clock_max_events, "--temporal-clock-max-events", 0)
        require_integer(self.clock_max_digits, "--temporal-clock-max-digits", 1)
        if ObservationId.TEMPORAL_INNOVATION_BORROW in self.info and (
            type(self.innovation_modulus) is not int
            or not 3 <= self.innovation_modulus <= 4096
            or self.innovation_modulus % 2 == 0
        ):
            raise ValueError("innovation-borrow requires an odd modulus in [3, 4096]")
        if ObservationId.TEMPORAL_CLOCK in self.info:
            require_integer(self.clock_max_events, "--temporal-clock-max-events", 0)
            require_integer(self.clock_max_digits, "--temporal-clock-max-digits", 1)


@dataclass(frozen=True, slots=True)
class CollatzEventObservationOptions:
    info: tuple[ObservationId, ...] = ()
    modulus: int = 257
    twisted_width: int = 2
    twisted_sign: int = -1
    hasse_order: int = 2
    precision: int = 8
    target: int = 0
    s_weight: int = 1
    z_weight: int = 1

    def __post_init__(self) -> None:
        _validate_info_names(self.info)
        modulus = require_integer(self.modulus, "--modulus", 1)
        if modulus.bit_length() > 4096:
            raise ValueError("coefficient modulus exceeds bit budget")
        require_integer(self.twisted_width, "--arithmetic-twisted-width", 1, 256)
        require_integer(self.hasse_order, "--arithmetic-hasse-order", 1, 8)
        require_integer(self.precision, "--precision", 0, 4096)
        require_integer(self.twisted_sign, "--arithmetic-twisted-sign")
        if self.twisted_sign not in (-1, 1):
            raise ValueError("cylinder sign must be -1 or +1")
        require_integer(self.target, "--target")
        require_integer(self.s_weight, "--s-weight")
        require_integer(self.z_weight, "--z-weight")


@dataclass(frozen=True, slots=True)
class AntihydraObservationOptions:
    info: tuple[ObservationId, ...] = ()
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
        require_integer(
            self.width,
            "--spatial-width",
            0 if ObservationId.TEMPORAL_DIAGONAL_CARRY in self.info else 1,
            256,
        )
        if self.width == 0 and {
            ObservationId.ARITHMETIC_TWISTED,
            ObservationId.SPATIAL_TAPE,
            ObservationId.TEMPORAL_SPACETIME,
            ObservationId.ARITHMETIC_HASSE,
            ObservationId.ARITHMETIC_FACTOR,
        }.intersection(self.info):
            raise ValueError("full spatial width is only supported by diagonal carry")
        require_integer(self.sign, "--sign")
        require_integer(self.precision, "--precision", 0, 4096)
        require_integer(self.time_width, "--time-width", 1, 256)
        require_integer(self.time_sign, "--time-sign")
        require_integer(self.max_observer_terms, "--max-observer-terms", 0)
        if self.sign not in (-1, 1) or self.time_sign not in (-1, 1):
            raise ValueError("cylinder signs must be -1 or +1")
        if {
            ObservationId.ARITHMETIC_HENSEL,
            ObservationId.ARITHMETIC_MAHLER,
        }.intersection(self.info) and self.precision == 0:
            raise ValueError("--precision must be positive for Hensel/Mahler observers")
        if ObservationId.ARITHMETIC_HASSE in self.info and self.width > 8:
            raise ValueError("Hasse order must be from 1 through 8")
        if ObservationId.TEMPORAL_SPACETIME in self.info:
            if self.width > 64 or self.time_width > 64:
                raise ValueError("spacetime widths must be from 1 through 64")
            require_integer(self.max_observer_terms, "--max-observer-terms", 1)
        if (
            ObservationId.ARITHMETIC_FACTOR in self.info
            and pow(2, self.width, modulus) != self.sign % modulus
        ):
            raise ValueError("factor target is incompatible with the tape cylinder")


@dataclass(frozen=True, slots=True)
class CommaObservationOptions:
    info: tuple[ObservationId, ...] = ()

    def __post_init__(self) -> None:
        _validate_info_names(self.info)


@dataclass(frozen=True, slots=True)
class PrimeObservationOptions:
    info: tuple[ObservationId, ...] = ()

    def __post_init__(self) -> None:
        _validate_info_names(self.info)


@dataclass(frozen=True, slots=True)
class SpecialObservationOptions:
    info: tuple[ObservationId, ...] = ()
    defect: int | None = None
    max_digits: int = 4096
    max_candidate_bits: int = 1_000_000
    max_factor_products: int = 4096
    ordered_carry_windows: bool = False

    def __post_init__(self) -> None:
        _validate_info_names(self.info)
        if self.defect is not None:
            require_integer(self.defect, "--defect", 0)
        require_integer(self.max_digits, "--max-digits", 1)
        require_integer(self.max_candidate_bits, "--max-candidate-bits", 1)
        require_integer(self.max_factor_products, "--max-factor-products", 1)
        if type(self.ordered_carry_windows) is not bool:
            raise TypeError("ordered carry windows demand must be Boolean")


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
    matrix: MatrixRequest | None = None

    def __post_init__(self) -> None:
        if type(self.presentation) is not PresentationOptions:
            raise TypeError("presentation must be PresentationOptions")
        if type(self.max_index_bits) is not int or self.max_index_bits < 1:
            raise ValueError("maximum index bits must be a positive integer")
        family = getattr(self.execution, "family", None)
        selector = getattr(self.execution, "selector", None)
        if type(family) is not FamilyId or type(selector) is not SelectorId:
            raise TypeError("execution must carry registered family and selector ids")
        from number_compiler.api.family_registry import family_spec

        spec = family_spec(family)
        expected_query = {
            SelectorId.NTH: spec.query_type,
            SelectorId.EVENTS: spec.event_query_type,
            SelectorId.VERIFY: spec.verify_query_type,
        }.get(selector)
        if expected_query is None or type(self.execution) is not expected_query:
            raise TypeError("execution must match its registered exact query type")
        if type(self.index) is not int or self.index < 0:
            raise TypeError("execution index must be a nonnegative integer")
        if self.index.bit_length() > self.max_index_bits:
            raise ValueError("index exceeds --max-index-bits")
        if (
            self.presentation.index.encoding is IndexEncoding.POWER10
            and not _matches_power10(
                self.index, self.presentation.index.exponent, self.max_index_bits
            )
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
                if selector is SelectorId.EVENTS
                else spec.term_observation
            )
            if selector is SelectorId.VERIFY or binding is None:
                raise ValueError("execution selector does not accept observations")
            if type(self.observations) is not binding.options_type:
                raise TypeError("observations must match the registered option type")
            if type(self.observations.info) is not tuple or any(
                type(name) is not ObservationId for name in self.observations.info
            ):
                raise TypeError(
                    "observation names must be an immutable ObservationId tuple"
                )
            supported_info = (
                spec.event_info if selector is SelectorId.EVENTS else spec.nth_info
            )
            if set(self.observations.info) - set(supported_info):
                raise ValueError(
                    "requested information is unavailable for this selector"
                )
            spec.validate_observation_request(self.execution, self.observations)
        if {
            ObservationId.TEMPORAL_MATRIX,
            ObservationId.TEMPORAL_MATRIX_TRACE,
        }.intersection(self.observations.info):
            if spec.matrix is None or self.matrix is None:
                raise ValueError("temporal.matrix requires an admitted matrix request")
            spec.matrix.validate(self.matrix)
            from number_compiler.api.matrix_contracts import SourceTransferRequest

            trace = ObservationId.TEMPORAL_MATRIX_TRACE in self.observations.info
            if isinstance(self.matrix, SourceTransferRequest):
                if self.matrix.trace is not trace:
                    raise ValueError(
                        "matrix trace demand differs from its admitted request"
                    )
            elif trace:
                raise ValueError("matrix.trace requires source-transfer kind")
            if (
                spec.matrix.max_source_index is not None
                and self.index > spec.matrix.max_source_index
            ):
                raise ValueError("matrix source index exceeds admitted budget")
        elif self.matrix is not None:
            raise ValueError("matrix request requires --info temporal.matrix")

    @property
    def family(self) -> FamilyId:
        return self.execution.family

    @property
    def selector(self) -> SelectorId:
        return self.execution.selector

    @property
    def index(self) -> int:
        return self.execution.index

    @property
    def index_unit(self) -> IndexUnit:
        from number_compiler.api.family_registry import family_spec

        unit = family_spec(self.family).unit_for(self.selector)
        if unit is None:
            raise RuntimeError("registered selector has no declared index unit")
        return unit

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
