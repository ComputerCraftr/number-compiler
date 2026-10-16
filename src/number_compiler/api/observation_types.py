"""Canonical typed identifiers and categories for CLI observations."""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum
from types import MappingProxyType
from typing import TYPE_CHECKING, Final

if TYPE_CHECKING:
    from number_compiler.api.output_schema import ObservationPacket


class FamilyId(StrEnum):
    REVERSE_ADD = "reverse-add"
    DOUBLE_REVERSE = "2rev10"
    COLLATZ = "collatz"
    ANTIHYDRA = "antihydra"
    A367620 = "a367620"
    PRIME = "prime"
    FERMAT = "fermat"
    MERSENNE = "mersenne"


class SelectorId(StrEnum):
    NTH = "nth"
    EVENTS = "events"
    VERIFY = "verify"


class IndexUnit(StrEnum):
    ITERATIONS = "iterations"
    PHYSICAL_ITERATIONS = "physical_iterations"
    MACRO_RETURNS_AFTER_STARTUP = "macro_returns_after_startup"
    OEIS_INDEX = "oeis_index"
    PRIME_INDEX = "prime_index"
    FERMAT_INDEX = "fermat_index"
    MERSENNE_EXPONENT = "mersenne_exponent"
    ACCELERATED_ODD_EVENTS = "accelerated_odd_events"
    CERTIFICATE = "certificate"


class OutputFormat(StrEnum):
    VALUE = "value"
    SYMBOLIC = "symbolic"
    JSON = "json"


class IndexEncoding(StrEnum):
    INTEGER = "integer"
    POWER10 = "power10"


class OutputStatus(StrEnum):
    AVAILABLE = "available"
    SNAPSHOT = "snapshot"
    UNAVAILABLE = "unavailable"
    UNKNOWN = "unknown"
    PRIME = "prime"
    COMPOSITE = "composite"
    NOT_APPLICABLE = "not_applicable"
    NOT_FOUND = "not_found"
    REJECTED = "rejected"


class ObservationCategory(StrEnum):
    METRICS = "metrics"
    TEMPORAL = "temporal"
    SPATIAL = "spatial"
    ARITHMETIC = "arithmetic"
    SAFETY = "safety"
    NUMBER_THEORY = "number-theory"


class ObservationId(StrEnum):
    METRICS = "metrics"
    TEMPORAL = "temporal"
    TEMPORAL_CLOCK = "temporal.clock"
    TEMPORAL_MACRO = "temporal.macro"
    TEMPORAL_MATRIX = "temporal.matrix"
    TEMPORAL_STENCIL = "temporal.stencil"
    TEMPORAL_BANK = "temporal.bank"
    TEMPORAL_BIRTH_LAYERS = "temporal.birth-layers"
    TEMPORAL_OPEN_RING = "temporal.open-ring"
    TEMPORAL_GRAMMAR = "temporal.grammar"
    TEMPORAL_RADIX_WALSH = "temporal.radix-walsh"
    TEMPORAL_CLOSED_FORM = "temporal.closed-form"
    TEMPORAL_RESIDUE99 = "temporal.residue99"
    TEMPORAL_CARRY_SAFETY = "temporal.carry-safety"
    TEMPORAL_ACCUMULATOR = "temporal.accumulator"
    TEMPORAL_INNOVATION_BORROW = "temporal.innovation-borrow"
    TEMPORAL_SPACETIME = "temporal.spacetime"
    SPATIAL_MIRROR = "spatial.mirror"
    SPATIAL_STENCIL = "spatial.stencil"
    SPATIAL_PAIR_BANK = "spatial.pair-bank"
    SPATIAL_BANK_MORPHISM = "spatial.bank-morphism"
    SPATIAL_BANK_WINDOW = "spatial.bank-window"
    SPATIAL_TAPE = "spatial.tape"
    ARITHMETIC_MODULAR = "arithmetic.modular"
    ARITHMETIC_RADIX25_SHIFT = "arithmetic.radix25-shift"
    ARITHMETIC_TWISTED = "arithmetic.twisted"
    ARITHMETIC_HASSE = "arithmetic.hasse"
    ARITHMETIC_HENSEL = "arithmetic.hensel"
    ARITHMETIC_MAHLER = "arithmetic.mahler"
    ARITHMETIC_TROPICAL = "arithmetic.tropical"
    ARITHMETIC_FACTOR = "arithmetic.factor"
    SAFETY_EXECUTION = "safety.execution"
    SAFETY_LEDGER = "safety.ledger"
    SAFETY_CERTIFICATE = "safety.certificate"
    NUMBER_THEORY_PRIMALITY = "number-theory.primality"
    NUMBER_THEORY_FACTOR = "number-theory.factor"
    NUMBER_THEORY_ROOT = "number-theory.root"


@dataclass(frozen=True, slots=True, init=False)
class OptionSpec:
    """One typed CLI option and the information packets which consume it."""

    default: object | None
    information: tuple[ObservationId, ...]
    required: bool = False
    name: str = ""
    value_kind: str = "integer"
    help: str = ""
    choices: tuple[str, ...] = ()
    flag_name: str | None = None

    def __init__(
        self,
        default: object | None,
        information: tuple[str | ObservationId, ...],
        required: bool = False,
        name: str = "",
        value_kind: str = "integer",
        help: str = "",
        choices: tuple[str, ...] = (),
        flag_name: str | None = None,
    ) -> None:
        object.__setattr__(self, "default", default)
        object.__setattr__(
            self, "information", tuple(observation_id(value) for value in information)
        )
        object.__setattr__(self, "required", required)
        object.__setattr__(self, "name", name)
        object.__setattr__(self, "value_kind", value_kind)
        object.__setattr__(self, "help", help)
        object.__setattr__(self, "choices", choices)
        object.__setattr__(self, "flag_name", flag_name)

    @property
    def flag(self) -> str:
        flag = self.name if self.flag_name is None else self.flag_name
        return "--" + flag.replace("_", "-")


@dataclass(frozen=True, slots=True)
class ObservationAdapterBinding:
    """Lazy family adapter methods for an observation selection."""

    module: str
    prepare: str
    admit: str
    observe: str


@dataclass(frozen=True, slots=True)
class ObservationSpec:
    """Resolved selector, coordinate, option, adapter, and packet contract."""

    identifier: ObservationId
    category: ObservationCategory
    selectors: tuple[SelectorId, ...] = (SelectorId.NTH,)
    selector_units: tuple[tuple[SelectorId, IndexUnit], ...] = ()
    options: tuple[OptionSpec, ...] = ()
    adapter: ObservationAdapterBinding | None = None

    @property
    def packet_schema(self) -> type[ObservationPacket]:
        from number_compiler.api.output_schema import ObservationPacket

        return ObservationPacket

    def unit_for(self, selector: SelectorId) -> IndexUnit | None:
        """Return the coordinate unit for this observation under a selector."""
        return next(
            (unit for selected, unit in self.selector_units if selected is selector),
            None,
        )


_CATEGORIES: Final[dict[ObservationCategory, tuple[ObservationId, ...]]] = {
    ObservationCategory.METRICS: (ObservationId.METRICS,),
    ObservationCategory.TEMPORAL: (
        ObservationId.TEMPORAL,
        ObservationId.TEMPORAL_CLOCK,
        ObservationId.TEMPORAL_MACRO,
        ObservationId.TEMPORAL_MATRIX,
        ObservationId.TEMPORAL_STENCIL,
        ObservationId.TEMPORAL_BANK,
        ObservationId.TEMPORAL_OPEN_RING,
        ObservationId.TEMPORAL_BIRTH_LAYERS,
        ObservationId.TEMPORAL_GRAMMAR,
        ObservationId.TEMPORAL_RADIX_WALSH,
        ObservationId.TEMPORAL_CLOSED_FORM,
        ObservationId.TEMPORAL_RESIDUE99,
        ObservationId.TEMPORAL_CARRY_SAFETY,
        ObservationId.TEMPORAL_ACCUMULATOR,
        ObservationId.TEMPORAL_INNOVATION_BORROW,
        ObservationId.TEMPORAL_SPACETIME,
    ),
    ObservationCategory.SPATIAL: (
        ObservationId.SPATIAL_MIRROR,
        ObservationId.SPATIAL_STENCIL,
        ObservationId.SPATIAL_PAIR_BANK,
        ObservationId.SPATIAL_BANK_MORPHISM,
        ObservationId.SPATIAL_BANK_WINDOW,
        ObservationId.SPATIAL_TAPE,
    ),
    ObservationCategory.ARITHMETIC: (
        ObservationId.ARITHMETIC_MODULAR,
        ObservationId.ARITHMETIC_RADIX25_SHIFT,
        ObservationId.ARITHMETIC_TWISTED,
        ObservationId.ARITHMETIC_HASSE,
        ObservationId.ARITHMETIC_HENSEL,
        ObservationId.ARITHMETIC_MAHLER,
        ObservationId.ARITHMETIC_TROPICAL,
        ObservationId.ARITHMETIC_FACTOR,
    ),
    ObservationCategory.SAFETY: (
        ObservationId.SAFETY_EXECUTION,
        ObservationId.SAFETY_LEDGER,
        ObservationId.SAFETY_CERTIFICATE,
    ),
    ObservationCategory.NUMBER_THEORY: (
        ObservationId.NUMBER_THEORY_PRIMALITY,
        ObservationId.NUMBER_THEORY_FACTOR,
        ObservationId.NUMBER_THEORY_ROOT,
    ),
}

OBSERVATION_REGISTRY: Final[MappingProxyType[ObservationId, ObservationSpec]] = (
    MappingProxyType(
        {
            identifier: ObservationSpec(identifier, category)
            for category, identifiers in _CATEGORIES.items()
            for identifier in identifiers
        }
    )
)


def observation_id(value: str | ObservationId) -> ObservationId:
    """Validate a CLI spelling once at the external request boundary."""
    if isinstance(value, ObservationId):
        return value
    try:
        return ObservationId(value)
    except ValueError as error:
        raise ValueError(f"unknown observation: {value}") from error


def family_id(value: str | FamilyId) -> FamilyId:
    """Validate a family spelling once at a CLI or integration boundary."""
    if isinstance(value, FamilyId):
        return value
    try:
        return FamilyId(value)
    except ValueError as error:
        raise ValueError(f"unknown family: {value}") from error


def selector_id(value: str | SelectorId) -> SelectorId:
    """Validate one request selector at the parser boundary."""
    if isinstance(value, SelectorId):
        return value
    try:
        return SelectorId(value)
    except ValueError as error:
        raise ValueError(f"unknown selector: {value}") from error


def index_unit(value: str | IndexUnit) -> IndexUnit:
    """Validate the declared family coordinate unit."""
    if isinstance(value, IndexUnit):
        return value
    try:
        return IndexUnit(value)
    except ValueError as error:
        raise ValueError(f"unknown index unit: {value}") from error


def output_status(value: str | OutputStatus) -> OutputStatus:
    """Validate a public information-packet status."""
    if isinstance(value, OutputStatus):
        return value
    try:
        return OutputStatus(value)
    except ValueError as error:
        raise ValueError(f"unknown output status: {value}") from error


__all__ = [
    "OBSERVATION_REGISTRY",
    "FamilyId",
    "IndexEncoding",
    "IndexUnit",
    "ObservationAdapterBinding",
    "ObservationCategory",
    "ObservationId",
    "ObservationSpec",
    "OptionSpec",
    "OutputFormat",
    "OutputStatus",
    "SelectorId",
    "family_id",
    "index_unit",
    "observation_id",
    "output_status",
    "selector_id",
]
