"""Canonical typed identifiers and categories for CLI observations."""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum
from types import MappingProxyType
from typing import TYPE_CHECKING, Final, TypeAlias

if TYPE_CHECKING:
    from number_compiler.api.output_schema import ObservationPacket


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


class OptionValueKind(StrEnum):
    """Parser kind for one option declared by the family registry."""

    INTEGER = "integer"
    BOOLEAN = "boolean"
    CHOICE = "choice"


OptionDefault: TypeAlias = int | bool | str | StrEnum | None


def option_default(value: object) -> OptionDefault:
    """Admit defaults discovered from dataclass metadata at the registry boundary."""
    if value is None:
        return value
    if type(value) is int:
        return value
    if type(value) is bool:
        return value
    if type(value) is str:
        return value
    if isinstance(value, StrEnum):
        return value
    raise TypeError("registered parser option has an unsupported default")


class ObservationId(StrEnum):
    METRICS = "metrics"
    TEMPORAL = "temporal"
    TEMPORAL_CLOCK = "temporal.clock"
    TEMPORAL_MACRO = "temporal.macro"
    TEMPORAL_MATRIX = "temporal.matrix"
    TEMPORAL_MATRIX_TRACE = "temporal.matrix.trace"
    TEMPORAL_STENCIL = "temporal.stencil"
    TEMPORAL_BANK = "temporal.bank"
    TEMPORAL_BIRTH_LAYERS = "temporal.birth-layers"
    TEMPORAL_OPEN_RING = "temporal.open-ring"
    TEMPORAL_SEED_ORBIT = "temporal.seed-orbit"
    TEMPORAL_GRAMMAR = "temporal.grammar"
    TEMPORAL_RADIX_WALSH = "temporal.radix-walsh"
    TEMPORAL_CLOSED_FORM = "temporal.closed-form"
    TEMPORAL_RESIDUE99 = "temporal.residue99"
    TEMPORAL_ACCUMULATOR99 = "temporal.accumulator99"
    TEMPORAL_SEED_MORPHISM = "temporal.seed-morphism"
    TEMPORAL_DEFECT_CLOCK = "temporal.defect-clock"
    TEMPORAL_CARRY_SAFETY = "temporal.carry-safety"
    TEMPORAL_ACCUMULATOR = "temporal.accumulator"
    TEMPORAL_DOUBLE_ACCUMULATOR = "temporal.double-accumulator"
    TEMPORAL_INNOVATION_BORROW = "temporal.innovation-borrow"
    TEMPORAL_SPACETIME = "temporal.spacetime"
    TEMPORAL_DIAGONAL_CARRY = "temporal.diagonal-carry"
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


@dataclass(frozen=True, slots=True)
class OptionSpec:
    """One typed CLI option and the information packets which consume it."""

    default: OptionDefault
    information: tuple[ObservationId, ...]
    required: bool = False
    name: str = ""
    value_kind: OptionValueKind = OptionValueKind.INTEGER
    help: str = ""
    choices: tuple[str, ...] = ()
    flag_name: str | None = None

    def __post_init__(self) -> None:
        if type(self.name) is not str or type(self.help) is not str:
            raise TypeError("option name and help must be strings")
        if type(self.information) is not tuple or any(
            type(identifier) is not ObservationId for identifier in self.information
        ):
            raise TypeError("option information must be declared ObservationIds")
        if type(self.choices) is not tuple or any(
            type(choice) is not str for choice in self.choices
        ):
            raise TypeError("option choices must be a tuple of strings")
        if self.flag_name is not None and type(self.flag_name) is not str:
            raise TypeError("option flag name must be a string")
        if type(self.value_kind) is not OptionValueKind:
            raise TypeError("option value kind must be declared by OptionValueKind")
        if type(self.required) is not bool:
            raise TypeError("option required flag must be Boolean")
        if self.value_kind is OptionValueKind.INTEGER and self.default is not None:
            if type(self.default) is not int:
                raise TypeError("integer option default must be an integer")
        elif self.value_kind is OptionValueKind.BOOLEAN and self.default is not None:
            if type(self.default) is not bool:
                raise TypeError("Boolean option default must be Boolean")
        elif self.value_kind is OptionValueKind.CHOICE:
            if self.default is not None and not isinstance(self.default, str):
                raise TypeError("choice option default must be a string value")
            if self.default is not None and self.default not in self.choices:
                raise ValueError("choice option default must be one of its choices")

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

    def __post_init__(self) -> None:
        if any(
            type(name) is not str or not name
            for name in (self.module, self.prepare, self.admit, self.observe)
        ):
            raise TypeError("observation adapter bindings must be nonempty names")


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
        ObservationId.TEMPORAL_MATRIX_TRACE,
        ObservationId.TEMPORAL_STENCIL,
        ObservationId.TEMPORAL_BANK,
        ObservationId.TEMPORAL_OPEN_RING,
        ObservationId.TEMPORAL_SEED_ORBIT,
        ObservationId.TEMPORAL_BIRTH_LAYERS,
        ObservationId.TEMPORAL_GRAMMAR,
        ObservationId.TEMPORAL_RADIX_WALSH,
        ObservationId.TEMPORAL_CLOSED_FORM,
        ObservationId.TEMPORAL_RESIDUE99,
        ObservationId.TEMPORAL_ACCUMULATOR99,
        ObservationId.TEMPORAL_SEED_MORPHISM,
        ObservationId.TEMPORAL_DEFECT_CLOCK,
        ObservationId.TEMPORAL_CARRY_SAFETY,
        ObservationId.TEMPORAL_ACCUMULATOR,
        ObservationId.TEMPORAL_DOUBLE_ACCUMULATOR,
        ObservationId.TEMPORAL_INNOVATION_BORROW,
        ObservationId.TEMPORAL_SPACETIME,
        ObservationId.TEMPORAL_DIAGONAL_CARRY,
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
    "IndexEncoding",
    "IndexUnit",
    "ObservationAdapterBinding",
    "ObservationCategory",
    "ObservationId",
    "ObservationSpec",
    "OptionSpec",
    "OptionDefault",
    "OptionValueKind",
    "OutputFormat",
    "OutputStatus",
    "SelectorId",
    "index_unit",
    "observation_id",
    "option_default",
    "output_status",
    "selector_id",
]
