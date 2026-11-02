"""Typed wire contracts for query results and demanded observation packets."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal, NotRequired, Required, TypeAlias, TypedDict

JsonValue: TypeAlias = (
    str
    | int
    | float
    | bool
    | None
    | list["JsonValue"]
    | tuple["JsonValue", ...]
    | dict[str, "JsonValue"]
)


class EncodedIntegerPacket(TypedDict):
    """Exact integer wire encoding used when Python decimal conversion is unsafe."""

    encoding: Literal["hex"]
    value: str
    bits: int


JsonInteger: TypeAlias = int | EncodedIntegerPacket


class RationalValuePacket(TypedDict):
    numerator: JsonInteger
    denominator: JsonInteger


class MahlerActionPacket(TypedDict, total=False):
    """Named fields of the finite Mahler action observation."""

    source_binding: str
    extent: JsonInteger
    homogeneous_growth: JsonValue
    radial_sturmian: JsonValue
    source_bound_radix6_difference: JsonValue
    source_bound_joint_successor: JsonValue
    source_bound_odd_to_odd: JsonValue
    source_cylinder: JsonValue
    radial_affine_arithmetic: JsonValue
    bit_convention: str
    scale: RationalValuePacket
    offset: RationalValuePacket
    cap: RationalValuePacket | None
    initial_margin: str
    pulled_threshold: JsonValue
    first_failure: JsonInteger | None
    first_failure_index_unit: str
    predicate: str
    temporal_run_residual: JsonValue
    root_shell: JsonValue
    all_time_claim: bool


class AntihydraTangentFields(TypedDict, total=False):
    """Fields shared by finite tangent projections."""

    source: Required[JsonInteger]
    timestamp_macro_returns: Required[JsonInteger]
    consumed_centered_odd_events: Required[JsonInteger]
    slack: Required[JsonInteger]
    at_odd_seam: Required[bool]
    all_time_barrier_proved: Required[bool]
    moving_cylinder: Required[JsonValue]
    even_run_depth: JsonInteger
    precision: JsonInteger
    normalized_residue: JsonInteger
    clock_root: JsonInteger
    matched_bits: JsonInteger
    matched_radix64_cells: JsonInteger
    resolved: bool
    gap: JsonInteger
    child_precision: JsonInteger
    child_normalized_residue: JsonInteger
    required_next_precision: JsonInteger


class AntihydraTangentPacket(AntihydraTangentFields, total=False):
    """Finite tangent fields, with optional source-bound Mahler projection."""

    associated_action: NotRequired[MahlerActionPacket]


class AntihydraMahlerTangentPacket(AntihydraTangentFields, total=False):
    """Tangent packet whose Mahler action is required by this observation."""

    associated_action: Required[MahlerActionPacket]


class AntihydraSourceFields(TypedDict, total=False):
    """Authenticated source and work metadata shared by demanded observers."""

    family: Required[Literal["antihydra"]]
    machine: Required[str]
    machine_sha256: Required[str]
    source_binding: Required[str]
    kind: Required[str]
    index_unit: Required[str]
    requested_returns: Required[JsonInteger]
    completed_returns: Required[JsonInteger]
    scope: Required[str]
    work_counters: NotRequired[dict[str, JsonValue]]
    peak_nodes: NotRequired[JsonInteger]
    retained_nodes: NotRequired[JsonInteger]


class AntihydraDiagonalPacket(TypedDict):
    """Demanded finite carry field, with no all-time execution authority."""

    family: Literal["antihydra"]
    kind: Literal["temporal.diagonal-carry"]
    source_binding: str
    requested_returns: int
    endpoint: int
    clock_unit: Literal["macro_returns_after_startup"]
    all_time_claim: Literal[False]
    field: JsonValue


class CollatzDiagonalPacket(TypedDict):
    """Finite spatial projections of one issued physical/normalized run."""

    family: Literal["collatz"]
    kind: Literal["temporal.diagonal-carry"]
    source: int
    normalized_endpoint: int
    physical_endpoint: int
    normalized_steps: int
    physical_ticks: int
    phase: int
    clock_unit: Literal["physical_iterations"]
    moving_cut: Literal["binary-normalized"]
    field_width: int
    complete: bool
    field: JsonValue
    macro_affine_carries_lsb: tuple[int, ...]
    macro_laurent_carry_lsb: tuple[int, ...]
    macro_laurent_factor: Literal["z-2"]
    weighted_laurent_complete: bool
    weighted_laurent_aggregate: JsonValue
    all_time_claim: Literal[False]


class AntihydraRunAvailablePacket(AntihydraSourceFields):
    status: Literal["available"]
    halted: Literal[False]
    nonhalting_certified: Literal[False]
    value: AntihydraMahlerTangentPacket


class AntihydraRunUnavailablePacket(TypedDict):
    status: Literal["unavailable"]
    family: Literal["antihydra"]
    kind: str
    reason: str
    requested_returns: JsonInteger
    halt_boundary: JsonInteger
    halted: Literal[True]
    physical_ticks_at_halt: JsonInteger
    nonhalting_certified: Literal[False]


AntihydraRunMahlerPacket: TypeAlias = (
    AntihydraRunAvailablePacket | AntihydraRunUnavailablePacket
)


class AntihydraArithmeticPacket(AntihydraSourceFields):
    guarded_physical_status: str
    ledger_first_failure_index: JsonInteger | None
    nonhalting_certified: Literal[False]
    value: AntihydraTangentPacket


class BlankLedgerPacket(TypedDict):
    delta: int
    minimum: int
    maximum: int


class CollatzTapeWidthPacket(TypedDict):
    radix: Literal[2]
    scope: str
    source_width: int
    target_width: int
    physical_ticks: int
    normalized_symbols: int
    odd_steps: int
    blank: BlankLedgerPacket


class RadialSturmianPacket(TypedDict):
    growths: int
    halvings: int
    binary_order: int
    prefix_width: int
    prefix_value: int
    precision_bits: int
    scope: str


class HomogeneousGrowthPacket(TypedDict):
    growths: int
    halvings: int
    radix: int
    homogeneous_radix_order: int


class CollatzPhysicalClockValue(TypedDict):
    events: int
    divisions: int
    physical_ticks: int
    real_prime_exponents: tuple[int, int]
    two_adic_exponent: int
    three_adic_exponent: int
    homogeneous_growth: HomogeneousGrowthPacket
    radial_sturmian: RadialSturmianPacket


class PhysicalCollatzClockPacket(TypedDict):
    family: Literal["collatz"]
    kind: Literal["physical-clock"]
    scope: str
    requested_ticks: int
    width_tape: CollatzTapeWidthPacket | None
    value: CollatzPhysicalClockValue
    work_counters: NotRequired[dict[str, int]]
    peak_nodes: NotRequired[int]
    retained_nodes: NotRequired[int]


IndexValue: TypeAlias = int | dict[str, JsonValue]


@dataclass(frozen=True, slots=True)
class VerificationResult:
    accepted: bool
    packet: dict[str, JsonValue]
    success_message: str


class ObservationPacket(TypedDict):
    family: str
    kind: str
    index: IndexValue
    index_unit: str
    status: str


def observation_packet(
    *,
    family: str,
    kind: str,
    index: IndexValue,
    index_unit: str,
    status: str,
) -> ObservationPacket:
    """Create the shared typed envelope for one demanded observation."""
    return {
        "family": family,
        "kind": kind,
        "index": index,
        "index_unit": index_unit,
        "status": status,
    }


class UnresolvedErrorPacket(TypedDict):
    code: Literal["unresolved_sequence_boundary"]
    requested_index: IndexValue
    certified_max_index: int
    certificate_id: str
    reason: str


class QueryResult(TypedDict):
    family: str
    index: IndexValue
    index_unit: str
    output_base: int
    value: str | None
    info: dict[str, dict[str, JsonValue]]
    error: NotRequired[UnresolvedErrorPacket]


def query_result(
    *,
    family: str,
    index: IndexValue,
    index_unit: str,
    output_base: int,
    value: str | None,
    info: dict[str, dict[str, JsonValue]],
    error: UnresolvedErrorPacket | None = None,
) -> QueryResult:
    """Publish only already-demanded values; serialization performs no queries."""
    result: QueryResult = {
        "family": family,
        "index": index,
        "index_unit": index_unit,
        "output_base": output_base,
        "value": value,
        "info": info,
    }
    if error is not None:
        result["error"] = error
    return result
