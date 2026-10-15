"""Typed wire contracts for query results and demanded observation packets."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Literal, NotRequired, TypeAlias, TypedDict

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
