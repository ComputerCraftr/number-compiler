"""Bounded canonical decoding for FutureCID class tables."""

from __future__ import annotations

import base64
import binascii
import json
from collections.abc import Callable, Mapping
from dataclasses import dataclass
from hashlib import sha256
from pathlib import Path
from types import MappingProxyType
from typing import Final, cast

from number_compiler.arithmetic.contracts.input_validation import (
    is_mapping_instance,
    is_object_list_instance,
    is_runtime_instance,
)
from number_compiler.resources.bounded_json import (
    NodeReserver,
    snapshot_canonical_json,
)
from number_compiler.sequences.comma.boundary_chart import PERIOD
from number_compiler.sequences.comma.future_authority import (
    FutureClass,
    FutureControl,
)

SOURCE_COUNT: Final[int] = 2 * 8 * PERIOD
FUTURE_CANDIDATE_FORMAT: Final[str] = "comma-semantic-future-candidate-v2"
FUTURE_CANDIDATE_AUTHORITY: Final[str] = "untrusted-source-derived-candidate"
FUTURE_SOURCE_UNIVERSE: Final[str] = "kind=N,Z; a=2..9; residue=0..923; nested-order"
MAX_CANDIDATE_BYTES: Final[int] = 2 * 1024 * 1024
MAX_CANDIDATE_JSON_DEPTH: Final[int] = 16
MAX_CANDIDATE_JSON_NODES: Final[int] = 1_048_576
MAX_CID_VARINT_BYTES: Final[int] = 2
RECORD_FIELDS: Final[frozenset[str]] = frozenset(
    {
        "format",
        "authority",
        "state_universe",
        "class_of_state_varint_base64",
        "controls",
        "ordered_children",
        "class_rank_candidate",
    }
)
WorkCharger = Callable[[int], None]
BeforeCandidateParse = Callable[[Mapping[str, object]], None]
ReserveDecodedShape = Callable[[Mapping[str, object]], None]


@dataclass(frozen=True, slots=True)
class ParsedFutureCandidate:
    """Structurally checked candidate data with no runtime authority."""

    source_classes: tuple[int, ...]
    classes: tuple[FutureClass, ...]
    artifact_sha256: str


def decode_class_map(
    payload: bytes,
    class_count: int,
    *,
    source_count: int,
    max_varint_bytes: int,
) -> tuple[int, ...]:
    """Decode the bounded canonical varint map from sources to class IDs."""
    if type(payload) is not bytes or len(payload) > source_count * max_varint_bytes:
        raise ValueError("future source map exceeds its bounded varint payload")
    values: list[int] = []
    current = 0
    shift = 0
    width = 0
    for byte in payload:
        width += 1
        if width > max_varint_bytes:
            raise ValueError("future source map contains an oversized CID varint")
        current |= (byte & 0x7F) << shift
        if byte & 0x80:
            shift += 7
            continue
        if current >= class_count:
            raise ValueError("future source map contains an out-of-range CID")
        if width > 1 and current < (1 << (7 * (width - 1))):
            raise ValueError("future source map contains a noncanonical CID varint")
        values.append(current)
        if len(values) > source_count:
            raise ValueError("future source map has too many source entries")
        current = 0
        shift = 0
        width = 0
    if width:
        raise ValueError("future source map ends with a truncated CID varint")
    if len(values) != source_count:
        raise ValueError("future source map is truncated or has extra source entries")
    return tuple(values)


def decode_class_rows(
    raw_controls: list[object],
    raw_children: list[object],
    raw_ranks: list[object],
    class_count: int,
) -> tuple[FutureClass, ...]:
    """Decode exactly two ordered children and one optional rank per class."""
    result: list[FutureClass] = []
    for raw_control, raw_row, raw_rank in zip(
        raw_controls, raw_children, raw_ranks, strict=True
    ):
        if not is_object_list_instance(raw_control) or len(raw_control) != 2:
            raise ValueError("future class control is malformed")
        kind, coefficient = raw_control
        if type(kind) is not str:
            raise ValueError("future class control is neither Fork nor Landmine")
        if kind == "fork":
            if type(coefficient) is not int or not 2 <= coefficient <= 9:
                raise ValueError("future Fork control needs its exact coefficient")
            control = FutureControl("fork", coefficient)
        elif kind == "landmine":
            if coefficient is not None:
                raise ValueError("future Landmine control cannot carry a coefficient")
            control = FutureControl("landmine", coefficient)
        else:
            raise ValueError("future class control is neither Fork nor Landmine")
        if not is_object_list_instance(raw_row) or len(raw_row) != 2:
            raise ValueError("future class row must preserve two ordered slots")
        children: list[int | None] = []
        for target in raw_row:
            if target is None:
                children.append(None)
            elif type(target) is int and 0 <= target < class_count:
                children.append(target)
            else:
                raise ValueError("future ordered child leaves the class table")
        if control.kind == "landmine" and children != [None, None]:
            raise ValueError("future Landmine row carries child edges")
        if control.kind == "fork" and any(child is None for child in children):
            raise ValueError("future Fork row lost an ordered child")
        if raw_rank is None:
            rank = None
        elif type(raw_rank) is int and raw_rank >= 0:
            rank = raw_rank
        else:
            raise ValueError("future rank must be a nonnegative integer or null")
        result.append(FutureClass(control, (children[0], children[1]), rank))
    return tuple(result)


def canonical_json_bytes(record: Mapping[str, object]) -> bytes:
    """Encode an artifact deterministically while rejecting non-JSON values."""
    try:
        text = json.dumps(
            record,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
            allow_nan=False,
        )
    except (TypeError, ValueError) as exc:
        raise ValueError("future candidate contains non-JSON data") from exc
    return (text + "\n").encode("ascii")


def reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    """Reject ambiguous JSON objects before artifact admission."""
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError("duplicate future candidate JSON key")
        result[key] = value
    return result


def parse_future_candidate(
    record: Mapping[str, object], *, charge_work: WorkCharger
) -> ParsedFutureCandidate:
    """Check bounded JSON structure without granting provider authority."""
    snapshot = preflight_future_candidate(record, charge_work=charge_work)
    return parse_preflighted_future_candidate(snapshot, charge_work=charge_work)


def parse_future_candidate_file(
    path: Path,
    *,
    charge_work: WorkCharger,
    before_parse: BeforeCandidateParse | None = None,
    reserve_nodes: NodeReserver | None = None,
    reserve_decoded_shape: ReserveDecodedShape | None = None,
) -> ParsedFutureCandidate:
    """Read and validate one bounded canonical candidate file."""
    if not is_runtime_instance(path, Path):
        raise TypeError("future candidate path must be a pathlib Path")
    size = path.stat().st_size
    if size > MAX_CANDIDATE_BYTES:
        raise ValueError("future candidate exceeds the bounded input size")
    estimated_work = max(1, (size + 65_535) // 65_536)
    charge_work_amount(charge_work, estimated_work)
    with path.open("rb") as stream:
        payload = stream.read(MAX_CANDIDATE_BYTES + 1)
    actual_work = max(1, (len(payload) + 65_535) // 65_536)
    if actual_work > estimated_work:
        charge_work_amount(charge_work, actual_work - estimated_work)
    if len(payload) > MAX_CANDIDATE_BYTES:
        raise ValueError("future candidate exceeds the bounded input size")
    try:
        text = payload.decode("utf-8")
        raw: object = json.loads(text, object_pairs_hook=reject_duplicate_keys)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError("future candidate is not valid UTF-8 JSON") from exc
    except RecursionError as exc:
        raise ValueError(
            "future candidate JSON exceeds the parser nesting bound"
        ) from exc
    if type(raw) is not dict:
        raise ValueError("future candidate JSON root must be an object")
    raw_record = cast(dict[str, object], raw)
    snapshot = preflight_future_candidate(
        raw_record,
        charge_work=charge_work,
        reserve_nodes=reserve_nodes,
    )
    if payload != canonical_json_bytes(snapshot):
        raise ValueError("future candidate JSON is not in canonical form")
    if before_parse is not None:
        before_parse(raw_record)
    if reserve_decoded_shape is not None:
        reserve_decoded_shape(snapshot)
    return parse_preflighted_future_candidate(
        snapshot,
        charge_work=charge_work,
        artifact_sha256=sha256(payload).hexdigest(),
    )


def parse_preflighted_future_candidate(
    record: Mapping[str, object],
    *,
    charge_work: WorkCharger,
    artifact_sha256: str | None = None,
) -> ParsedFutureCandidate:
    """Decode a record after its JSON shape and serialized size were bounded."""
    source_classes, classes = validate_record(record, charge_work=charge_work)
    digest = (
        future_candidate_sha256(record) if artifact_sha256 is None else artifact_sha256
    )
    return ParsedFutureCandidate(source_classes, classes, digest)


def preflight_future_candidate(
    record: Mapping[str, object],
    *,
    charge_work: WorkCharger,
    reserve_nodes: NodeReserver | None = None,
) -> dict[str, object]:
    """Snapshot input under the FutureCID JSON and resource limits."""
    return snapshot_canonical_json(
        record,
        max_bytes=MAX_CANDIDATE_BYTES,
        max_depth=MAX_CANDIDATE_JSON_DEPTH,
        max_nodes=MAX_CANDIDATE_JSON_NODES,
        charge_work=charge_work,
        reserve_nodes=reserve_nodes,
    )


def future_candidate_sha256(record: Mapping[str, object]) -> str:
    """Hash a record after its caller charged bounded structural parsing."""
    if type(record) not in (dict, MappingProxyType) or any(
        type(key) is not str for key in record
    ):
        raise TypeError("future candidate must be a string-keyed mapping")
    canonical_record = (
        dict(cast(Mapping[str, object], record))
        if type(record) is MappingProxyType
        else record
    )
    return sha256(canonical_json_bytes(canonical_record)).hexdigest()


def charge_work_amount(charge: WorkCharger, amount: int) -> None:
    if not callable(charge):
        raise TypeError("future provider operation requires a work charger")
    if type(amount) is not int or amount <= 0:
        raise ValueError("future provider work charge must be positive")
    charge(amount)


def validate_record(
    record: Mapping[str, object], *, charge_work: WorkCharger
) -> tuple[tuple[int, ...], tuple[FutureClass, ...]]:
    """Validate a candidate's exact fields and decode its ordered class table."""
    if not is_mapping_instance(record) or any(type(key) is not str for key in record):
        raise TypeError("future candidate must be a string-keyed object")
    if frozenset(record) != RECORD_FIELDS:
        raise ValueError("future candidate fields differ from the supported schema")
    if record.get("format") != FUTURE_CANDIDATE_FORMAT:
        raise ValueError("unsupported semantic future candidate version")
    if record.get("authority") != FUTURE_CANDIDATE_AUTHORITY:
        raise ValueError("future candidate producer authority marker is unsupported")
    if record.get("state_universe") != FUTURE_SOURCE_UNIVERSE:
        raise ValueError("future candidate source universe differs from the contract")

    encoded_map = record.get("class_of_state_varint_base64")
    if type(encoded_map) is not str or len(encoded_map) > 4 * (
        (SOURCE_COUNT * 2 + 2) // 3
    ):
        raise ValueError("future source map has an invalid bounded encoding")
    try:
        encoded_bytes = encoded_map.encode("ascii")
        decoded = base64.b64decode(encoded_bytes, validate=True)
    except (UnicodeEncodeError, binascii.Error) as exc:
        raise ValueError("future source map is not valid base64") from exc
    if base64.b64encode(decoded).decode("ascii") != encoded_map:
        raise ValueError("future source map base64 is not canonical")

    raw_controls = record.get("controls")
    raw_children = record.get("ordered_children")
    raw_ranks = record.get("class_rank_candidate")
    if not is_object_list_instance(raw_controls) or not is_object_list_instance(
        raw_children
    ):
        raise TypeError("future controls and ordered children must be arrays")
    if not is_object_list_instance(raw_ranks):
        raise TypeError("future candidate ranks must be an array")
    class_count = len(raw_controls)
    if not 0 < class_count <= SOURCE_COUNT:
        raise ValueError("future class table has an invalid bounded size")
    if len(raw_children) != class_count or len(raw_ranks) != class_count:
        raise ValueError("future class controls, children, and ranks differ in size")
    charge_work_amount(charge_work, SOURCE_COUNT + 3 * class_count)
    class_ids = decode_class_map(
        decoded,
        class_count,
        source_count=SOURCE_COUNT,
        max_varint_bytes=MAX_CID_VARINT_BYTES,
    )
    classes = decode_class_rows(raw_controls, raw_children, raw_ranks, class_count)
    if set(class_ids) != set(range(class_count)):
        raise ValueError("future source map has missing or unused class identifiers")

    return class_ids, classes


__all__ = [
    "canonical_json_bytes",
    "charge_work_amount",
    "decode_class_map",
    "decode_class_rows",
    "FUTURE_CANDIDATE_AUTHORITY",
    "FUTURE_CANDIDATE_FORMAT",
    "FUTURE_SOURCE_UNIVERSE",
    "MAX_CANDIDATE_BYTES",
    "MAX_CANDIDATE_JSON_DEPTH",
    "MAX_CANDIDATE_JSON_NODES",
    "MAX_CID_VARINT_BYTES",
    "ParsedFutureCandidate",
    "parse_future_candidate",
    "parse_future_candidate_file",
    "parse_preflighted_future_candidate",
    "preflight_future_candidate",
    "reject_duplicate_keys",
    "SOURCE_COUNT",
    "validate_record",
]
