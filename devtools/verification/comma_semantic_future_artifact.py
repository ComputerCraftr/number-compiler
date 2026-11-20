"""Canonical, non-authoritative compact FutureCID artifact bytes."""

from __future__ import annotations

import base64
import binascii
import json
import re
from collections.abc import Iterable, Mapping, Sequence
from hashlib import sha256
from pathlib import Path

from devtools.checks.isabelle_syntax import mask_comments

_V1_FORMAT = "comma-semantic-future-candidate-v1"
MAX_CANDIDATE_HOL_DATA_BYTES = 4 * 1024 * 1024
_V1_RUNTIME_FIELDS = frozenset(
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
_V1_DIAGNOSTIC_FIELDS = frozenset(
    {
        "refinement_rounds",
        "refinement_collision_witnesses",
        "seam_is_projected_from_cid",
        "seam_projection_collision",
    }
)


def decode_unsigned_varints(
    payload: bytes, *, max_values: int, max_value: int
) -> tuple[int, ...]:
    """Decode and canonicalize the compact CID binding stream."""
    if type(payload) is not bytes:
        raise TypeError("candidate CID binding must be bytes")
    if (
        type(max_values) is not int
        or max_values < 0
        or type(max_value) is not int
        or max_value < 0
    ):
        raise ValueError("candidate CID decoder bounds must be nonnegative")
    max_bytes = max(1, (max_value.bit_length() + 6) // 7)
    if len(payload) > max_values * max_bytes:
        raise ValueError("candidate CID payload exceeds its bounded shape")
    values: list[int] = []
    value = 0
    shift = 0
    current_bytes = 0
    for byte in payload:
        current_bytes += 1
        if current_bytes > max_bytes:
            raise ValueError("candidate CID varint exceeds its bounded width")
        value |= (byte & 0x7F) << shift
        if byte & 0x80:
            shift += 7
            continue
        if value > max_value:
            raise ValueError("candidate CID value leaves its declared universe")
        values.append(value)
        if len(values) > max_values:
            raise ValueError("candidate CID payload has too many values")
        value = 0
        shift = 0
        current_bytes = 0
    if current_bytes != 0:
        raise ValueError("truncated candidate CID varint")
    decoded = tuple(values)
    if encode_unsigned_varints(decoded, max_value=max_value) != payload:
        raise ValueError("candidate CID varints are not canonically encoded")
    return decoded


def runtime_candidate_record_from_m204_data(
    source_text: str, graph_text: str
) -> dict[str, object]:
    """Read bounded literal ML proposals, without executing ML or granting authority."""
    from number_compiler.sequences.comma import future_provider_codec

    for text in (source_text, graph_text):
        if len(text.encode("utf-8")) > MAX_CANDIDATE_HOL_DATA_BYTES:
            raise ValueError("M204 proposal exceeds its source size bound")
    numbers = r"\[\s*[0-9]+(?:\s*,\s*[0-9]+)*\s*\]"
    source = re.fullmatch(
        r"\s*structure Comma_Future_M204_Candidate_Data\s*=\s*struct\s+"
        rf"val radices\s*=\s*({numbers})\s+"
        rf"val classes_roots\s*=\s*({numbers})\s+"
        r"fun classes_seeds\s*\(\)\s*=\s*let\s+"
        r"val L\s*=\s*Comma_CRT_MDD_Arena.Seed_Leaf\s+"
        r"val B\s*=\s*Comma_CRT_MDD_Arena.Seed_Branch\s+"
        r"in map L\s*\(0 upto ([0-9]+)\)\s*@\s*\[(.*?)\]\s*end\s*end\s*",
        mask_comments(source_text),
        re.DOTALL,
    )
    graph = re.fullmatch(
        r"\s*structure Comma_Future_M204_Graph_Data\s*=\s*struct\s+"
        r"val rows\s*:\s*\(int \* int list \* int option\) list\s*=\s*"
        r"\[(.*?)\]\s*end\s*",
        mask_comments(graph_text),
        re.DOTALL,
    )
    if source is None or graph is None:
        raise ValueError("M204 proposal is not the supported literal declaration")

    def natural(text: str) -> int:
        return _parse_natural(text, name="M204 proposal")

    def natural_list(text: str) -> list[int]:
        contents = text.strip()[1:-1].strip()
        return [] if not contents else [natural(x.strip()) for x in contents.split(",")]

    def rows(pattern: str, text: str) -> Iterable[re.Match[str]]:
        offset = 0
        expression = re.compile(pattern)
        while text[offset:].strip():
            match = expression.match(text, offset)
            if match is None:
                raise ValueError("M204 proposal contains a computed or malformed row")
            yield match
            offset = match.end()
            if not text[offset:].strip():
                break
            comma = re.match(r"\s*,", text[offset:])
            if comma is None:
                raise ValueError("M204 proposal is missing a row separator")
            offset += comma.end()
            if not text[offset:].strip():
                raise ValueError("M204 proposal has a trailing separator")

    last_leaf = natural(source.group(3))
    if last_leaf >= future_provider_codec.SOURCE_COUNT:
        raise ValueError("M204 proposal has too many class leaves")
    nodes: list[list[object]] = [[cid] for cid in range(last_leaf + 1)]
    for row in rows(rf"\s*B\s*\(([0-9]+),\s*({numbers})\)", source.group(4)):
        nodes.append([natural(row.group(1)), natural_list(row.group(2))])
    controls: list[list[object]] = []
    children: list[list[int | None]] = []
    ranks: list[int | None] = []
    for row in rows(
        r"\s*\((~1|[0-9]+),\s*(\[\s*(?:[0-9]+(?:\s*,\s*[0-9]+)*)?\s*\]),"
        r"\s*(NONE|SOME\s+[0-9]+)\)",
        graph.group(1),
    ):
        control, slots, rank = row.groups()
        successors = natural_list(slots)
        if control == "~1":
            if successors:
                raise ValueError("M204 landmine has child slots")
            controls.append(["landmine", None])
            children.append([None, None])
        else:
            controls.append(["fork", natural(control)])
            children.append(list(successors))
        ranks.append(None if rank == "NONE" else natural(rank.split()[1]))
    record: dict[str, object] = {
        "format": future_provider_codec.FUTURE_CANDIDATE_FORMAT,
        "authority": future_provider_codec.FUTURE_CANDIDATE_AUTHORITY,
        "state_universe": future_provider_codec.FUTURE_SOURCE_UNIVERSE,
        "source_radices": natural_list(source.group(1)),
        "source_roots": natural_list(source.group(2)),
        "source_nodes": nodes,
        "controls": controls,
        "ordered_children": children,
        "class_rank_candidate": ranks,
    }
    future_provider_codec.parse_future_candidate(
        record, charge_work=lambda _amount: None
    )
    return record


def encode_unsigned_varints(values: Iterable[int], *, max_value: int) -> bytes:
    """Encode exact nonnegative integers into canonical unsigned varints."""
    if type(max_value) is not int or max_value < 0:
        raise ValueError("candidate CID varint bound must be nonnegative")
    result = bytearray()
    for value in values:
        if type(value) is not int or not 0 <= value <= max_value:
            raise ValueError("candidate class id leaves its declared universe")
        remaining = value
        while remaining >= 0x80:
            result.append((remaining & 0x7F) | 0x80)
            remaining >>= 7
        result.append(remaining)
    return bytes(result)


def _parse_natural(item: str, *, name: str) -> int:
    if len(item) > 5 or re.fullmatch(r"[0-9]+", item) is None:
        raise ValueError(f"candidate table {name} contains a nonliteral natural")
    value = int(item)
    if str(value) != item:
        raise ValueError(f"candidate table {name} has a noncanonical natural")
    return value


def write_runtime_candidate_from_native_export(
    source_path: Path, output_path: Path
) -> dict[str, object]:
    """Copy a bounded candidate exported by the checked native session.

    The input is the session database export, not authored theory text. This
    function validates and copies its canonical bytes; it does not regenerate
    class data or grant the runtime provider authority.
    """
    from number_compiler.sequences.comma import future_provider_codec

    validate_output_paths(output_path)
    if source_path.resolve() == output_path.resolve():
        raise ValueError("candidate output must be distinct from its native export")
    canonical_payload: bytes | None = None

    def capture_canonical_payload(record: Mapping[str, object]) -> None:
        nonlocal canonical_payload
        canonical_payload = future_provider_codec.canonical_json_bytes(record)

    parsed = future_provider_codec.parse_future_candidate_file(
        source_path,
        charge_work=lambda _amount: None,
        before_parse=capture_canonical_payload,
    )
    if canonical_payload is None:
        raise RuntimeError("native candidate parser did not expose its validated bytes")
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open("xb") as target:
        target.write(canonical_payload)
    return {
        "output": str(output_path),
        "format": future_provider_codec.FUTURE_CANDIDATE_FORMAT,
        "bytes": len(canonical_payload),
        "sha256": parsed.artifact_sha256,
        "authority": future_provider_codec.FUTURE_CANDIDATE_AUTHORITY,
    }


def canonical_candidate_bytes(record: Mapping[str, object]) -> bytes:
    """Serialize the exact newline-terminated JSON bytes consumed at runtime."""
    try:
        text = json.dumps(
            record,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
            allow_nan=False,
        )
    except (TypeError, ValueError) as error:
        raise ValueError("candidate contains non-canonical JSON data") from error
    return (text + "\n").encode("ascii")


def runtime_candidate_record(record: Mapping[str, object]) -> dict[str, object]:
    """Compress an offline source audit into an untrusted CRT MDD candidate."""
    from number_compiler.sequences.comma import future_provider_codec

    if record.get("format") != _V1_FORMAT:
        raise ValueError("runtime candidate conversion requires a v1 candidate")
    if set(record) != set(_V1_RUNTIME_FIELDS | _V1_DIAGNOSTIC_FIELDS):
        raise ValueError("v1 candidate fields differ from the supported schema")
    encoded = record["class_of_state_varint_base64"]
    if (
        not isinstance(encoded, str)
        or len(encoded) > 4 * future_provider_codec.SOURCE_COUNT
    ):
        raise ValueError("candidate CID encoding exceeds its bounded shape")
    try:
        payload = base64.b64decode(encoded, validate=True)
    except (binascii.Error, ValueError) as error:
        raise ValueError("candidate CID encoding is malformed") from error
    if base64.b64encode(payload).decode("ascii") != encoded:
        raise ValueError("candidate CID encoding is noncanonical")
    ids = decode_unsigned_varints(
        payload,
        max_values=future_provider_codec.SOURCE_COUNT,
        max_value=future_provider_codec.SOURCE_COUNT - 1,
    )
    result = {
        **{
            field: record[field]
            for field in _V1_RUNTIME_FIELDS
            if field not in {"format", "class_of_state_varint_base64"}
        },
        "format": future_provider_codec.FUTURE_CANDIDATE_FORMAT,
        **source_mdd_fields(ids),
    }
    future_provider_codec.parse_future_candidate(
        result, charge_work=lambda _amount: None
    )
    return result


_PhaseGroup = tuple[int, tuple[int, ...]]


def source_mdd_fields(source_classes: Sequence[int]) -> dict[str, object]:
    """Compress an independent full source audit; never used during production lookup."""
    from number_compiler.sequences.comma.future_provider_codec import SOURCE_COUNT

    if len(source_classes) != SOURCE_COUNT or any(
        type(cid) is not int or not 0 <= cid < SOURCE_COUNT for cid in source_classes
    ):
        raise ValueError("candidate map does not cover its bounded source universe")
    radices = (3, 4, 7, 11)
    nodes: list[list[object]] = []
    interned: dict[tuple[int, ...], int] = {}

    def intern(key: tuple[int, ...]) -> int:
        previous = interned.get(key)
        if previous is not None:
            return previous
        index = len(nodes)
        interned[key] = index
        nodes.append([key[0]] if len(key) == 1 else [key[0], list(key[1:])])
        return index

    roots: list[int] = []
    for slot in range(16):
        offset = slot * 924
        completed: dict[_PhaseGroup, int] = {}
        initial = (0, tuple(range(924)))
        pending: list[tuple[_PhaseGroup, tuple[_PhaseGroup, ...] | None]] = [
            (initial, None)
        ]
        while pending:
            key, child_keys = pending.pop()
            axis, phases = key
            if child_keys is not None:
                children = tuple(completed[child] for child in child_keys)
                completed[key] = (
                    children[0]
                    if all(child == children[0] for child in children)
                    else intern((axis, *children))
                )
                continue
            first = source_classes[offset + phases[0]]
            if all(source_classes[offset + phase] == first for phase in phases):
                completed[key] = intern((first,))
                continue
            if axis == len(radices):
                raise ValueError("candidate phase characters do not determine a class")
            child_keys = tuple(
                (axis + 1, tuple(p for p in phases if p % radices[axis] == r))
                for r in range(radices[axis])
            )
            pending.append((key, child_keys))
            pending.extend((child, None) for child in reversed(child_keys))
        roots.append(completed[initial])
    return {
        "source_radices": list(radices),
        "source_roots": roots,
        "source_nodes": nodes,
    }


def runtime_candidate_bytes(record: Mapping[str, object]) -> bytes:
    """Return v3 candidate bytes without elevating their untrusted authority."""
    return canonical_candidate_bytes(runtime_candidate_record(record))


def runtime_candidate_sha256(record: Mapping[str, object]) -> str:
    """Hash the exact canonical bytes used by the runtime digest contract."""
    return canonical_candidate_sha256(runtime_candidate_record(record))


def canonical_candidate_sha256(record: Mapping[str, object]) -> str:
    """Hash a canonical candidate record already in its requested version."""
    return sha256(canonical_candidate_bytes(record)).hexdigest()


def validate_output_paths(*paths: Path | None) -> None:
    """Require optional candidate outputs to be distinct and not pre-existing."""
    resolved = [path.resolve() for path in paths if path is not None]
    if len(set(resolved)) != len(resolved):
        raise ValueError("candidate outputs must use distinct paths")
    if any(path.exists() for path in resolved):
        raise FileExistsError("candidate outputs must be new files")
