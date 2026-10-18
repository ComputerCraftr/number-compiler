"""Canonical, non-authoritative FutureCID artifact bytes."""

from __future__ import annotations

import base64
import json
import re
from collections.abc import Iterable, Mapping
from hashlib import sha256
from pathlib import Path
from types import MappingProxyType

from devtools.checks.isabelle_source_analysis import extract_isabelle_declarations
from devtools.checks.isabelle_syntax import parse_theory_header

_V1_FORMAT = "comma-semantic-future-candidate-v1"
_V2_FORMAT = "comma-semantic-future-candidate-v2"
MAX_CANDIDATE_HOL_DATA_BYTES = 4 * 1024 * 1024
CANDIDATE_TABLE_NAMES = (
    "comma_semantic_future_candidate_class_ids",
    "comma_semantic_future_candidate_controls",
    "comma_semantic_future_candidate_children",
    "comma_semantic_future_candidate_ranks",
)
_CANDIDATE_TABLE_TYPES = {
    CANDIDATE_TABLE_NAMES[0]: "nat list",
    CANDIDATE_TABLE_NAMES[1]: "comma_future_control list",
    CANDIDATE_TABLE_NAMES[2]: "(nat option \\<times> nat option) list",
    CANDIDATE_TABLE_NAMES[3]: "nat option list",
}
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


def candidate_table_definitions(text: str, path: Path) -> Mapping[str, tuple[str, str]]:
    """Extract only the four canonical CID data definitions from a theory."""
    selected = tuple(
        item
        for item in extract_isabelle_declarations(text, path)
        if item.name in CANDIDATE_TABLE_NAMES
    )
    declarations = {item.name: item for item in selected}
    if len(selected) != len(CANDIDATE_TABLE_NAMES) or set(declarations) != set(
        CANDIDATE_TABLE_NAMES
    ):
        raise ValueError("candidate data theory lacks a unique canonical table set")
    return MappingProxyType(
        {
            name: (declarations[name].command, declarations[name].body.strip())
            for name in CANDIDATE_TABLE_NAMES
        }
    )


def _literal_list(body: str, name: str, *, max_entries: int) -> tuple[str, ...]:
    """Read a list whose definition is a closed literal, rejecting HOL code."""
    hol_type = _CANDIDATE_TABLE_TYPES[name]
    declaration = re.fullmatch(
        rf'\s*{re.escape(name)}\s*::\s*"{re.escape(hol_type)}"\s+where\s+'
        rf'"{re.escape(name)}\s*=\s*\[(.*)\]"\s*',
        body,
        re.DOTALL,
    )
    if declaration is None:
        raise ValueError(f"candidate table {name} is not a canonical literal list")
    contents = declaration.group(1)
    if not contents.strip():
        return ()
    entries: list[str] = []
    depth = 0
    start = 0
    for index, char in enumerate(contents):
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
            if depth < 0:
                raise ValueError(f"candidate table {name} has unbalanced grouping")
        elif char == "," and depth == 0:
            if len(entries) >= max_entries:
                raise ValueError(f"candidate table {name} exceeds its bounded length")
            entry = contents[start:index].strip()
            if not entry:
                raise ValueError(f"candidate table {name} has an empty list item")
            entries.append(entry)
            start = index + 1
    if depth != 0:
        raise ValueError(f"candidate table {name} has unbalanced grouping")
    final = contents[start:].strip()
    if not final:
        raise ValueError(f"candidate table {name} has a trailing comma")
    if len(entries) >= max_entries:
        raise ValueError(f"candidate table {name} exceeds its bounded length")
    entries.append(final)
    return tuple(entries)


def runtime_candidate_record_from_isabelle_data(
    text: str, path: Path
) -> dict[str, object]:
    """Project only the four checked-in HOL data tables into untrusted v2 JSON.

    This parses authored literals only. It does not rebuild the boundary graph,
    infer diagnostics, or confer kernel/runtime authority.
    """
    from number_compiler.sequences.comma import future_provider

    if (
        type(text) is not str
        or len(text.encode("utf-8")) > MAX_CANDIDATE_HOL_DATA_BYTES
    ):
        raise ValueError("candidate data theory exceeds its bounded source size")
    declarations = candidate_table_definitions(text, path)
    if parse_theory_header(text, path)[0] != "Comma_Semantic_Future_Candidate_Data":
        raise ValueError("candidate source has the wrong Isabelle theory name")
    if any(command != "definition" for command, _body in declarations.values()):
        raise ValueError("candidate data tables must be literal definitions")
    source_count = future_provider.SOURCE_COUNT

    ids = tuple(
        _parse_natural(item, name=CANDIDATE_TABLE_NAMES[0])
        for item in _literal_list(
            declarations[CANDIDATE_TABLE_NAMES[0]][1],
            CANDIDATE_TABLE_NAMES[0],
            max_entries=source_count,
        )
    )
    controls: list[list[object]] = []
    for item in _literal_list(
        declarations[CANDIDATE_TABLE_NAMES[1]][1],
        CANDIDATE_TABLE_NAMES[1],
        max_entries=source_count,
    ):
        if item == "Comma_Future_Landmine":
            controls.append(["landmine", None])
            continue
        match = re.fullmatch(r"Comma_Future_Fork\s+([0-9]+)", item)
        if match is None:
            raise ValueError("candidate control table contains nonliteral syntax")
        controls.append(["fork", _parse_natural(match.group(1), name="control")])

    children: list[list[int | None]] = []
    child_pattern = re.compile(
        r"\(\s*(None|Some\s+[0-9]+)\s*,\s*(None|Some\s+[0-9]+)\s*\)"
    )
    for item in _literal_list(
        declarations[CANDIDATE_TABLE_NAMES[2]][1],
        CANDIDATE_TABLE_NAMES[2],
        max_entries=source_count,
    ):
        match = child_pattern.fullmatch(item)
        if match is None:
            raise ValueError("candidate child table contains nonliteral syntax")
        children.append([_parse_option_nat(value, "child") for value in match.groups()])

    ranks = [
        _parse_option_nat(item, "rank")
        for item in _literal_list(
            declarations[CANDIDATE_TABLE_NAMES[3]][1],
            CANDIDATE_TABLE_NAMES[3],
            max_entries=source_count,
        )
    ]
    if len(ids) != source_count:
        raise ValueError("candidate source map does not cover its declared universe")
    class_count = len(controls)
    if class_count == 0 or len(children) != class_count or len(ranks) != class_count:
        raise ValueError("candidate class tables have inconsistent dimensions")
    if any(cid >= class_count for cid in ids) or set(ids) != set(range(class_count)):
        raise ValueError("candidate source map has invalid or unused class IDs")

    encoded_ids = encode_unsigned_varints(ids, max_value=class_count - 1)
    record: dict[str, object] = {
        "format": future_provider.FUTURE_CANDIDATE_FORMAT,
        "authority": future_provider.FUTURE_CANDIDATE_AUTHORITY,
        "state_universe": future_provider.FUTURE_SOURCE_UNIVERSE,
        "class_of_state_varint_base64": base64.b64encode(encoded_ids).decode("ascii"),
        "controls": controls,
        "ordered_children": children,
        "class_rank_candidate": ranks,
    }
    future_provider.parse_future_candidate(record, charge_work=lambda _amount: None)
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


def _parse_option_nat(item: str, field: str) -> int | None:
    if item == "None":
        return None
    match = re.fullmatch(r"Some\s+([0-9]+)", item)
    if match is None:
        raise ValueError(f"candidate {field} table contains nonliteral syntax")
    return _parse_natural(match.group(1), name=field)


def write_runtime_candidate_from_isabelle_data(
    source_path: Path, output_path: Path
) -> dict[str, object]:
    """Write canonical untrusted runtime bytes without replacing existing files."""
    validate_output_paths(output_path)
    if source_path.resolve() == output_path.resolve():
        raise ValueError("candidate output must be distinct from its Isabelle source")
    with source_path.open("rb") as source:
        raw_data = source.read(MAX_CANDIDATE_HOL_DATA_BYTES + 1)
    if len(raw_data) > MAX_CANDIDATE_HOL_DATA_BYTES:
        raise ValueError("candidate data theory exceeds its bounded source size")
    record = runtime_candidate_record_from_isabelle_data(
        raw_data.decode("utf-8"), source_path
    )
    payload = canonical_candidate_bytes(record)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with output_path.open("xb") as target:
        target.write(payload)
    return {
        "output": str(output_path),
        "format": record["format"],
        "bytes": len(payload),
        "sha256": sha256(payload).hexdigest(),
        "authority": record["authority"],
    }


def assert_candidate_data_theory_matches(
    checked_text: str,
    checked_path: Path,
    generated_text: str,
    generated_path: Path,
) -> None:
    """Require the authored theory header and canonical table declarations."""
    if parse_theory_header(checked_text, checked_path) != parse_theory_header(
        generated_text, generated_path
    ):
        raise ValueError("candidate data theory header differs")
    if candidate_table_definitions(
        checked_text, checked_path
    ) != candidate_table_definitions(generated_text, generated_path):
        raise ValueError("candidate table definitions differ")


def _runtime_candidate_sha256_after_hol_match(
    record: Mapping[str, object],
    generated_text: str,
    checked_path: Path,
) -> str:
    """Hash canonical v2 bytes only after their generated HOL tables match.

    This development-time consistency check grants no kernel or runtime
    admission. The caller must validate and render the bounded v2 record first.
    """
    if record.get("format") != _V2_FORMAT:
        raise ValueError("HOL data binding requires a v2 runtime candidate")
    if not isinstance(checked_path, Path):
        raise TypeError("checked candidate data path must be a pathlib Path")
    checked_text = checked_path.read_text(encoding="utf-8")
    generated_path = checked_path
    assert_candidate_data_theory_matches(
        checked_text, checked_path, generated_text, generated_path
    )
    return sha256(canonical_candidate_bytes(record)).hexdigest()


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
    """Version an existing candidate record for the bounded runtime consumer."""
    if record.get("format") != _V1_FORMAT:
        raise ValueError("runtime candidate conversion requires a v1 candidate")
    if set(record) != _V1_RUNTIME_FIELDS | _V1_DIAGNOSTIC_FIELDS:
        raise ValueError("v1 candidate fields differ from the supported schema")
    return {
        **{field: record[field] for field in _V1_RUNTIME_FIELDS if field != "format"},
        "format": _V2_FORMAT,
    }


def runtime_candidate_bytes(record: Mapping[str, object]) -> bytes:
    """Return v2 candidate bytes without elevating their untrusted authority."""
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
