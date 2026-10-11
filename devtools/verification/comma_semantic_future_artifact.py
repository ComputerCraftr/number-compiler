"""Canonical, non-authoritative FutureCID artifact bytes."""

from __future__ import annotations

import json
from collections.abc import Mapping
from hashlib import sha256
from pathlib import Path
from types import MappingProxyType

from devtools.checks.isabelle_source_analysis import extract_isabelle_declarations
from devtools.checks.isabelle_syntax import parse_theory_header

_V1_FORMAT = "comma-semantic-future-candidate-v1"
_V2_FORMAT = "comma-semantic-future-candidate-v2"
CANDIDATE_TABLE_NAMES = (
    "comma_semantic_future_candidate_class_ids",
    "comma_semantic_future_candidate_controls",
    "comma_semantic_future_candidate_children",
    "comma_semantic_future_candidate_ranks",
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
    result = dict(record)
    result["format"] = _V2_FORMAT
    return result


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
