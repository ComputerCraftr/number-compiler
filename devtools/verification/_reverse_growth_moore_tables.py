"""Typed loader for the bounded reverse-growth table fixture."""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import cast

_ARCHIVE = Path(__file__).with_name("data") / "reverse_growth_g161.json"
_MAX_ARCHIVE_BYTES = 1_000_000


@dataclass(frozen=True, slots=True)
class _GrowthTables:
    absent: int
    exit: int
    spatial_q11_classes: int
    temporal_t191_classes: int
    temporal_output_ids: tuple[int, ...]
    temporal_transitions: tuple[tuple[int, ...], ...]
    d5_macro_pairs: tuple[tuple[int, int], ...]
    d5_field_to_macro: tuple[int, ...]


def _unique_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate reverse-growth archive field: {key}")
        result[key] = value
    return result


def _exact_int(value: object, name: str) -> int:
    if type(value) is not int:
        raise ValueError(f"reverse-growth archive field {name} is not an exact integer")
    return value


def _object_list(value: object, name: str) -> list[object]:
    if type(value) is not list:
        raise ValueError(f"reverse-growth archive field {name} is not an array")
    return cast(list[object], value)


def _int_vector(value: object, name: str, size: int) -> tuple[int, ...]:
    items = _object_list(value, name)
    if len(items) != size:
        raise ValueError(f"reverse-growth archive field {name} has the wrong shape")
    return tuple(
        _exact_int(item, f"{name}[{index}]") for index, item in enumerate(items)
    )


def _int_matrix(
    value: object, name: str, rows: int, columns: int
) -> tuple[tuple[int, ...], ...]:
    items = _object_list(value, name)
    if len(items) != rows:
        raise ValueError(f"reverse-growth archive field {name} has the wrong row count")
    return tuple(
        _int_vector(row, f"{name}[{index}]", columns) for index, row in enumerate(items)
    )


def _int_pairs(value: object, name: str, size: int) -> tuple[tuple[int, int], ...]:
    items = _object_list(value, name)
    if len(items) != size:
        raise ValueError(f"reverse-growth archive field {name} has the wrong shape")
    pairs: list[tuple[int, int]] = []
    for index, raw_row in enumerate(items):
        row = _object_list(raw_row, f"{name}[{index}]")
        if len(row) != 2:
            raise ValueError(
                f"reverse-growth archive field {name}[{index}] is not a pair"
            )
        pairs.append(
            (
                _exact_int(row[0], f"{name}[{index}][0]"),
                _exact_int(row[1], f"{name}[{index}][1]"),
            )
        )
    return tuple(pairs)


def load_growth_tables(path: Path = _ARCHIVE) -> _GrowthTables:
    """Load and validate the immutable finite table fixture."""
    try:
        with path.open("rb") as stream:
            raw = stream.read(_MAX_ARCHIVE_BYTES + 1)
        if len(raw) > _MAX_ARCHIVE_BYTES:
            raise ValueError("reverse-growth archive exceeds its byte budget")
        payload: object = json.loads(
            raw.decode("utf-8"), object_pairs_hook=_unique_object
        )
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError("reverse-growth archive is malformed") from exc
    expected_fields = {
        "format",
        "ABSENT",
        "EXIT",
        "SPATIAL_Q11_CLASSES",
        "TEMPORAL_T191_CLASSES",
        "TEMPORAL_OUTPUT_IDS",
        "TEMPORAL_TRANSITIONS",
        "D5_MACRO_PAIRS",
        "D5_FIELD_TO_MACRO",
    }
    if type(payload) is not dict:
        raise ValueError("reverse-growth archive has an invalid field set")
    payload = cast(dict[str, object], payload)
    if set(payload) != expected_fields:
        raise ValueError("reverse-growth archive has an invalid field set")
    if payload["format"] != "reverse-growth-g161-t191-v1":
        raise ValueError("reverse-growth archive has another format")

    absent = _exact_int(payload["ABSENT"], "ABSENT")
    exit_code = _exact_int(payload["EXIT"], "EXIT")
    spatial = _exact_int(payload["SPATIAL_Q11_CLASSES"], "SPATIAL_Q11_CLASSES")
    temporal = _exact_int(payload["TEMPORAL_T191_CLASSES"], "TEMPORAL_T191_CLASSES")
    if absent >= 0 or exit_code >= 0 or absent == exit_code:
        raise ValueError("reverse-growth archive terminal codes are invalid")
    if spatial != 11 or temporal != 191:
        raise ValueError("reverse-growth archive declares another state domain")
    outputs = _int_vector(
        payload["TEMPORAL_OUTPUT_IDS"], "TEMPORAL_OUTPUT_IDS", temporal
    )
    if any(not 0 <= value < 20 for value in outputs):
        raise ValueError("reverse-growth archive has an invalid output label")
    transitions = _int_matrix(
        payload["TEMPORAL_TRANSITIONS"],
        "TEMPORAL_TRANSITIONS",
        temporal,
        spatial,
    )
    if any(
        code not in (absent, exit_code) and not 0 <= code < spatial * temporal
        for row in transitions
        for code in row
    ):
        raise ValueError("reverse-growth archive has an invalid transition target")
    macro_pairs = _int_pairs(payload["D5_MACRO_PAIRS"], "D5_MACRO_PAIRS", 930)
    if any(
        not 0 <= spatial_id < spatial or not 0 <= temporal_id < temporal
        for spatial_id, temporal_id in macro_pairs
    ):
        raise ValueError("reverse-growth archive has an invalid D5 macro pair")
    field_to_macro = _int_vector(
        payload["D5_FIELD_TO_MACRO"], "D5_FIELD_TO_MACRO", 3610
    )
    if any(not 0 <= macro_id < len(macro_pairs) for macro_id in field_to_macro):
        raise ValueError("reverse-growth archive has an invalid macro index")
    return _GrowthTables(
        absent,
        exit_code,
        spatial,
        temporal,
        outputs,
        transitions,
        macro_pairs,
        field_to_macro,
    )


_TABLES = load_growth_tables()
ABSENT = _TABLES.absent
EXIT = _TABLES.exit
SPATIAL_Q11_CLASSES = _TABLES.spatial_q11_classes
TEMPORAL_T191_CLASSES = _TABLES.temporal_t191_classes
TEMPORAL_OUTPUT_IDS = _TABLES.temporal_output_ids
TEMPORAL_TRANSITIONS = _TABLES.temporal_transitions
D5_MACRO_PAIRS = _TABLES.d5_macro_pairs
D5_FIELD_TO_MACRO = _TABLES.d5_field_to_macro
