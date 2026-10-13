"""One iterative JSON encoder for already-demanded CLI observation values."""

from __future__ import annotations

from collections.abc import Mapping
from math import isfinite

from number_compiler.api.output_schema import JsonValue


def json_integers(payload: Mapping[str, object]) -> dict[str, JsonValue]:
    """Encode bounded wire values without changing Python's integer limits.

    This serialization boundary never invokes methods on payload objects or
    mutates shared observation packets. Oversized integers retain exact hex.
    """
    result: dict[str, JsonValue] = {}
    pending: list[
        tuple[
            Mapping[str, object] | tuple[object, ...] | list[object],
            dict[str, JsonValue] | list[JsonValue],
        ]
    ] = [(payload, result)]
    while pending:
        source, destination = pending.pop()
        items = source.items() if isinstance(source, Mapping) else enumerate(source)
        for key, value in items:
            encoded: JsonValue
            if type(value) is int and value.bit_length() > 12000:
                encoded = {
                    "encoding": "hex",
                    "value": hex(value),
                    "bits": value.bit_length(),
                }
            elif isinstance(value, Mapping):
                nested: dict[str, JsonValue] = {}
                encoded = nested
                pending.append((value, nested))
            elif isinstance(value, (tuple, list)):
                sequence: list[JsonValue] = []
                encoded = sequence
                pending.append((value, sequence))
            elif isinstance(value, float) and not isfinite(value):
                raise ValueError("JSON measurements must be finite or null")
            elif value is None or isinstance(value, (str, int, float, bool)):
                encoded = value
            else:
                raise TypeError(
                    f"unsupported JSON payload type: {type(value).__name__}"
                )
            if isinstance(destination, dict):
                if not isinstance(key, str):
                    raise TypeError("JSON object keys must be strings")
                destination[key] = encoded
            else:
                destination.append(encoded)
    return result
