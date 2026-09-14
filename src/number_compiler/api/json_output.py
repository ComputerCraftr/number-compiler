"""Bounded JSON integer encoding shared by CLI and family observers."""

from typing import Any


def json_integers(payload: dict[str, Any]) -> dict[str, Any]:
    """Render very large integers in hex without changing Python's global limits."""
    pending: list[Any] = [payload]
    while pending:
        container = pending.pop()
        keys = list(container) if isinstance(container, dict) else range(len(container))
        for key in keys:
            value = container[key]
            if type(value) is int and value.bit_length() > 12000:
                container[key] = {"encoding": "hex", "value": hex(value), "bits": value.bit_length()}
            elif isinstance(value, tuple):
                container[key] = list(value)
                pending.append(container[key])
            elif isinstance(value, (dict, list)):
                pending.append(value)
    return payload
