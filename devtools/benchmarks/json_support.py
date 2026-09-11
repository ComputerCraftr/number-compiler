"""Shared JSON normalization for executable benchmark probes."""

from __future__ import annotations

import json
from dataclasses import asdict, is_dataclass


def jsonable(value: object) -> object:
    """Normalize dataclasses/tuples/maps through the stdlib JSON encoder.

    Keeping one owner for this benchmark-only boundary avoids duplicated
    recursive walkers in individual probes.
    """

    def default(item: object) -> dict[str, object]:
        if is_dataclass(item) and not isinstance(item, type):
            return asdict(item)
        raise TypeError(f"unsupported JSON value: {type(item)!r}")

    return json.loads(json.dumps(value, default=default))


__all__ = ["jsonable"]
