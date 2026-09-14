"""Resolve public facade names without importing unrelated family runtimes."""

from importlib import import_module
from typing import Any


def resolve_export(
    name: str, modules: dict[str, str], namespace: dict[str, Any]
) -> Any:
    module = modules.get(name)
    if module is None:
        raise AttributeError(
            f"module {namespace['__name__']!r} has no attribute {name!r}"
        )
    value = getattr(import_module(module), name)
    namespace[name] = value
    return value
