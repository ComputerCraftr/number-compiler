"""Resolve public facade names without importing unrelated family runtimes."""

from collections.abc import Mapping, MutableMapping
from importlib import import_module


def resolve_export(
    name: str, modules: Mapping[str, str], namespace: MutableMapping[str, object]
) -> object:
    module = modules.get(name)
    if module is None:
        raise AttributeError(
            f"module {namespace['__name__']!r} has no attribute {name!r}"
        )
    value: object = getattr(import_module(module), name)
    namespace[name] = value
    return value
