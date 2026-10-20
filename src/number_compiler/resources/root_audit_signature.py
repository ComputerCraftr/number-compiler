"""Shallow signatures for live ledger roots."""

from __future__ import annotations

from collections.abc import Iterable, Sized


def root_audit_signature(
    roots: Iterable[object],
) -> tuple[tuple[int, tuple[tuple[str, int, int | None], ...]], ...]:
    """Record direct root fields without walking retained execution DAGs."""
    rows: list[tuple[int, tuple[tuple[str, int, int | None], ...]]] = []
    for root in roots:
        try:
            attributes = dict(vars(root))
        except TypeError:
            attributes = {}
        for cls in type(root).__mro__:
            slots = cls.__dict__.get("__slots__", ())
            if isinstance(slots, str):
                slots = (slots,)
            for name in slots:
                if name in ("__dict__", "__weakref__") or name in attributes:
                    continue
                if name.startswith("__") and not name.endswith("__"):
                    name = "_" + cls.__name__.lstrip("_") + name
                try:
                    attributes[name] = getattr(root, name)
                except AttributeError:
                    continue
        fields: list[tuple[str, int, int | None]] = []
        for name, value in attributes.items():
            try:
                size = len(value) if isinstance(value, Sized) else None
            except (RuntimeError, TypeError, ValueError):
                size = None
            fields.append((name, id(value), size))
        rows.append((id(root), tuple(sorted(fields))))
    return tuple(sorted(rows))


__all__ = ["root_audit_signature"]
