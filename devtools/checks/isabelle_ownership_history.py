"""Validate authored relocation history against the live proof inventory."""

from __future__ import annotations

import json
from collections.abc import Mapping
from pathlib import Path
from typing import cast

from devtools.checks.isabelle_source_analysis import IsabelleAnalysis
from devtools.checks.isabelle_syntax import Session, named_type_and_locale_declarations


def _record(value: object) -> dict[str, object]:
    if not isinstance(value, dict) or any(not isinstance(key, str) for key in value):
        raise ValueError("invalid Isabelle ownership history record")
    return cast("dict[str, object]", value)


def _records(value: object) -> list[dict[str, object]]:
    if not isinstance(value, list):
        raise TypeError("invalid Isabelle ownership history collection")
    return [_record(row) for row in value]


def ownership_history(
    root: Path,
    sessions: tuple[Session, ...],
    analyses: Mapping[Path, IsabelleAnalysis],
    texts: Mapping[Path, str],
) -> dict[str, object] | None:
    """Check destinations and declarations; history never supplies proof evidence."""
    path = root / "devtools/checks/isabelle_ownership_history.json"
    if not path.is_file():
        return None
    history = _record(json.loads(path.read_text(encoding="utf-8")))
    if history.get("schema_version") != 1:
        raise ValueError("unsupported Isabelle ownership history schema")
    current = {session.name: session for session in sessions}
    seen: set[str] = set()
    moves = _record(history.get("sessions_by_old_path"))
    for row in [
        *(_record(value) for value in moves.values()),
        *_records(history.get("new_sessions")),
    ]:
        name = row.get("session")
        if not isinstance(name, str) or name not in current or name in seen:
            raise ValueError(f"unknown or duplicate ownership-history session: {name}")
        seen.add(name)
        expected = (Path("proofs/isabelle") / current[name].directory).as_posix()
        if row.get("new_session_path", row.get("session_path")) != expected:
            raise ValueError(f"stale ownership-history session path: {name}")
    for claim in _records(history.get("declaration_extraction_claims")):
        for destination in _records(claim.get("destinations")):
            relative = destination.get("path")
            names = destination.get("declarations")
            if not isinstance(relative, str) or not isinstance(names, list):
                raise TypeError("invalid ownership-history declaration destination")
            target = (root / relative).resolve()
            analysis = analyses.get(target)
            available = (
                {row.name for row in analysis.declarations} if analysis else set()
            )
            available.update(named_type_and_locale_declarations(texts.get(target, "")))
            if not names or any(
                not isinstance(name, str) or name not in available for name in names
            ):
                raise ValueError(f"missing relocated declaration in {relative}")
    return history
