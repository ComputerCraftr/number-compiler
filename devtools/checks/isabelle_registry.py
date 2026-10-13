"""Discover Isabelle registrations through ROOTS without inventing dependencies."""

from collections.abc import Sequence
from dataclasses import replace
from pathlib import Path

from devtools.checks.isabelle_syntax import Session, parse_sessions, validate_sessions
from devtools.checks.source_discovery import authored_files


def root_files(
    root: Path, *, authored_sources: Sequence[Path] | None = None
) -> tuple[Path, ...]:
    """Read the registered directory graph; reject escapes and hidden ROOT files."""
    root = root.resolve()
    pending = [root]
    visited: set[Path] = set()
    files: list[Path] = []
    while pending:
        directory = pending.pop()
        if not directory.is_relative_to(root):
            raise ValueError(f"ROOTS directory escapes theory root: {directory}")
        if directory in visited:
            raise ValueError(f"repeated ROOTS directory: {directory}")
        visited.add(directory)
        registration = directory / "ROOT"
        roots = directory / "ROOTS"
        if not registration.is_file() and not roots.is_file():
            raise ValueError(f"missing ROOT or ROOTS in {directory}")
        if registration.is_file():
            if not registration.resolve().is_relative_to(root):
                raise ValueError(f"ROOT file escapes theory root: {registration}")
            files.append(registration)
        if roots.is_file():
            if not roots.resolve().is_relative_to(root):
                raise ValueError(f"ROOTS file escapes theory root: {roots}")
            children: list[Path] = []
            for line in roots.read_text(encoding="utf-8").splitlines():
                entry = line.strip()
                if not entry or entry.startswith("#"):
                    continue
                if entry.startswith('"') and entry.endswith('"'):
                    entry = entry[1:-1]
                if not entry or '"' in entry or "\\" in entry:
                    raise ValueError(f"unsupported ROOTS entry: {line}")
                path = Path(entry)
                if path.is_absolute() or ".." in path.parts:
                    raise ValueError(f"ROOTS directory escapes theory root: {entry}")
                children.append((directory / path).resolve())
            pending.extend(reversed(children))
    source_paths = (
        authored_files(root) if authored_sources is None else authored_sources
    )
    hidden = {
        path.resolve()
        for path in source_paths
        if path.name == "ROOT" and path.resolve().is_relative_to(root)
    } - {path.resolve() for path in files}
    if hidden:
        raise ValueError(f"unregistered ROOT files: {sorted(hidden)}")
    return tuple(files)


def discover_sessions(
    root: Path, *, authored_sources: Sequence[Path] | None = None
) -> tuple[Session, ...]:
    """Return every session with its directory relative to the common proof root."""
    root = root.resolve()
    sessions: list[Session] = []
    for registration in root_files(root, authored_sources=authored_sources):
        for session in parse_sessions(registration.read_text(encoding="utf-8")):
            directory = (registration.parent / session.directory).resolve()
            if not directory.is_relative_to(root):
                raise ValueError(
                    f"{session.name}: session directory escapes theory root"
                )
            sessions.append(replace(session, directory=directory.relative_to(root)))
    result = tuple(sessions)
    if len({session.directory for session in result}) != len(result):
        raise ValueError("duplicate canonical Isabelle session directory")
    validate_sessions(result)
    return result
